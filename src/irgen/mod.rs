//! # Homework: IR Generation
//!
//! The goal of this homework is to translate the components of a C file into KECC IR. While doing
//! so, you will familarize yourself with the structure of KECC IR, and understand the semantics of
//! C in terms of KECC.
//!
//! We highly recommend checking out the [slides][slides] and [github repo][github-qna-irgen] for
//! useful information.
//!
//! ## Guide
//!
//! ### High Level Guide
//!
//! Please watch the following video from 2020 along the lecture slides.
//! - [Intermediate Representation][ir]
//! - [IRgen (Overview)][irgen-overview]
//!
//! ### Coding Guide
//!
//! We highly recommend you copy-and-paste the code given in the following lecture videos from 2020:
//! - [IRgen (Code, Variable Declaration)][irgen-var-decl]
//! - [IRgen (Code, Function Definition)][irgen-func-def]
//! - [IRgen (Code, Statement 1)][irgen-stmt-1]
//! - [IRgen (Code, Statement 2)][irgen-stmt-2]
//!
//! The skeleton code roughly consists of the code for the first two videos, but you should still
//! watch them to have an idea of what the code is like.
//!
//! [slides]: https://docs.google.com/presentation/d/1SqtU-Cn60Sd1jkbO0OSsRYKPMIkul0eZoYG9KpMugFE/edit?usp=sharing
//! [ir]: https://youtu.be/7CY_lX5ZroI
//! [irgen-overview]: https://youtu.be/YPtnXlKDSYo
//! [irgen-var-decl]: https://youtu.be/HjARCUoK08s
//! [irgen-func-def]: https://youtu.be/Rszt9x0Xu_0
//! [irgen-stmt-1]: https://youtu.be/jFahkyxm994
//! [irgen-stmt-2]: https://youtu.be/UkaXaNw462U
//! [github-qna-irgen]: https://github.com/kaist-cp/cs420/labels/homework%20-%20irgen
use core::cmp::Ordering;
use core::convert::TryFrom;
use core::{fmt, mem, panic};
use std::collections::{BTreeMap, HashMap};
use std::ops::Deref;

use itertools::izip;
use lang_c::ast::*;
use lang_c::driver::Parse;
use lang_c::span::Node;
use thiserror::Error;

use crate::ir::{DtypeError, HasDtype, JumpArg, Named};
use crate::write_base::WriteString;
use crate::*;

#[derive(Debug)]
pub struct IrgenError {
    pub code: String,
    pub message: IrgenErrorMessage,
}

impl IrgenError {
    pub fn new(code: String, message: IrgenErrorMessage) -> Self {
        Self { code, message }
    }
}

impl fmt::Display for IrgenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}\r\n\r\ncode: {}", self.message, self.code)
    }
}

/// Error format when a compiler error happens.
///
/// Feel free to add more kinds of errors.
#[derive(Debug, PartialEq, Eq, Error)]
pub enum IrgenErrorMessage {
    /// For uncommon error
    #[error("{message}")]
    Misc { message: String },
    #[error("called object `{callee:?}` is not a function or function pointer")]
    NeedFunctionOrFunctionPointer { callee: ir::Operand },
    #[error("redefinition, `{name}`")]
    Redefinition { name: String },
    #[error("`{dtype}` conflicts prototype's dtype, `{protorype_dtype}`")]
    ConflictingDtype {
        dtype: ir::Dtype,
        protorype_dtype: ir::Dtype,
    },
    #[error("{dtype_error}")]
    InvalidDtype { dtype_error: DtypeError },
    #[error("l-value required as {message}")]
    RequireLvalue { message: String },
}

/// A C file going through IR generation.
#[derive(Default, Debug)]
pub struct Irgen {
    /// Declarations made in the C file (e.g, global variables and functions)
    decls: BTreeMap<String, ir::Declaration>,
    /// Type definitions made in the C file (e.g, typedef my_type = int;)
    typedefs: HashMap<String, ir::Dtype>,
    /// Structs defined in the C file,
    // TODO: explain how to use this.
    structs: HashMap<String, Option<ir::Dtype>>,
    /// Temporary counter for anonymous structs. One should not need to use this any more.
    struct_tempid_counter: usize,
}

impl Translate<Parse> for Irgen {
    type Target = ir::TranslationUnit;
    type Error = IrgenError;

    fn translate(&mut self, source: &Parse) -> Result<Self::Target, Self::Error> {
        self.translate(&source.unit)
    }
}

impl Translate<TranslationUnit> for Irgen {
    type Target = ir::TranslationUnit;
    type Error = IrgenError;

    fn translate(&mut self, source: &TranslationUnit) -> Result<Self::Target, Self::Error> {
        for ext_decl in &source.0 {
            match &ext_decl.node {
                ExternalDeclaration::Declaration(var) => {
                    self.add_declaration(&var.node)?;
                }
                ExternalDeclaration::StaticAssert(_) => {
                    panic!("ExternalDeclaration::StaticAssert is unsupported")
                }
                ExternalDeclaration::FunctionDefinition(func) => {
                    self.add_function_definition(&func.node)?;
                }
            }
        }

        let decls = mem::take(&mut self.decls);
        let structs = mem::take(&mut self.structs);
        Ok(Self::Target { decls, structs })
    }
}

impl Irgen {
    const BID_INIT: ir::BlockId = ir::BlockId(0);
    // `0` is used to create `BID_INIT`
    const BID_COUNTER_INIT: usize = 1;
    const TEMPID_COUNTER_INIT: usize = 0;

    /// Add a declaration. It can be either a struct, typedef, or a variable.
    fn add_declaration(&mut self, source: &Declaration) -> Result<(), IrgenError> {
        // assume for example we have some typedefs before: typedef int tt
        // 解析DeclarationSpecifiers
        let (base_dtype, is_typedef) =
            ir::Dtype::try_from_ast_declaration_specifiers(&source.specifiers).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;
        // 将specifier的Dtype(可能变体为Struct/Int/Float/Unit/Typedef),解析成不包含Typedef变体的Dtype(例如Struct中的fields不包含Typedef变体的Dtype)
        let base_dtype = base_dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
            IrgenError::new(
                format!("{source:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        // 如果typespecifier对应一个struct，先把结构体名字则添加到struct表中的,然后如果是struct的一个定义，则进行struct_resolve,返回一个无定义的struct Dtype(fields=None)
        let base_dtype = if let ir::Dtype::Struct { name, fields, .. } = &base_dtype {
            if let Some(name) = name {
                let _ = self.structs.entry(name.to_string()).or_insert(None);
            }

            if fields.is_some() {
                base_dtype
                    .resolve_structs(&mut self.structs, &mut self.struct_tempid_counter)
                    .map_err(|e| {
                        IrgenError::new(
                            format!("{source:#?}"),
                            IrgenErrorMessage::InvalidDtype { dtype_error: e },
                        )
                    })?
            } else {
                base_dtype
            }
        } else {
            base_dtype
        };
        // tt *a, b
        for init_decl in &source.declarators {
            let declarator = &init_decl.node.declarator.node;
            let name = name_of_declarator(declarator); // a 和 b(2次循环中)

            let dtype = base_dtype
                .clone()
                .with_ast_declarator(declarator)
                .map_err(|e| {
                    IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::InvalidDtype { dtype_error: e },
                    )
                })?
                .deref()
                .clone();
            let dtype = dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
                // 这里需要resolve_typedefs是因为Dtype的嵌套构造(Pointer,Array,Func)的Func构造中的params可能出现Dtype::Typedef,需要去除别名(同时检验别名是否均已定义)
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;
            // 此时dtype就是该Declaration中的一个声明子Declarator的完整类型，如int *(*f(struct A, int *))[3]去除了类型别名，进行了自定义类(struct)一致性检查
            if !is_typedef && is_invalid_structure(&dtype, &self.structs) {
                // 为了定义具体变量(匿名或非匿名)，要求结构体类必须完整
                // 例如：struct A;      // 声明，此时 A 是不完整类型，self.structs中没有A的定义，但有A的key
                // struct A var;  错误！编译器不知道 A 多大，is_invalid_structure 返回 true
                return Err(IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::Misc {
                        message: "incomplete struct type".to_string(),
                    },
                ));
            }

            if is_typedef {
                // Add new typedef if nothing has been declared before
                let prev_dtype = self
                    .typedefs
                    .entry(name.clone())
                    .or_insert_with(|| dtype.clone());

                if prev_dtype != &dtype {
                    return Err(IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::ConflictingDtype {
                            dtype,
                            protorype_dtype: prev_dtype.clone(),
                        },
                    ));
                }

                continue;
            }

            // Creates a new declaration based on the dtype. 为每个declarator创建一个ir::Declaration，e.g. int a[3], *b; 要创建2个ir::Declaration
            let mut decl = ir::Declaration::try_from(dtype.clone()).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;

            // If `initializer` exists, convert initializer to a constant value
            if let Some(initializer) = init_decl.node.initializer.as_ref() {
                if !is_valid_initializer(&initializer.node, &dtype, &self.structs) {
                    return Err(IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::Misc {
                            message: "initializer is not valid".to_string(),
                        },
                    ));
                }

                match &mut decl {
                    ir::Declaration::Variable {
                        initializer: var_initializer,
                        ..
                    } => {
                        if var_initializer.is_some() {
                            return Err(IrgenError::new(
                                format!("{source:#?}"),
                                IrgenErrorMessage::Redefinition { name },
                            ));
                        }
                        *var_initializer = Some(initializer.node.clone());
                    }
                    ir::Declaration::Function { .. } => {
                        return Err(IrgenError::new(
                            format!("{source:#?}"),
                            IrgenErrorMessage::Misc {
                                message: "illegal initializer (only variables can be initialized)"
                                    .to_string(),
                            },
                        ));
                    }
                }
            }

            self.add_decl(&name, decl)?;
        }

        Ok(())
    }

    /// Add a function definition.
    fn add_function_definition(&mut self, source: &FunctionDefinition) -> Result<(), IrgenError> {
        // Creates name and signature.
        let specifiers = &source.specifiers;
        let declarator = &source.declarator.node;

        let name = name_of_declarator(declarator);
        let name_of_params = name_of_params_from_function_declarator(declarator)
            .expect("declarator is not from function definition");

        // 解析返回类型的基础部分
        let (base_dtype, is_typedef) = ir::Dtype::try_from_ast_declaration_specifiers(specifiers)
            .map_err(|e| {
            IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        if is_typedef {
            return Err(IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::Misc {
                    message: "function definition declared typedef".into(),
                },
            ));
        }

        // 将基础类型和声明修饰符（指针、数组等）结合，形成完整的函数类型
        let dtype = base_dtype
            .with_ast_declarator(declarator)
            .map_err(|e| {
                IrgenError::new(
                    format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?
            .deref()
            .clone();
        // 替换掉类型中的所有 typedef 别名
        let dtype = dtype.resolve_typedefs(&self.typedefs).map_err(|e| {
            IrgenError::new(
                format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                IrgenErrorMessage::InvalidDtype { dtype_error: e },
            )
        })?;

        // 创建一个 FunctionSignature 对象，描述函数的返回类型和参数类型
        let signature = ir::FunctionSignature::new(dtype.clone());

        // 函数定义同时也隐含了一个声明。将该函数加入到全局声明表 self.decls 中
        // Adds new declaration if nothing has been declared before
        let decl = ir::Declaration::try_from(dtype).unwrap();
        self.add_decl(&name, decl)?;

        // 在翻译函数体之前，需要准备好一个“翻译现场” —— IrgenFunc 结构体。

        // Prepare scope for global variable
        // 函数体内部可以访问全局变量。遍历当前所有的全局声明（self.decls），为每一个全局变量/函数创建一个 Constant::global_variable 指针
        let global_scope: HashMap<_, _> = self
            .decls
            .iter()
            .map(|(name, decl)| {
                let dtype = decl.dtype();
                let pointer = ir::Constant::global_variable(name.clone(), dtype);
                let operand = ir::Operand::constant(pointer);
                (name.clone(), operand)
            })
            .collect();

        // Prepares for irgen pass.
        // 创建 IrgenFunc 实例：初始化块计数器（BID）、寄存器计数器（tempid）、分配列表（allocations）等
        let mut irgen = IrgenFunc {
            return_type: signature.ret.clone(),
            bid_init: Irgen::BID_INIT,
            phinodes_init: Vec::new(),
            allocations: Vec::new(),
            blocks: BTreeMap::new(),
            bid_counter: Irgen::BID_COUNTER_INIT,
            tempid_counter: Irgen::TEMPID_COUNTER_INIT,
            typedefs: &self.typedefs,
            structs: &self.structs,
            // Initial symbol table has scope for global variable already
            symbol_table: vec![global_scope], // 将这些全局符号放入初始的 symbol_table（作用域栈的底层）
        };
        // 创建一个 Context，从 BID_INIT 开始编写指令
        let mut context = Context::new(irgen.bid_init);

        // 开启函数局部作用域
        // Enter variable scope for alloc registers matched with function parameters
        irgen.enter_scope();

        // Creates the init block that stores arguments.
        // 先在self.allocations中为函数参数分配内存，用寄存器%l0、%l1...存储地址
        // 根据函数参数类型设置self.phinodes_init, 即第一个block的phinodes，例如第一个参数为int a，则
        // block 0 的第一个phinode为i32:a, RegisterId为%b0:p0
        // 将block 0 上的phinode存储到%l0、%l1指向的内存, e.g. %b0:i0:unit = store %b0:p0:i32 %l0:i32*
        // 将参数名和这些寄存器的映射存入符号表symbol_table,如a -> %l0:i32 这个映射
        irgen
            .translate_parameter_decl(&signature, irgen.bid_init, &name_of_params, &mut context)
            .map_err(|e| {
                IrgenError::new(format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"), e)
            })?;

        // Translates statement.
        // 遍历函数的大括号 { ... } 里的所有语句，生成对应的 IR 指令, context 会记录生成的指令流，并可能根据 if/while 语句拆分成多个基本块
        irgen.translate_stmt(&source.statement.node, &mut context, None, None)?;

        // Creates the end block
        let ret = signature.ret.set_const(false);
        let value = if ret == ir::Dtype::unit() {
            ir::Operand::constant(ir::Constant::unit())
        } else if ret == ir::Dtype::INT {
            // If "main" function, default return value is `0` when return type is `int`
            if name == "main" {
                ir::Operand::constant(ir::Constant::int(0, ret))
            } else {
                ir::Operand::constant(ir::Constant::undef(ret))
            }
        } else {
            ir::Operand::constant(ir::Constant::undef(ret))
        };

        // Last Block of the function
        irgen.insert_block(context, ir::BlockExit::Return { value });

        // Exit variable scope created above
        irgen.exit_scope();

        let func_def = ir::FunctionDefinition {
            allocations: irgen.allocations,
            blocks: irgen.blocks,
            bid_init: irgen.bid_init,
        };

        let decl = self
            .decls
            .get_mut(&name)
            .unwrap_or_else(|| panic!("The declaration of `{name}` must exist"));
        if let ir::Declaration::Function { definition, .. } = decl {
            if definition.is_some() {
                return Err(IrgenError::new(
                    format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                    IrgenErrorMessage::Misc {
                        message: format!("the name `{name}` is defined multiple time"),
                    },
                ));
            }

            // Update function definition
            *definition = Some(func_def);
        } else {
            panic!("`{name}` must be function declaration")
        }

        Ok(())
    }

    /// Adds a possibly existing declaration.
    ///
    /// Returns error if the previous declearation is incompatible with `decl`.
    fn add_decl(&mut self, name: &str, decl: ir::Declaration) -> Result<(), IrgenError> {
        let Some(old_decl) = self.decls.insert(name.to_string(), decl.clone()) else {
            return Ok(());
        };

        // Check if type is conflicting for pre-declared one
        if !old_decl.is_compatible(&decl) {
            return Err(IrgenError::new(
                name.to_string(),
                IrgenErrorMessage::ConflictingDtype {
                    dtype: old_decl.dtype(),
                    protorype_dtype: decl.dtype(),
                },
            ));
        }

        Ok(())
    }
}

/// Storage for instructions up to the insertion of a block
#[derive(Debug)]
struct Context {
    /// The block id of the current context.
    bid: ir::BlockId,
    /// Current instructions of the block.
    instrs: Vec<Named<ir::Instruction>>,
}

impl Context {
    /// Create a new context with block number bid
    fn new(bid: ir::BlockId) -> Self {
        Self {
            bid,
            instrs: Vec::new(),
        }
    }

    // Adds `instr` to the current context.
    fn insert_instruction(
        &mut self,
        instr: ir::Instruction,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let dtype = instr.dtype();
        self.instrs.push(Named::new(None, instr));

        Ok(ir::Operand::register(
            ir::RegisterId::temp(self.bid, self.instrs.len() - 1),
            dtype,
        ))
    }
}

/// A C function being translated.
struct IrgenFunc<'i> {
    /// return type of the function.
    return_type: ir::Dtype,
    /// initial block id for the function, typically 0.
    bid_init: ir::BlockId,
    /// arguments represented as initial phinodes. Order must be the same of that given in the C
    /// function.
    phinodes_init: Vec<Named<ir::Dtype>>,
    /// local allocations.
    allocations: Vec<Named<ir::Dtype>>,
    /// Map from block id to basic blocks
    blocks: BTreeMap<ir::BlockId, ir::Block>,
    /// current block id. `blocks` must have an entry for all ids less then this
    bid_counter: usize,
    /// current temporary id. Used to create temporary names in the IR for e.g,
    tempid_counter: usize,
    /// Usable definitions
    typedefs: &'i HashMap<String, ir::Dtype>,
    /// Usable structs
    // TODO: Add examples on how to use properly use this field.
    structs: &'i HashMap<String, Option<ir::Dtype>>,
    /// Current symbol table. The initial symbol table has the global variables.
    symbol_table: Vec<HashMap<String, ir::Operand>>,
}

impl IrgenFunc<'_> {
    /// Allocate a new block id.
    fn alloc_bid(&mut self) -> ir::BlockId {
        let bid = self.bid_counter;
        self.bid_counter += 1;
        ir::BlockId(bid)
    }

    /// Allocate a new temporary id.
    fn alloc_tempid(&mut self) -> String {
        let tempid = self.tempid_counter;
        self.tempid_counter += 1;
        format!("t{tempid}")
    }

    /// Create a new allocation with type given by `alloc`.
    fn insert_alloc(&mut self, alloc: Named<ir::Dtype>) -> ir::RegisterId {
        self.allocations.push(alloc);
        let id = self.allocations.len() - 1;
        ir::RegisterId::local(id)
    }

    /// Insert a new block `context` with exit instruction `exit`.
    ///
    /// # Panic
    ///
    /// Panics if another block with the same bid as `context` already existed.
    fn insert_block(&mut self, context: Context, exit: ir::BlockExit) {
        let block = ir::Block {
            phinodes: if context.bid == self.bid_init {
                self.phinodes_init.clone()
            } else {
                Vec::new()
            },
            instructions: context.instrs,
            exit,
        };
        if self.blocks.insert(context.bid, block).is_some() {
            panic!("the bid `{}` is defined multiple time", context.bid)
        }
    }

    /// Enter a scope and create a new symbol table entry, i.e, we are at a `{` in the function.
    fn enter_scope(&mut self) {
        self.symbol_table.push(HashMap::new());
    }

    /// Exit a scope and remove the a oldest symbol table entry. i.e, we are at a `}` in the
    /// function.
    ///
    /// # Panic
    ///
    /// Panics if there are no scopes to exit, i.e, the function has a unmatched `}`.
    fn exit_scope(&mut self) {
        let _unused = self.symbol_table.pop().unwrap();
        debug_assert!(!self.symbol_table.is_empty())
    }

    /// Inserts `var` with `value` to the current symbol table.
    ///
    /// Returns Ok() if the current scope has no previously-stored entry for a given variable.
    fn insert_symbol_table_entry(
        &mut self,
        var: String,
        value: ir::Operand,
    ) -> Result<(), IrgenErrorMessage> {
        let cur_scope = self
            .symbol_table
            .last_mut()
            .expect("symbol table has no valid scope");
        if cur_scope.insert(var.clone(), value).is_some() {
            return Err(IrgenErrorMessage::Redefinition { name: var });
        }

        Ok(())
    }

    /// Transalte a C statement `stmt` under the current block `context`, with `continue` block
    /// `bid_continue` and break block `bid_break`.
    fn translate_stmt(
        &mut self,
        stmt: &Statement,
        context: &mut Context,
        bid_continue: Option<ir::BlockId>,
        bid_break: Option<ir::BlockId>,
    ) -> Result<(), IrgenError> {
        match stmt {
            Statement::Compound(items) => {
                self.enter_scope();
                for item in items {
                    match &item.node {
                        BlockItem::StaticAssert(_) => {
                            panic!("BlockItem::StaticAssert not supported")
                        }
                        BlockItem::Declaration(decl) => {
                            self.translate_declaration(&decl.node, context)
                                .map_err(|e| IrgenError {
                                    code: decl.write_string(),
                                    message: e,
                                })?;
                        }
                        BlockItem::Statement(stmt) => {
                            self.translate_stmt(&stmt.node, context, bid_continue, bid_break)?
                        }
                    }
                }
                self.exit_scope();
                Ok(())
            }
            Statement::Expression(expr) => {
                if let Some(expr) = expr {
                    let _unused = self
                        .translate_expr_rvalue(&expr.node, context)
                        .map_err(|e| IrgenError::new(expr.write_string(), e))?;
                }
                Ok(())
            }
            Statement::If(stmt) => {
                let then_stmt = &stmt.node.then_statement.node;
                let else_stmt_opt = &stmt.node.else_statement;
                let condition = &stmt.node.condition.node;

                let then_bid = self.alloc_bid();
                let else_bid = self.alloc_bid();
                let end_bid = self.alloc_bid();

                // translate condition into operand
                let cond_operand = self
                    .translate_condition(condition, context)
                    .map_err(|e| IrgenError::new(condition.write_string(), e))?;

                // 结束当前块：根据条件跳转
                let tgt_else = if else_stmt_opt.is_some() {
                    else_bid
                } else {
                    end_bid
                };
                self.insert_block(
                    mem::replace(context, Context::new(then_bid)),
                    ir::BlockExit::ConditionalJump {
                        condition: cond_operand,
                        arg_then: JumpArg::new(then_bid, vec![]),
                        arg_else: JumpArg::new(tgt_else, vec![]),
                    },
                );

                // then block, exit为跳转到end block
                self.translate_stmt(then_stmt, context, bid_continue, bid_break)?;
                self.insert_block(
                    mem::replace(context, Context::new(else_bid)),
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(end_bid, vec![]),
                    },
                );

                // else block (if exists)
                if let Some(else_stmt) = else_stmt_opt {
                    self.translate_stmt(&else_stmt.node, context, bid_continue, bid_break)?;
                }
                // 无论如何commit else block
                self.insert_block(
                    mem::replace(context, Context::new(end_bid)),
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(end_bid, vec![]),
                    },
                );
                // 此时context 指向“接下来该写指令的地方”：end_bid
                Ok(())
            }
            Statement::While(stmt) => {
                let cond = &stmt.node.expression.node;
                let loop_body = &stmt.node.statement.node;

                let cond_bid = self.alloc_bid();
                let loop_body_bid = self.alloc_bid();
                let end_bid = self.alloc_bid();

                // jump to the condition block
                self.insert_block(
                    mem::replace(context, Context::new(cond_bid)),
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(cond_bid, vec![]),
                    },
                );

                // translate to get condition value
                let cond_operand = self
                    .translate_condition(cond, context)
                    .map_err(|e| IrgenError::new(cond.write_string(), e))?;
                self.insert_block(
                    mem::replace(context, Context::new(loop_body_bid)),
                    ir::BlockExit::ConditionalJump {
                        condition: cond_operand,
                        arg_then: JumpArg::new(loop_body_bid, vec![]),
                        arg_else: JumpArg::new(end_bid, vec![]),
                    },
                );

                // translate the loop body
                self.translate_stmt(loop_body, context, Some(cond_bid), Some(end_bid))?;
                // commit body block
                self.insert_block(
                    mem::replace(context, Context::new(end_bid)),
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(cond_bid, vec![]),
                    },
                );
                Ok(())
            }
            _ => todo!(),
        }
    }

    // 检查声明类型，local allocation，必要时初始化变量(store)
    fn translate_declaration(
        &mut self,
        decl: &Declaration,
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        let (base_dtype, is_typedef) =
            ir::Dtype::try_from_ast_declaration_specifiers(&decl.specifiers)
                .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

        // resolve typedefs
        let base_dtype = base_dtype
            .resolve_typedefs(self.typedefs)
            .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

        // 函数内部不支持typedef
        assert!(!is_typedef);
        // 函数内部不支持定义结构体类型。检查结构体类型是否已被定义(使用辅助函数is_invalid_structure)
        if is_invalid_structure(&base_dtype, self.structs) {
            return Err(IrgenErrorMessage::Misc {
                message: format!("{} has incomplete type!", base_dtype),
            });
        }

        for init_decl in &decl.declarators {
            let declarator = &init_decl.node.declarator.node;
            let var = name_of_declarator(declarator); // 变量名字

            let dtype = base_dtype
                .clone()
                .with_ast_declarator(declarator)
                .map_err(|e| {
                    IrgenErrorMessage::InvalidDtype { dtype_error: e } // 变量类型
                })?
                .deref()
                .clone();

            // resolve typedefs
            let dtype = dtype
                .resolve_typedefs(self.typedefs)
                .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

            // translate initializer并根据其返回的operand初始化变量var
            match &dtype {
                ir::Dtype::Unit { .. } => todo!(),
                ir::Dtype::Int { .. }
                | ir::Dtype::Float { .. }
                | ir::Dtype::Pointer { .. }
                | ir::Dtype::Array { .. } => {
                    let value = if let Some(initializer) = &init_decl.node.initializer {
                        Some(self.translate_initializer(&initializer.node, context)?)
                    } else {
                        None
                    };
                    let _unused =
                        self.translate_alloc(var.clone(), dtype.clone(), value, context)?;
                }
                ir::Dtype::Function { .. } => todo!(),
                ir::Dtype::Typedef { .. } => {
                    panic!("typedef should be reduced to real types");
                }
                ir::Dtype::Struct { .. } => todo!(),
            }
        }
        Ok(())
    }

    fn translate_initializer(
        &mut self,
        initializer: &Initializer,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match initializer {
            Initializer::Expression(expr) => self.translate_expr_rvalue(&expr.node, context),
            Initializer::List(_) => panic!("Initializer::List is unsupported"), // 重点，{1, 2, 3},{.a = init, .b = init2}这种形式的初始化暂时不支持，因为比较复杂
        }
    }

    fn translate_expr_rvalue(
        &mut self,
        expr: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match expr {
            Expression::Identifier(id) => {
                let ptr = self.lookup_symbol_table(&id.node.name)?;
                let dtype_of_ptr = ptr.dtype();
                let ptr_inner_type = dtype_of_ptr
                    .get_pointer_inner()
                    .ok_or_else(|| panic!("`Operand` from `symbol_table` must be pointer type"))?;

                // 如果ptr指向一个函数，就返回ptr本身
                if ptr_inner_type.get_function_inner().is_some() {
                    return Ok(ptr);
                }

                // int a[10]; 则ptr类型为[10 x i32]*, 需要转换成i32*操作数
                if let Some(array_inner) = ptr_inner_type.get_array_inner() {
                    // we convert array into pointer
                    return self.convert_array_to_pointer(ptr, array_inner.clone(), context);
                }
                context.insert_instruction(ir::Instruction::Load { ptr })
            }
            _ => todo!(),
        }
    }

    fn lookup_symbol_table(&self, name: &str) -> Result<ir::Operand, IrgenErrorMessage> {
        for scope in self.symbol_table.iter().rev() {
            if let Some(operand) = scope.get(name) {
                return Ok(operand.clone());
            }
        }
        Err(IrgenErrorMessage::Misc {
            message: format!("{} not found in symbol table", name),
        })
    }

    // 将数组指针转换为指向其首元素的指针 (Array-to-pointer decay)
    fn convert_array_to_pointer(
        &mut self,
        ptr: ir::Operand,
        inner_dtype: ir::Dtype,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let tgt_ptr_type = ir::Dtype::pointer(inner_dtype);
        let offset = ir::Operand::constant(ir::Constant::int(0, ir::Dtype::LONG));

        context.insert_instruction(ir::Instruction::GetElementPtr {
            ptr,
            offset,
            dtype: tgt_ptr_type,
        })
    }

    fn translate_condition(
        &mut self,
        expr: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let val = self.translate_expr_rvalue(expr, context)?;
        let dtype = val.dtype();

        if dtype == ir::Dtype::BOOL {
            return Ok(val);
        }
        // 否则，生成"val != 0"的逻辑
        let zero = if dtype.get_int_width().is_some() {
            ir::Operand::constant(ir::Constant::int(0, dtype.clone()))
        } else if dtype.get_float_width().is_some() {
            ir::Operand::constant(ir::Constant::float(0.0, dtype.clone()))
        } else if dtype.get_pointer_inner().is_some() {
            ir::Operand::constant(ir::Constant::int(0, ir::Dtype::LONG))
        } else {
            return Err(IrgenErrorMessage::Misc {
                message: format!("expected scalar type in condition, found {}", dtype),
            });
        };

        // 插入比较指令
        context.insert_instruction(ir::Instruction::BinOp {
            op: BinaryOperator::NotEquals,
            lhs: val,
            rhs: zero,
            dtype: ir::Dtype::BOOL, // 返回的比较结果(temp register)是BOOL类型
        })
    }
    /// Translate initial parameter declarations of the functions to IR.
    ///
    /// For example, given the following C function from [`foo.c`][foo]:
    ///
    /// ```C
    /// int foo(int x, int y, int z) {
    ///    if (x == y) {
    ///       return y;
    ///    } else {
    ///       return z;
    ///    }
    /// }
    /// ```
    ///
    /// The IR before this function looks roughly as follows:
    ///
    /// ```text
    /// fun i32 @foo (i32, i32, i32) {
    ///   init:
    ///     bid: b0
    ///     allocations:
    ///
    ///   block b0:
    ///     %b0:p0:i32:x
    ///     %b0:p1:i32:y
    ///     %b0:p2:i32:z
    ///   ...
    /// ```
    ///
    /// With the following arguments :
    ///
    /// ```ignore
    /// signature = FunctionSignature { ret: ir::INT, params: vec![ir::INT, ir::INT, ir::INT] }
    /// bid_init = 0
    /// name_of_params = ["x", "y", "z"]
    /// context = // omitted
    /// ```
    ///
    /// The resulting IR after this function should be roughly follows :
    ///
    /// ```text
    /// fun i32 @foo (i32, i32, i32) {
    ///   init:
    ///     bid: b0
    ///     allocations:
    ///       %l0:i32:x
    ///       %l1:i32:y
    ///       %l2:i32:z
    ///
    ///   block b0:
    ///     %b0:p0:i32:x
    ///     %b0:p1:i32:y
    ///     %b0:p2:i32:z
    ///     %b0:i0:unit = store %b0:p0:i32 %l0:i32*
    ///     %b0:i1:unit = store %b0:p1:i32 %l1:i32*
    ///     %b0:i2:unit = store %b0:p2:i32 %l2:i32*
    ///   ...
    /// ```
    ///
    /// In particular, note that it is added to the local allocation list and store them to the
    /// initial phinodes.
    ///
    /// Note that the resulting IR is **a** solution. If you can think of a better way to
    /// translate parameters, feel free to do so.
    ///
    /// [foo]: https://github.com/kaist-cp/kecc-public/blob/main/examples/c/foo.c
    fn translate_parameter_decl(
        &mut self,
        signature: &ir::FunctionSignature,
        bid_init: ir::BlockId,
        name_of_params: &[String],
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        if signature.params.len() != name_of_params.len() {
            panic!("len of `parameters ` and `name_of_params` must be same")
        }
        // 对每个block arguments
        for (i, (dtype, var)) in izip!(&signature.params, name_of_params).enumerate() {
            // 设置 IrGenFunc的phinodes_init，在insert block时让入口块知道有这个参数声明
            self.phinodes_init
                .push(Named::new(Some(var.clone()), dtype.clone()));

            // 构造指向该参数的寄存器操作数 (%bid:pi)
            let value = Some(ir::Operand::register(
                ir::RegisterId::arg(bid_init, i),
                dtype.clone(),
            ));
            // allocate variables 并将block argument的值用于初始化(store指令)
            let _unused = self.translate_alloc(var.clone(), dtype.clone(), value, context)?;
        }
        Ok(())
    }

    fn translate_alloc(
        &mut self,
        var: String,                // the name of the var which is to be allocated
        dtype: ir::Dtype,           // the dtype of the var
        value: Option<ir::Operand>, // if is_some() store the value to initialize the memory location
        context: &mut Context,      // add instrs to context
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        // insert allocation, and get the allocation's registerId: aid
        let rid = self.insert_alloc(Named::new(Some(var.clone()), dtype.clone()));

        // Create Pointer
        let pointer_type = ir::Dtype::pointer(dtype.clone());
        let ptr_register = ir::Operand::register(rid, pointer_type);
        self.insert_symbol_table_entry(var, ptr_register.clone())?; // 变量var用ptr_register这个operand指代

        // initialize allocated variables if `value ` is not `None`
        if let Some(value) = value {
            // implicit type_cast，例如
            // void foo(float x)
            // foo(3);
            let value = self.translate_typecast(value, dtype, context)?; // 将用于初始化变量的Operand typecast成dtype目标类型
            return context.insert_instruction(ir::Instruction::Store {
                ptr: ptr_register,
                value,
            }); // 返回Store指令结果：temp register
        }
        Ok(ptr_register) // 返回指代该variable的register
    }

    fn translate_typecast(
        &mut self,
        value: ir::Operand,
        dtype: ir::Dtype,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        // 类型一致，直接返回原始操作数
        if value.dtype() == dtype {
            return Ok(value);
        }
        // 如果操作数是一个常量，尝试进行Constant Folding，减少运行时指令开销
        if let ir::Operand::Constant(constant) = value {
            return Ok(ir::Operand::constant(constant.typecast(dtype)));
        }

        context.insert_instruction(ir::Instruction::TypeCast {
            value,
            target_dtype: dtype,
        }) // 返回指代类型转换结果的临时寄存器
    }
}

#[inline]
fn name_of_declarator(declarator: &Declarator) -> String {
    let declarator_kind = &declarator.kind;
    match &declarator_kind.node {
        DeclaratorKind::Abstract => panic!("DeclaratorKind::Abstract is unsupported"),
        DeclaratorKind::Identifier(identifier) => identifier.node.name.clone(),
        DeclaratorKind::Declarator(declarator) => name_of_declarator(&declarator.node),
    }
}

#[inline]
fn name_of_params_from_function_declarator(declarator: &Declarator) -> Option<Vec<String>> {
    let declarator_kind = &declarator.kind;
    match &declarator_kind.node {
        DeclaratorKind::Abstract => panic!("DeclaratorKind::Abstract is unsupported"),
        DeclaratorKind::Identifier(_) => {
            name_of_params_from_derived_declarators(&declarator.derived)
        }
        DeclaratorKind::Declarator(next_declarator) => {
            name_of_params_from_function_declarator(&next_declarator.node)
                .or_else(|| name_of_params_from_derived_declarators(&declarator.derived))
        }
    }
}

#[inline]
fn name_of_params_from_derived_declarators(
    derived_decls: &[Node<DerivedDeclarator>],
) -> Option<Vec<String>> {
    for derived_decl in derived_decls {
        match &derived_decl.node {
            DerivedDeclarator::Function(func_decl) => {
                let name_of_params = func_decl
                    .node
                    .parameters
                    .iter()
                    .map(|p| name_of_parameter_declaration(&p.node))
                    .collect::<Option<Vec<_>>>()
                    .unwrap_or_default();
                return Some(name_of_params);
            }
            DerivedDeclarator::KRFunction(_kr_func_decl) => {
                // K&R function is allowed only when it has no parameter
                return Some(Vec::new());
            }
            _ => (),
        };
    }

    None
}

#[inline]
fn name_of_parameter_declaration(parameter_declaration: &ParameterDeclaration) -> Option<String> {
    let declarator = parameter_declaration.declarator.as_ref()?;
    Some(name_of_declarator(&declarator.node))
}

// 判断initializer是否是编译时期可确定的`常量表达式`，因为全局变量的初始化值必须是常量表达式
#[inline]
fn is_valid_initializer(
    initializer: &Initializer,
    dtype: &ir::Dtype,
    structs: &HashMap<String, Option<ir::Dtype>>,
) -> bool {
    match initializer {
        Initializer::Expression(expr) => match dtype {
            ir::Dtype::Int { .. } | ir::Dtype::Float { .. } | ir::Dtype::Pointer { .. } => {
                match &expr.node {
                    Expression::Constant(_) => true,
                    Expression::UnaryOperator(unary) => matches!(
                        &unary.node.operator.node,
                        UnaryOperator::Minus | UnaryOperator::Plus // 不支持1 + 2 或 &...
                    ),
                    _ => false,
                }
            }
            _ => false,
        },
        Initializer::List(items) => match dtype {
            ir::Dtype::Array { inner, .. } => items
                .iter()
                .all(|i| is_valid_initializer(&i.node.initializer.node, inner, structs)),
            ir::Dtype::Struct { name, .. } => {
                let name = name.as_ref().expect("struct should have its name");
                let struct_type = structs
                    .get(name)
                    .expect("struct type matched with `name` must exist")
                    .as_ref()
                    .expect("`struct_type` must have its definition");
                let fields = struct_type
                    .get_struct_fields()
                    .expect("`struct_type` must be struct type")
                    .as_ref()
                    .expect("`fields` must be `Some`");

                izip!(fields, items).all(|(f, i)| {
                    is_valid_initializer(&i.node.initializer.node, f.deref(), structs)
                })
            }
            _ => false,
        },
    }
}

#[inline]
fn is_invalid_structure(dtype: &ir::Dtype, structs: &HashMap<String, Option<ir::Dtype>>) -> bool {
    // When `dtype` is `Dtype::Struct`, `structs` has real definition of `dtype`
    // 断言：这里的 dtype 实例应该是“引用形式”的结构体
    // 即：它必须有名字，且它内部不直接携带字段信息（fields 为 None）
    // 因为完整的定义已经存放在了 Irgen 的全局 structs 表中
    if let ir::Dtype::Struct { name, fields, .. } = dtype {
        assert!(name.is_some() && fields.is_none()); // Dtype是struct且fields为空
        let name = name.as_ref().unwrap();
        // 核心逻辑：判断该结构体是否在全局表里“没有定义”
        // .is_none_or(Option::is_none) 处理了两种情况：
        // 1. structs.get(name) 返回 None -> 说明该结构体名字连声明都没见过。
        // 2. structs.get(name) 返回 Some(None) -> 说明见过声明（如 struct A;），但还没见到大括号定义的成员。
        structs.get(name).is_none_or(Option::is_none)
    } else {
        false
    }
}
