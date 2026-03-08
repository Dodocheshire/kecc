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
use std::collections::{BTreeMap, HashMap, binary_heap};
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

        // Creates the end block(对应函数末尾，此时没有任何语句，但我们有默认的返回逻辑)
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
    /// 可用于命名匿名结构体类型和匿名局部变量，i.e. struct %t1 / %l5:u1:t0
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
            Statement::DoWhile(stmt) => {
                let expr = &stmt.node.expression.node;
                let body = &stmt.node.statement.node;

                let loop_bid = self.alloc_bid();
                let cond_bid = self.alloc_bid();
                let end_bid = self.alloc_bid();

                self.insert_block(
                    mem::replace(context, Context::new(loop_bid)),
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(loop_bid, vec![]),
                    },
                );

                self.translate_stmt(body, context, Some(cond_bid), Some(end_bid))?;
                self.insert_block(
                    mem::replace(context, Context::new(cond_bid)),
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(cond_bid, vec![]),
                    },
                );

                let cond_operand = self
                    .translate_condition(expr, context)
                    .map_err(|e| IrgenError::new(expr.write_string(), e))?;
                self.insert_block(
                    mem::replace(context, Context::new(end_bid)),
                    ir::BlockExit::ConditionalJump {
                        condition: cond_operand,
                        arg_then: JumpArg::new(loop_bid, vec![]),
                        arg_else: JumpArg::new(end_bid, vec![]),
                    },
                );

                Ok(())
            }
            Statement::For(stmt) => {
                let init = &stmt.node.initializer.node;
                let cond_opt = &stmt.node.condition;
                let step_opt = &stmt.node.step;
                let body = &stmt.node.statement.node;

                let cond_bid = self.alloc_bid();
                let step_bid = self.alloc_bid();
                let loop_bid = self.alloc_bid();
                let end_bid = self.alloc_bid();

                self.enter_scope();
                match init {
                    ForInitializer::Declaration(decl) => {
                        self.translate_declaration(&decl.node, context)
                            .map_err(|e| IrgenError::new(decl.write_string(), e))?;
                    }
                    ForInitializer::Empty => {}
                    ForInitializer::Expression(expr) => {
                        let _unused = self
                            .translate_expr_rvalue(&expr.node, context)
                            .map_err(|e| IrgenError::new(expr.write_string(), e))?;
                    }
                    ForInitializer::StaticAssert(_) => {
                        panic!("ForInitializer::StaticAssert not supported");
                    }
                }

                self.insert_block(
                    mem::replace(context, Context::new(cond_bid)),
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(cond_bid, vec![]),
                    },
                );

                let cond_operand = if let Some(cond_expr) = cond_opt {
                    self.translate_condition(&cond_expr.node, context)
                        .map_err(|e| IrgenError::new(cond_expr.write_string(), e))?
                } else {
                    ir::Operand::constant(ir::Constant::int(1, ir::Dtype::BOOL))
                };

                self.insert_block(
                    mem::replace(context, Context::new(loop_bid)),
                    ir::BlockExit::ConditionalJump {
                        condition: cond_operand,
                        arg_then: JumpArg::new(loop_bid, vec![]),
                        arg_else: JumpArg::new(end_bid, vec![]),
                    },
                );

                self.translate_stmt(body, context, Some(step_bid), Some(end_bid))?;
                self.insert_block(
                    mem::replace(context, Context::new(step_bid)),
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(step_bid, vec![]),
                    },
                );

                if let Some(step_expr) = step_opt {
                    let _unused = self
                        .translate_expr_rvalue(&step_expr.node, context)
                        .map_err(|e| IrgenError::new(step_expr.write_string(), e))?;
                }
                self.insert_block(
                    mem::replace(context, Context::new(end_bid)),
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(cond_bid, vec![]),
                    },
                );

                self.exit_scope();
                Ok(())
            }
            Statement::Asm(_) => panic!("Statement::Asm not supported"),
            Statement::Labeled(stmt) => {
                panic!("Statement::Labeled not supported");
            }
            Statement::Goto(_) => panic!("Statement::Goto"),
            Statement::Switch(stmt) => {
                let value = self
                    .translate_expr_rvalue(&stmt.node.expression.node, context)
                    .map_err(|e| IrgenError::new(stmt.node.expression.node.write_string(), e))?;
                let bid_end = self.alloc_bid();
                let (cases, bid_default) =
                    self.translate_switch_body(&stmt.node.statement.node, bid_end)?; // 这里不影响context

                self.insert_block(
                    mem::replace(context, Context::new(bid_end)),
                    ir::BlockExit::Switch {
                        value,
                        default: JumpArg::new(bid_default, vec![]),
                        cases,
                    },
                );

                Ok(())
            }
            Statement::Continue => {
                let bid_continue = bid_continue.unwrap_or_else(|| panic!("no bid_continue"));
                let next_bid = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(next_bid)),
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(bid_continue, vec![]),
                    },
                );
                // the code after `continue` maybe deadcode
                Ok(())
            }
            Statement::Break => {
                let bid_break = bid_break.unwrap_or_else(|| panic!("no bid_break"));
                let next_bid = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(next_bid)),
                    ir::BlockExit::Jump {
                        arg: JumpArg::new(bid_break, vec![]),
                    },
                );
                // the code after `break` maybe deadcode
                Ok(())
            }
            Statement::Return(expr_opt) => {
                let ret_operand = if let Some(expr) = expr_opt {
                    let val = self
                        .translate_expr_rvalue(&expr.node, context)
                        .map_err(|e| IrgenError::new(expr.write_string(), e))?;
                    // 隐式转换为函数返回类型 self.return_type
                    self.translate_typecast(val, self.return_type.clone(), context)
                        .map_err(|e| IrgenError::new(expr.write_string(), e))?
                } else {
                    // return; 返回单位值unit
                    ir::Operand::constant(ir::Constant::unit())
                };

                let next_bid = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(next_bid)),
                    ir::BlockExit::Return { value: ret_operand },
                );

                Ok(())
            }
        }
    }

    // 检查声明类型，local allocation，必要时初始化变量
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
        // todo: 考虑函数体中匿名结构体的情况
        if is_invalid_structure(&base_dtype, self.structs) {
            return Err(IrgenErrorMessage::Misc {
                message: format!("{} has incomplete type or is anonymous struct", base_dtype),
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

            // 栈上分配内存
            let ptr_reg = self.insert_alloc(Named::new(Some(var.clone()), dtype.clone()));
            let ptr_operand = ir::Operand::register(ptr_reg, ir::Dtype::pointer(dtype.clone()));

            // 将变量存入符号表，此时映射的是它的地址指针
            self.insert_symbol_table_entry(var.clone(), ptr_operand.clone())?;

            // 处理初始化逻辑
            if let Some(initializer) = &init_decl.node.initializer {
                self.translate_initializer_recursive(
                    &ptr_operand,
                    &dtype,
                    &initializer.node,
                    context,
                )?;
            }
        }
        Ok(())
    }

    // hard
    fn translate_initializer_recursive(
        &mut self,
        ptr: &ir::Operand, // 当前要写入的内存地址 (Pointer Operand)
        dtype: &ir::Dtype, // 当前地址对应的 Dtype
        initializer: &Initializer,
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        match initializer {
            Initializer::Expression(expr) => {
                let val_op = self.translate_expr_rvalue(&expr.node, context)?;
                // implicit typecast
                let val_casted = self.translate_typecast(val_op, dtype.clone(), context)?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    // 结构体类型也能一条Store IR完成
                    ptr: ptr.clone(),
                    value: val_casted,
                })?;
            }
            // 列表初始化（例如 {1, 2, {3, 4}}）
            Initializer::List(items) => {
                match dtype {
                    // 数组初始化 [N x T]
                    ir::Dtype::Array { inner, size } => {
                        // 先将 [N x T]* 转换为 T* 用于计算偏移
                        let element_ptr_base =
                            context.insert_instruction(ir::Instruction::GetElementPtr {
                                ptr: ptr.clone(),
                                offset: ir::Operand::constant(ir::Constant::int(
                                    0,
                                    ir::Dtype::LONG,
                                )),
                                dtype: ir::Dtype::pointer(inner.deref().clone()),
                            })?;
                        let (elem_size, _) = inner.size_align_of(&self.structs).unwrap();

                        for (i, item) in items.iter().enumerate() {
                            // 赋值截断至前size个元素(防止超过数组大小)
                            if i >= *size {
                                break;
                            }
                            // 计算当前元素地址：element_ptr = base + i * sizeof(T)
                            let byte_offset = (i * elem_size) as u128;
                            let element_ptr =
                                context.insert_instruction(ir::Instruction::GetElementPtr {
                                    ptr: element_ptr_base.clone(),
                                    offset: ir::Operand::constant(ir::Constant::int(
                                        byte_offset,
                                        ir::Dtype::LONG,
                                    )),
                                    dtype: ir::Dtype::pointer(inner.deref().clone()),
                                })?;
                            // 递归初始化子元素
                            // 这里忽略每个InitializerListItem的designation字段，即假设{.a = ..., .b[1] = ...}这种委派不存在
                            self.translate_initializer_recursive(
                                &element_ptr,
                                inner.deref(),
                                &item.node.initializer.node,
                                context,
                            )?;
                        }
                    }
                    ir::Dtype::Struct { name, .. } => {
                        let struct_name = name.as_ref().expect("Struct must have a name");
                        // 结构体类型必须预先定义过
                        let struct_def = self.structs.get(struct_name).unwrap().as_ref().unwrap();
                        // 获取字段列表和预先计算好的偏移量
                        // 该Dtype必须是结构体，且字段定义非空
                        let fields = struct_def.get_struct_fields().unwrap().as_ref().unwrap();
                        let (_, _, offsets) = struct_def
                            .get_struct_size_align_offsets()
                            .unwrap()
                            .as_ref()
                            .unwrap();

                        for (field, &offset, item) in izip!(fields, offsets, items) {
                            let field_dtype = field.deref();
                            // 计算字段地址: field_ptr = struct_ptr + offset
                            let field_ptr =
                                context.insert_instruction(ir::Instruction::GetElementPtr {
                                    ptr: ptr.clone(), // struct pointer
                                    offset: ir::Operand::constant(ir::Constant::int(
                                        offset as u128,
                                        ir::Dtype::LONG,
                                    )),
                                    dtype: ir::Dtype::pointer(field_dtype.clone()),
                                })?;

                            // 递归初始化字段
                            self.translate_initializer_recursive(
                                &field_ptr,
                                field_dtype,
                                &item.node.initializer.node,
                                context,
                            )?;
                        }
                    }
                    _ => {
                        return Err(IrgenErrorMessage::Misc {
                            message: "Initializer List for non-aggregate type".to_string(),
                        });
                    }
                }
            }
        }

        Ok(())
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
                context.insert_instruction(ir::Instruction::Load { ptr }) // 注意Struct是可以直接一条IR Load的
            }
            Expression::Constant(constant) => {
                let constant = ir::Constant::try_from(&constant.node)
                    .expect("`constant` must be interpreted to `ir::Constant` value");
                Ok(ir::Operand::constant(constant))
            }
            Expression::StringLiteral(_string_lit) => {
                panic!("Expression::StringLiteral not supported")
            }
            Expression::GenericSelection(_) => panic!("Expression::GenericSelection not supported"),
            Expression::Member(member) => {
                let (field_ptr, field_dtype) = self.translate_member_expr_lvalue(
                    &member.node.operator.node,
                    &member.node.expression.node,
                    &member.node.identifier.node,
                    context,
                )?;

                // 如果该字段是数组类型，例如a.b中b是一个数组[i32 x 5],那么该字段作为右值退化成首元素的指针
                // 函数则直接返回指向函数的指针
                // 否则load
                if let Some(array_inner) = field_dtype.get_array_inner() {
                    self.convert_array_to_pointer(field_ptr, array_inner.clone(), context)
                } else if field_dtype.get_function_inner().is_some() {
                    Ok(field_ptr)
                } else {
                    context.insert_instruction(ir::Instruction::Load { ptr: field_ptr }) // 注意如果字段是结构体也是可以直接用一条IR Load的
                }
            }
            Expression::Call(call) => self.translate_func_call(&call.node, context),
            Expression::SizeOfTy(sz_ty) => {
                // sizeof(T) -> 编译器常量
                let dtype = ir::Dtype::try_from(&sz_ty.node.0.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                let dtype = dtype
                    .resolve_typedefs(&self.typedefs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                let (size, _) = dtype
                    .size_align_of(&self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                Ok(ir::Operand::constant(ir::Constant::int(
                    size as u128,
                    ir::Dtype::LONG,
                )))
            }
            Expression::SizeOfVal(sz_val) => {
                // sizeof(expr) -> 在 C 中表达式不求值，只需知道其类型
                // 这里我们通过临时翻译来获取表达式结果的Dtype(todo: 如何消除临时翻译过程中可能的副作用)
                let operand = self.translate_expr_rvalue(&sz_val.node.0.node, context)?;

                let (size, _) = operand
                    .dtype()
                    .size_align_of(&self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

                Ok(ir::Operand::constant(ir::Constant::int(
                    size as u128,
                    ir::Dtype::LONG,
                )))
            }
            Expression::AlignOf(typename) => {
                let dtype = ir::Dtype::try_from(&typename.node.0.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                let dtype = dtype
                    .resolve_typedefs(&self.typedefs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                let (_, align_of) = dtype
                    .size_align_of(&self.structs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                Ok(ir::Operand::constant(ir::Constant::int(
                    align_of as u128,
                    ir::Dtype::LONG,
                )))
            }
            Expression::UnaryOperator(unary) => self.translate_unary_op(&unary.node, context),
            Expression::Cast(cast) => {
                let tgt_dtype = ir::Dtype::try_from(&cast.node.type_name.node)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                let tgt_dtype = tgt_dtype
                    .resolve_typedefs(&self.typedefs)
                    .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
                let operand = self.translate_expr_rvalue(&cast.node.expression.node, context)?;
                self.translate_typecast(operand, tgt_dtype, context)
            }
            Expression::BinaryOperator(binary) => self.translate_binary_op(
                binary.node.operator.node.clone(),
                &binary.node.lhs.node,
                &binary.node.rhs.node,
                context,
            ),
            Expression::Conditional(conditional) => {
                self.translate_conditional(&conditional.node, context)
            }
            Expression::Comma(exprs) => {
                // (e1, e2, ... , en) 依次执行，返回最后一个表达式的值
                let mut last_op = None;
                for expr in exprs.deref() {
                    last_op = Some(self.translate_expr_rvalue(&expr.node, context)?);
                }
                last_op.ok_or_else(|| panic!("empty comma expression"))
            }
            _ => panic!(
                "CompoundLiteral, OffsetOf, VaArg, Statement variant of `Expression` is unsupported"
            ),
        }
    }

    fn translate_expr_lvalue(
        &mut self,
        expr: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match expr {
            Expression::Identifier(id) => self.lookup_symbol_table(&id.node.name),
            Expression::UnaryOperator(unary) => match &unary.node.operator.node {
                // 只允许解引用(*)做左值
                UnaryOperator::Indirection => {
                    // *a 的左值就是a(指针)
                    self.translate_expr_rvalue(&unary.node.operand.node, context)
                }
                _ => Err(IrgenErrorMessage::Misc {
                    message: "This error occured at `IrgenFunc::translate_expr_lvalue`".to_string(),
                }),
            },
            Expression::BinaryOperator(binary) => match &binary.node.operator.node {
                // 只允许索引([])当左值
                BinaryOperator::Index => self.translate_index_op_lvalue(
                    &binary.node.lhs.node,
                    &binary.node.rhs.node,
                    context,
                ),
                _ => Err(IrgenErrorMessage::Misc {
                    message: "binary operator expression cannot be used as l-value except \
                                index operator expression"
                        .to_string(),
                }),
            },
            Expression::StringLiteral(_string_lit) => todo!(),
            Expression::Member(member) => {
                // 如果 a.b 是一个 int[10]，它返回 (int[10])*
                // 如果 a.b 是一个函数，它返回 (function_type)* 不需要特殊处理
                let (field_ptr, _field_dtype) = self.translate_member_expr_lvalue(
                    &member.node.operator.node,
                    &member.node.expression.node,
                    &member.node.identifier.node,
                    context,
                )?;

                Ok(field_ptr)
            }
            Expression::Conditional(_)
            | Expression::Constant(_)
            | Expression::Call(_)
            | Expression::Comma(_)
            | Expression::SizeOfTy(_)
            | Expression::SizeOfVal(_)
            | Expression::AlignOf(_)
            | Expression::GenericSelection(_)
            | Expression::Cast(_) => Err(IrgenErrorMessage::Misc {
                message: "This error occured at `IrgenFunc::translate_expr_lvalue`".to_string(),
            }),
            _ => panic!("is unsupported"),
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

    fn translate_switch_body(
        &mut self,
        stmt: &Statement,
        bid_end: ir::BlockId,
    ) -> Result<(Vec<(ir::Constant, JumpArg)>, ir::BlockId), IrgenError> {
        // switch的翻译局限于如下形式
        // switch (e) {
        //  case 1: {A1; break;}
        //  case 2: {A2; break;}
        //  default: D;
        // }
        // B;
        // 检查是复合语句
        let items = if let Statement::Compound(items) = stmt {
            items
        } else {
            panic!("`Statement` in the `switch` is not supported except `Statement::Compound`")
        };

        let mut cases: Vec<(ir::Constant, JumpArg)> = Vec::new();
        let mut default = None;
        self.enter_scope();
        // 检查每个子句都是statement
        for item in items {
            match &item.node {
                BlockItem::Statement(stmt) => {
                    self.translate_switch_body_inner(
                        &stmt.node,
                        &mut cases,
                        &mut default,
                        bid_end,
                    )?;
                }
                _ => panic!(
                    "BlockItem::StaticAssert and Declaration is unsupported in `Switch`'s compound statement"
                ),
            }
        }
        // if default is not present, just jump to `bid_end`
        let default = default.unwrap_or(bid_end);
        Ok((cases, default))
    }

    fn translate_switch_body_inner(
        &mut self,
        stmt: &Statement,
        cases: &mut Vec<(ir::Constant, JumpArg)>,
        default: &mut Option<ir::BlockId>,
        bid_end: ir::BlockId,
    ) -> Result<(), IrgenError> {
        let label_stmt = if let Statement::Labeled(label_stmt) = stmt {
            &label_stmt.node
        } else {
            panic!(
                "`BlockItem::Statement` in the `Statement::Compound` of the `switch` \
                    is unsupported except `Statement::Labeled`
            "
            )
        };
        let bid = self.alloc_bid();
        // get case value from constant expr
        let case = match &label_stmt.label.node {
            Label::Identifier(_) => panic!("Label::Identifier not supported"),
            Label::Case(expr) => {
                let constant = ir::Constant::try_from(&expr.node).map_err(|_| {
                    IrgenError::new(
                        expr.write_string(),
                        IrgenErrorMessage::Misc {
                            message: "case label does not reduce to an integer constant"
                                .to_string(),
                        },
                    )
                })?;
                Some(constant)
            }
            Label::CaseRange(_) => panic!("Label::CaseRange not supported"),
            Label::Default => None,
        };
        let items = if let Statement::Compound(items) = &label_stmt.statement.node {
            items
        } else {
            panic!("Statement in label must be `Statement::Compound`")
        };

        // 为这个label compound statement创建分支：语句块
        let mut context = Context::new(bid);
        self.enter_scope();
        let (last, items) = items.split_last().expect("Statement::Compound has no item");

        // 翻译compound stmt里的items(除了最后一个BlockItem)
        for item in items {
            match &item.node {
                BlockItem::Declaration(decl) => self
                    .translate_declaration(&decl.node, &mut context)
                    .map_err(|e| IrgenError::new(decl.write_string(), e))?,
                BlockItem::Statement(stmt) => {
                    self.translate_stmt(&stmt.node, &mut context, None, None)?;
                }
                BlockItem::StaticAssert(_) => {
                    panic!("BlockItem::StaticAssert not supported");
                }
            }
        }

        // last element of the `Compound` items must be Statement::Break
        let last_stmt = if let BlockItem::Statement(stmt) = &last.node {
            &stmt.node
        } else {
            panic!("BlockItem in Statement::Compound of the `label` must be BlockItem::Statement ")
        };
        assert_eq!(
            last_stmt,
            &Statement::Break,
            "the last `BlockItem` in `Statement::Compound` of the `label` must be Statement::Break"
        );

        self.insert_block(
            context,
            ir::BlockExit::Jump {
                arg: JumpArg::new(bid_end, vec![]),
            },
        );
        self.exit_scope();

        // 根据`case`是否有值更新cases和default参数
        if let Some(case) = case {
            // 检查case value是否为整型
            if !case.is_integer_constant() {
                return Err(IrgenError::new(
                    label_stmt.label.write_string(),
                    IrgenErrorMessage::Misc {
                        message: "expression is not integer constant expression".to_string(),
                    },
                ));
            }
            // 检查cases里是否之前已经有这个case值了
            // todo: consider the case that same `value` but different `width`
            if cases.iter().any(|(c, _)| &case == c) {
                return Err(IrgenError::new(
                    label_stmt.label.write_string(),
                    IrgenErrorMessage::Misc {
                        message: "duplicate case value".to_string(),
                    },
                ));
            }

            cases.push((case, JumpArg::new(bid, vec![])));
        } else {
            // 检查default没有被重复定义过
            if default.is_some() {
                return Err(IrgenError::new(
                    label_stmt.label.write_string(),
                    IrgenErrorMessage::Misc {
                        message: "previous default already exists".to_string(),
                    },
                ));
            }
            *default = Some(bid);
        }

        Ok(())
    }

    // insert_block 实现对非初始块默认使用空的 Phi 节点（Vec::new()）,且使用 allocations 处理局部存储
    // 因此我们使用临时局部变量来保存then & else block中计算表达式得到的值
    // 1. 分配块 ID：分配 then 块、else 块和 end 块。
    // 2. 翻译条件：计算 cond 并根据结果执行 ConditionalJump
    // 3. 处理 Then 分支：翻译 then 表达式，确定结果类型，并在栈上 alloc 一个临时空间，将结果 store 进去
    // 4. 处理 Else 分支：翻译 else 表达式，将其转换为与 then 分支相同的类型，同样 store 到那个临时空间。
    // 5. 汇总：在 end 块执行 load，获取最终结果
    fn translate_conditional(
        &mut self,
        cond_expr: &ConditionalExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let then_bid = self.alloc_bid();
        let else_bid = self.alloc_bid();
        let end_bid = self.alloc_bid();

        let cond_val = self.translate_condition(&cond_expr.condition.node, context)?;
        self.insert_block(
            mem::replace(context, Context::new(then_bid)),
            ir::BlockExit::ConditionalJump {
                condition: cond_val,
                arg_then: JumpArg::new(then_bid, vec![]),
                arg_else: JumpArg::new(else_bid, vec![]),
            },
        );

        let v_then = self.translate_expr_rvalue(&cond_expr.then_expression.node, context)?;
        let res_dtype = v_then.dtype();

        // 在函数栈上分配临时空间用来存放三元运算的结果
        let tmp_name = self.alloc_tempid();
        let tmp_reg = self.insert_alloc(Named::new(Some(tmp_name), res_dtype.clone()));
        let tmp_ptr = ir::Operand::register(tmp_reg, res_dtype.clone());
        // 将 Then 的结果存入临时空间
        let _unused = context.insert_instruction(ir::Instruction::Store {
            ptr: tmp_ptr.clone(),
            value: v_then,
        })?;

        self.insert_block(
            mem::replace(context, Context::new(else_bid)),
            ir::BlockExit::Jump {
                arg: JumpArg::new(end_bid, vec![]),
            },
        );

        let v_else = self.translate_expr_rvalue(&cond_expr.else_expression.node, context)?;
        // 隐式转化
        // 在 C 语言标准中，三元运算符的结果类型是两个分支的“公共类型”。为了简化实验实现，这里以 then 分支的类型作为目标类型，并对 else 分支进行 typecast
        let v_else_casted = self.translate_typecast(v_else, res_dtype, context)?;
        // 将else结果存入同一个临时空间
        let _unused = context.insert_instruction(ir::Instruction::Store {
            ptr: tmp_ptr.clone(),
            value: v_else_casted,
        })?;

        self.insert_block(
            mem::replace(context, Context::new(end_bid)),
            ir::BlockExit::Jump {
                arg: JumpArg::new(end_bid, vec![]),
            },
        );

        // 在汇合点(end_bid)执行Load并返回其值
        context.insert_instruction(ir::Instruction::Load { ptr: tmp_ptr })
    }

    fn translate_func_call(
        &mut self,
        call: &CallExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        // 在 C 中，callee 既可以是标识符（函数名），也可以是函数指针表达式
        // 使用translate_expr_rvalue对标识符返回符号表里的全局/局部指针
        let callee_op = self.translate_expr_rvalue(&call.callee.node, context)?;

        // 获取函数签名信息: callee_op 的类型应该是 Pointer，其 inner 类型应该是 Function
        let callee_dtype = callee_op.dtype();
        let func_type = callee_dtype
            .get_pointer_inner()
            .and_then(|inner| inner.get_function_inner())
            .ok_or_else(|| IrgenErrorMessage::NeedFunctionOrFunctionPointer {
                callee: callee_op.clone(),
            })?;
        let (ret_dtype, param_dtypes) = func_type;

        // 处理参数
        let mut args = Vec::new();
        for (i, arg_ast) in call.arguments.iter().enumerate() {
            // 计算参数表达式的右值
            let arg_op = self.translate_expr_rvalue(&arg_ast.node, context)?;
            // 隐式转换参数为函数原型对应的参数类型, 超出原型定义的参数简化处理
            let arg_casted = if let Some(target_dtype) = param_dtypes.get(i) {
                self.translate_typecast(arg_op, target_dtype.clone(), context)?
            } else {
                arg_op
            };
            args.push(arg_casted);
        }

        // 插入call指令
        context.insert_instruction(ir::Instruction::Call {
            callee: callee_op,
            args,
            return_type: ret_dtype.clone(),
        })
    }

    // 3类逻辑：纯算术运算(如-,!,~)、内存操作(&, *)和具有副作用的自增自减(++,--)
    fn translate_unary_op(
        &mut self,
        unary: &UnaryOperatorExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let op = &unary.operator.node;
        let operand_ast = &unary.operand.node;

        match op {
            // 取地址运算符直接返回操作数的左值（即该变量在内存中的地址指针）
            UnaryOperator::Address => self.translate_expr_lvalue(operand_ast, context),
            // *(解引用)
            UnaryOperator::Indirection => {
                // 先计算操作数的右值（得到一个指针值）
                let ptr = self.translate_expr_rvalue(operand_ast, context)?;
                // 确保是指针
                if ptr.dtype().get_pointer_inner().is_none() {
                    return Err(IrgenErrorMessage::Misc {
                        message: "dereferencing a non-pointer value".to_string(),
                    });
                }
                // 从该地址读取数据
                context.insert_instruction(ir::Instruction::Load { ptr })
            }
            // 基础一元算术运算(+ - !)
            UnaryOperator::Plus | UnaryOperator::Minus | UnaryOperator::Negate => {
                let operand = self.translate_expr_rvalue(operand_ast, context)?;
                context.insert_instruction(ir::Instruction::UnaryOp {
                    op: op.clone(),
                    operand: operand.clone(),
                    dtype: operand.dtype(),
                })
            }
            // 按位取反 (~) 根据IR例子可得通过使用 XOR -1 来实现
            UnaryOperator::Complement => {
                let operand = self.translate_expr_rvalue(operand_ast, context)?;
                let dtype = operand.dtype();
                let mask = ir::Operand::constant(ir::Constant::int(u128::MAX, dtype.clone()));
                context.insert_instruction(ir::Instruction::BinOp {
                    op: BinaryOperator::BitwiseXor,
                    lhs: operand,
                    rhs: mask,
                    dtype,
                })
            }
            // 自增与自减 (++, --) 包括前置和后置
            UnaryOperator::PreIncrement
            | UnaryOperator::PreDecrement
            | UnaryOperator::PostIncrement
            | UnaryOperator::PostDecrement => {
                // 获取操作数左值
                let ptr = self.translate_expr_lvalue(operand_ast, context)?;
                let dtype = ptr.dtype().get_pointer_inner().unwrap().clone();

                // Load 当前值
                let old_val =
                    context.insert_instruction(ir::Instruction::Load { ptr: ptr.clone() })?;
                //计算新值 val+1 or val-1
                let is_inc = matches!(
                    op,
                    UnaryOperator::PreIncrement | UnaryOperator::PostIncrement
                );
                let bin_op = if is_inc {
                    BinaryOperator::Plus
                } else {
                    BinaryOperator::Minus
                };
                let one = ir::Operand::constant(ir::Constant::int(1, dtype.clone()));

                let new_val = context.insert_instruction(ir::Instruction::BinOp {
                    op: bin_op,
                    lhs: old_val.clone(),
                    rhs: one,
                    dtype: dtype.clone(),
                })?;

                // 将新值存回去
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr: ptr.clone(),
                    value: new_val.clone(),
                })?;

                // 根据++,--是后缀还是前缀决定返回旧值operand还是新值
                if matches!(
                    op,
                    UnaryOperator::PreDecrement | UnaryOperator::PreIncrement
                ) {
                    Ok(new_val)
                } else {
                    Ok(old_val)
                }
            }
        }
    }

    fn translate_binary_op(
        &mut self,
        op: BinaryOperator,
        lhs_ast: &Expression,
        rhs_ast: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match op {
            // a[i] equiv to *(a + i),使用GetElementPtr指令
            BinaryOperator::Index => {
                let element_ptr = self.translate_index_op_lvalue(lhs_ast, rhs_ast, context)?;
                // 作为右值，需要Load
                context.insert_instruction(ir::Instruction::Load { ptr: element_ptr })
            }
            // 普通算术和比较运算
            BinaryOperator::Multiply
            | BinaryOperator::Divide
            | BinaryOperator::Modulo
            | BinaryOperator::Plus
            | BinaryOperator::Minus
            | BinaryOperator::ShiftLeft
            | BinaryOperator::ShiftRight
            | BinaryOperator::Less
            | BinaryOperator::LessOrEqual
            | BinaryOperator::Greater
            | BinaryOperator::GreaterOrEqual
            | BinaryOperator::Equals
            | BinaryOperator::NotEquals
            | BinaryOperator::BitwiseAnd
            | BinaryOperator::BitwiseXor
            | BinaryOperator::BitwiseOr => {
                let lhs = self.translate_expr_rvalue(lhs_ast, context)?;
                let rhs = self.translate_expr_rvalue(rhs_ast, context)?;
                let rhs = self.translate_typecast(rhs, lhs.dtype(), context)?;
                // 确定结果类型，如果是比较运算，返回i1(BOOL)
                let res_dtype = if matches!(
                    op,
                    BinaryOperator::Less
                        | BinaryOperator::LessOrEqual
                        | BinaryOperator::Greater
                        | BinaryOperator::GreaterOrEqual
                        | BinaryOperator::Equals
                        | BinaryOperator::NotEquals
                ) {
                    ir::Dtype::BOOL
                } else {
                    lhs.dtype()
                };

                context.insert_instruction(ir::Instruction::BinOp {
                    op,
                    lhs,
                    rhs,
                    dtype: res_dtype,
                })
            }
            // 逻辑运算符,处理短路
            BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr => {
                self.translate_logical_op(op.clone(), lhs_ast, rhs_ast, context)
            }
            BinaryOperator::Assign => {
                let ptr = self.translate_expr_lvalue(lhs_ast, context)?;
                let dtype = ptr
                    .dtype()
                    .get_pointer_inner()
                    .ok_or_else(|| IrgenErrorMessage::Misc {
                        message: "Trying to Deref a non-pointer type".to_string(),
                    })?
                    .clone();
                let val = self.translate_expr_rvalue(rhs_ast, context)?;
                let val = self.translate_typecast(val, dtype, context)?;
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr: ptr.clone(),
                    value: val.clone(),
                })?;
                Ok(val) // 赋值表达式的值是赋值后的值
            }
            // 复合赋值运算(+= *= %= <<= ^=等)
            _ => {
                let ptr = self.translate_expr_lvalue(lhs_ast, context)?;
                let dtype = ptr
                    .dtype()
                    .get_pointer_inner()
                    .ok_or_else(|| IrgenErrorMessage::Misc {
                        message: "Trying to Deref a non-pointer type".to_string(),
                    })?
                    .clone();

                // a. load当前值
                let current_val =
                    context.insert_instruction(ir::Instruction::Load { ptr: ptr.clone() })?;
                // b. 计算右值
                let rhs_val = self.translate_expr_rvalue(rhs_ast, context)?;
                // 提取基础算术运算符
                let base_op = match op {
                    BinaryOperator::AssignPlus => BinaryOperator::Plus,
                    BinaryOperator::AssignMinus => BinaryOperator::Minus,
                    BinaryOperator::AssignMultiply => BinaryOperator::Multiply,
                    BinaryOperator::AssignDivide => BinaryOperator::Divide,
                    BinaryOperator::AssignModulo => BinaryOperator::Modulo,
                    BinaryOperator::AssignShiftLeft => BinaryOperator::ShiftLeft,
                    BinaryOperator::AssignShiftRight => BinaryOperator::ShiftRight,
                    BinaryOperator::AssignBitwiseAnd => BinaryOperator::BitwiseAnd,
                    BinaryOperator::AssignBitwiseXor => BinaryOperator::BitwiseXor,
                    BinaryOperator::AssignBitwiseOr => BinaryOperator::BitwiseOr,
                    _ => unreachable!(),
                };
                //c. typecast并运算
                let rhs_val = self.translate_typecast(rhs_val, dtype.clone(), context)?;
                let result = context.insert_instruction(ir::Instruction::BinOp {
                    op: base_op,
                    lhs: current_val,
                    rhs: rhs_val,
                    dtype: dtype.clone(),
                })?;

                //d. store
                let _unused = context.insert_instruction(ir::Instruction::Store {
                    ptr: ptr.clone(),
                    value: result.clone(),
                })?;

                Ok(result)
            }
        }
    }

    // translate a[i] as lvalue
    fn translate_index_op_lvalue(
        &mut self,
        lhs_ast: &Expression,
        rhs_ast: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let base = self.translate_expr_rvalue(lhs_ast, context)?;
        let index = self.translate_expr_rvalue(rhs_ast, context)?;

        let inner_type = base
            .dtype()
            .get_pointer_inner()
            .ok_or_else(|| IrgenErrorMessage::Misc {
                message: "indexing non-pointer type".to_string(),
            })?
            .clone();
        let (size, _) = inner_type
            .size_align_of(&self.structs)
            .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
        let size = ir::Operand::constant(ir::Constant::int(size as u128, ir::Dtype::LONG));

        // 计算byte 偏移量
        let offset = context.insert_instruction(ir::Instruction::BinOp {
            op: BinaryOperator::Multiply,
            lhs: index,
            rhs: size,
            dtype: ir::Dtype::LONG,
        })?;
        let element_ptr = context.insert_instruction(ir::Instruction::GetElementPtr {
            ptr: base,
            offset,
            dtype: ir::Dtype::pointer(inner_type.clone()),
        })?;

        Ok(element_ptr)
    }
    fn translate_logical_op(
        &mut self,
        op: BinaryOperator,
        lhs_ast: &Expression,
        rhs_ast: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let op_result = self.alloc_tempid();
        let local_id = self.insert_alloc(Named::new(Some(op_result), ir::Dtype::BOOL));
        let result_ptr = ir::Operand::register(local_id, ir::Dtype::pointer(ir::Dtype::BOOL));

        let else_bid = self.alloc_bid(); // 对lhs_ast估值后再对rhs_ast 估值
        let then_bid = self.alloc_bid(); // 对lhs_ast估值后不再对rhs_ast估值，而是store lhs的结果到op_result
        let end_bid = self.alloc_bid(); // 从局部临时变量中load结果作为logical operation的最终结果

        let (tgt_true, tgt_false) = if matches!(op, BinaryOperator::LogicalAnd) {
            // lhs_ast估值为真，跳转到tgt_true block
            (else_bid, then_bid)
        } else {
            (then_bid, else_bid)
        };

        let lhs = self.translate_condition(lhs_ast, context)?;
        self.insert_block(
            mem::replace(context, Context::new(then_bid)),
            ir::BlockExit::ConditionalJump {
                condition: lhs.clone(),
                arg_then: JumpArg::new(tgt_true, vec![]),
                arg_else: JumpArg::new(tgt_false, vec![]),
            },
        );

        // store lhs into result_ptr(temp allocation)
        let _unused = context.insert_instruction(ir::Instruction::Store {
            ptr: result_ptr.clone(),
            value: lhs,
        })?;
        self.insert_block(
            mem::replace(context, Context::new(else_bid)),
            ir::BlockExit::Jump {
                arg: JumpArg::new(end_bid, vec![]),
            },
        );

        // translate else_bid block(rhs_ast)
        let rhs = self.translate_condition(rhs_ast, context)?;
        let _unused = context.insert_instruction(ir::Instruction::Store {
            ptr: result_ptr.clone(),
            value: rhs,
        })?;
        self.insert_block(
            mem::replace(context, Context::new(end_bid)),
            ir::BlockExit::Jump {
                arg: JumpArg::new(end_bid, vec![]),
            },
        );

        // load `result_ptr` in end_bid block
        context.insert_instruction(ir::Instruction::Load { ptr: result_ptr })
    }

    fn translate_member_expr_lvalue(
        &mut self,
        op: &MemberOperator,
        expr: &Expression,
        member: &Identifier,
        context: &mut Context,
    ) -> Result<(ir::Operand, ir::Dtype), IrgenErrorMessage> {
        let base_ptr = match op {
            MemberOperator::Direct => {
                // a.b -> 先获取a的左值(地址)
                self.translate_expr_lvalue(expr, context)?
            }
            MemberOperator::Indirect => {
                // a->b -> 先获取a的右值(隐含a是个指针)
                self.translate_expr_rvalue(expr, context)?
            }
        };

        let base_dtype = base_ptr.dtype();
        let struct_dtype =
            base_dtype
                .get_pointer_inner()
                .ok_or_else(|| IrgenErrorMessage::Misc {
                    message: "member access on non-pointer type".to_string(),
                })?;
        // 在结构体定义中查找字段的偏移量和类型
        // 这里利用Dtype方法get_offset_struct_field
        let field_name = &member.name;
        let (offset, field_dtype) = struct_dtype
            .get_offset_struct_field(field_name, &self.structs)
            .ok_or_else(|| IrgenErrorMessage::Misc {
                message: format!("field {} not found in struct", field_name),
            })?;

        // 使用GetElementPtr计算字段地址
        let field_ptr = context.insert_instruction(ir::Instruction::GetElementPtr {
            ptr: base_ptr,
            offset: ir::Operand::constant(ir::Constant::int(offset as u128, ir::Dtype::LONG)),
            dtype: ir::Dtype::pointer(field_dtype.clone()),
        })?;

        Ok((field_ptr, field_dtype))
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
                    // 这里不考虑designation的存在
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
