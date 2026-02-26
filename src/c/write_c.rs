use core::panic;
use std::fmt::{Pointer, format};
use std::io::{Result, Write};

use lang_c::ast::*;
use lang_c::span::Node;

use crate::write_base::*;

impl<T: WriteLine> WriteLine for Node<T> {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        self.node.write_line(indent, write)
    }
}

impl<T: WriteString> WriteString for Node<T> {
    fn write_string(&self) -> String {
        self.node.write_string()
    }
}

impl WriteLine for TranslationUnit {
    /// VERY BIG HINT: You should start by understanding the [`writeln!`](https://doc.rust-lang.org/std/macro.writeln.html) macro.
    /// Translation Unit is a tuple struct
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        for ext_decl in &self.0 {
            ext_decl.write_line(indent, write)?;
            writeln!(write)?;
        }
        Ok(())
    }
}

impl WriteLine for ExternalDeclaration {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            Self::Declaration(decl) => decl.write_line(indent, write),
            Self::FunctionDefinition(fdef) => fdef.write_line(indent, write),
            Self::StaticAssert(static_assert) => static_assert.write_line(indent, write),
        }
    }
}

impl WriteLine for StaticAssert {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        let expr = self.expression.write_string();
        let msg = self.message.write_string();
        writeln!(write, "_Static_assert({}, {});", expr, msg)?;
        Ok(())
    }
}

impl WriteString for StaticAssert {
    fn write_string(&self) -> String {
        let expr = self.expression.write_string();
        let msg = self.message.write_string();
        format!("_Static_assert({}, {})", expr, msg)
    }
}
// int a[3] = {1,2,3}, b = 4; ast结构如下
// Declaration (write_line)
//  |—— DeclarationSpecifier::TypeSpecifier `int`
//  ├── InitDeclarator (write_string)
//  │     ├── Declarator `a[3]`
//  │     └── Initializer `{1, 2, 3}` (write_string)
//  ├── InitDeclarator (write_string)
//  |     |——Declarator `b`
//  |     |——Initializer `4`
// declarator还可能包含函数声明，例如int add(int a, int b);其中add(int a, int b)是declarator
// 这区别于：
// int add(int a, int b) {
//     return a + b;
// } 这属于 ExternalDeclaration::FunctionDefinition
// struct A {
//     int x;
// }; 只有DeclarationSpecifier::TypeSpecifier
// 没有 InitDeclarator，因为没有声明一个变量，只是“定义类型”
impl WriteLine for Declaration {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        let specifiers = self
            .specifiers
            .iter()
            .map(WriteString::write_string)
            .collect::<Vec<_>>()
            .join(" ");
        write!(write, "{}", specifiers);
        if !self.declarators.is_empty() {
            write!(write, " ")?;
            for (i, init_decl) in self.declarators.iter().enumerate() {
                if i > 0 {
                    write!(write, ", ")?;
                }
                write!(write, "{}", init_decl.write_string())?;
            }
        }
        writeln!(write, ";")?;
        Ok(())
    }
}

// “无分号版本”的 string 输出
impl WriteString for Declaration {
    fn write_string(&self) -> String {
        let specifiers = self
            .specifiers
            .iter()
            .map(WriteString::write_string)
            .collect::<Vec<_>>()
            .join(" ");

        let mut result = specifiers;

        if !self.declarators.is_empty() {
            let decls = self
                .declarators
                .iter()
                .map(|d| d.write_string())
                .collect::<Vec<_>>()
                .join(", ");

            result.push(' ');
            result.push_str(&decls);
        }

        result
    }
}

impl WriteString for DeclarationSpecifier {
    fn write_string(&self) -> String {
        match self {
            DeclarationSpecifier::StorageClass(sc) => sc.write_string(),
            DeclarationSpecifier::TypeSpecifier(ts) => ts.write_string(),
            DeclarationSpecifier::TypeQualifier(tq) => tq.write_string(),
            DeclarationSpecifier::Function(f) => f.write_string(),
            DeclarationSpecifier::Alignment(a) => a.write_string(),
            DeclarationSpecifier::Extension(e) => "".into(),
        }
    }
}

// 类型说明符
impl WriteString for TypeSpecifier {
    fn write_string(&self) -> String {
        match self {
            TypeSpecifier::Void => "void".into(),
            TypeSpecifier::Char => "char".into(),
            TypeSpecifier::Short => "short".into(),
            TypeSpecifier::Int => "int".into(),
            TypeSpecifier::Long => "long".into(),
            TypeSpecifier::Float => "float".into(),
            TypeSpecifier::Double => "double".into(),
            TypeSpecifier::Signed => "signed".into(),
            TypeSpecifier::Unsigned => "unsigned".into(),
            TypeSpecifier::Bool => "_Bool".into(),
            TypeSpecifier::Complex => "_Complex".into(),

            TypeSpecifier::Atomic(type_name) => {
                format!("_Atomic({})", type_name.write_string())
            }

            TypeSpecifier::Struct(s) => s.write_string(),

            TypeSpecifier::Enum(e) => e.write_string(),

            TypeSpecifier::TypedefName(id) => id.node.name.clone(),

            TypeSpecifier::TypeOf(t) => t.write_string(),

            TypeSpecifier::TS18661Float(f) => panic!("TypeSpecifier::TS18661Float"),
        }
    }
}

impl WriteString for TypeName {
    fn write_string(&self) -> String {
        let mut res = String::new();
        for (i, spec) in self.specifiers.iter().enumerate() {
            if i > 0 {
                res.push(' ');
            }
            res.push_str(&spec.write_string());
        }

        if let Some(decl) = &self.declarator {
            if !res.is_empty() {
                // 可能TypeName就是declarator 'T',没有specifiers/qualifiers
                res.push(' ');
            }
            res.push_str(&decl.write_string());
        }
        res
    }
}
// struct or union type specifier:
// struct-or-union identifier_opt {struct-declaration-list}
// struct-or-union identifier
// struct-declaration:
// specifier-qualifier-list struct-declarator-list
// struct-declarator:(结构体子段)
// declarator
// declarator_opt : constant-expression
impl WriteString for StructType {
    fn write_string(&self) -> String {
        let struct_or_union = match self.kind.node {
            StructKind::Struct => "struct".to_string(),
            StructKind::Union => "union".to_string(),
        };
        let identifier_opt = self
            .identifier
            .as_ref()
            .map_or("".into(), |e| e.node.name.clone());
        let struct_declarations = self.declarations.as_ref().map_or("".into(), |decl_vec| {
            let mut decls_str = String::from("{ ");
            for decl in decl_vec {
                decls_str.push_str(&decl.write_string());
                decls_str.push_str("; ");
            }
            decls_str.push('}');
            decls_str
        });

        format!(
            "{} {} {}",
            struct_or_union, identifier_opt, struct_declarations
        )
    }
}

impl WriteString for StructDeclaration {
    fn write_string(&self) -> String {
        match self {
            StructDeclaration::Field(field) => {
                let mut s = String::new();
                // specifiers and qualifiers
                let specs: Vec<String> = field
                    .node
                    .specifiers
                    .iter()
                    .map(|s| s.write_string())
                    .collect();
                s.push_str(&specs.join(" "));

                // declarators(不一定定义了字段，可能只有type specifier)
                if !field.node.declarators.is_empty() {
                    s.push(' ');
                    let decls: Vec<String> = field
                        .node
                        .declarators
                        .iter()
                        .map(|d| d.write_string())
                        .collect();

                    s.push_str(&decls.join(", "));
                }

                s.push(';');
                s
            }
            StructDeclaration::StaticAssert(sa) => sa.write_string(),
        }
    }
}

impl WriteString for StructDeclarator {
    fn write_string(&self) -> String {
        let mut decl_str = String::new();

        // declarator
        if let Some(decl) = &self.declarator {
            decl_str.push_str(&decl.write_string());
        }

        // bit-field 位域
        if let Some(width) = &self.bit_width {
            decl_str.push_str(" : ");
            decl_str.push_str(&width.write_string());
        }

        decl_str
    }
}

impl WriteString for EnumType {
    fn write_string(&self) -> String {
        let mut res = String::from("enum");
        if let Some(id) = &self.identifier {
            res.push(' ');
            res.push_str(&id.node.name);
        }

        if !self.enumerators.is_empty() {
            let enums = self
                .enumerators
                .iter()
                .map(|e| e.write_string())
                .collect::<Vec<_>>()
                .join(", ");
            res.push_str("{ ");
            res.push_str(&enums);
            res.push_str(" }");
        }
        res
    }
}

impl WriteString for Enumerator {
    fn write_string(&self) -> String {
        let name = self.identifier.node.name.clone();
        if let Some(expr) = &self.expression {
            format!("{} = {}", name, expr.write_string())
        } else {
            name
        }
    }
}

impl WriteString for TypeOf {
    fn write_string(&self) -> String {
        match self {
            TypeOf::Expression(expr) => format!("typeof({})", expr.write_string()),
            TypeOf::Type(ty) => {
                format!("typeof({})", ty.write_string())
            }
        }
    }
}
// TypeSpecifier/TypeQualifier
impl WriteString for SpecifierQualifier {
    fn write_string(&self) -> String {
        match self {
            SpecifierQualifier::TypeSpecifier(ts) => ts.write_string(),
            SpecifierQualifier::TypeQualifier(tq) => tq.write_string(),
            SpecifierQualifier::Extension(ext) => "".into(),
        }
    }
}

// 类型限定符
impl WriteString for TypeQualifier {
    fn write_string(&self) -> String {
        match self {
            TypeQualifier::Const => "const".into(),
            TypeQualifier::Restrict => "restrict".into(),
            TypeQualifier::Volatile => "volatile".into(),

            // Clang nullability extensions
            TypeQualifier::Nonnull => "_Nonnull".into(),
            TypeQualifier::NullUnspecified => "_Null_unspecified".into(),
            TypeQualifier::Nullable => "_Nullable".into(),

            // C11
            TypeQualifier::Atomic => "_Atomic".into(),
        }
    }
}
impl WriteString for FunctionSpecifier {
    fn write_string(&self) -> String {
        match self {
            FunctionSpecifier::Inline => "inline".into(),
            FunctionSpecifier::Noreturn => "_Noreturn".into(),
        }
    }
}
impl WriteString for AlignmentSpecifier {
    fn write_string(&self) -> String {
        match self {
            AlignmentSpecifier::Type(t) => {
                format!("_Alignas({})", t.write_string())
            }
            AlignmentSpecifier::Constant(expr) => {
                format!("_Alignas({})", expr.write_string())
            }
        }
    }
}
impl WriteString for StorageClassSpecifier {
    fn write_string(&self) -> String {
        match self {
            StorageClassSpecifier::Typedef => "typedef".into(),
            StorageClassSpecifier::Extern => "extern".into(),
            StorageClassSpecifier::Static => "static".into(),
            StorageClassSpecifier::ThreadLocal => "_Thread_local".into(),
            StorageClassSpecifier::Auto => "auto".into(),
            StorageClassSpecifier::Register => "register".into(),
        }
    }
}

impl WriteString for Expression {
    fn write_string(&self) -> String {
        match self {
            Expression::Identifier(id) => id.node.name.clone(),
            Expression::Constant(c) => c.write_string(),
            Expression::StringLiteral(s) => s.write_string(),

            Expression::SizeOfTy(t) => {
                format!("sizeof({})", t.node.0.write_string())
            }
            Expression::SizeOfVal(t) => {
                format!("sizeof({})", t.node.0.write_string())
            }

            Expression::AlignOf(t) => {
                format!("_Alignof({})", t.node.0.write_string())
            }

            Expression::Call(call) => call.write_string(),
            Expression::Member(m) => m.write_string(),

            Expression::UnaryOperator(u) => u.write_string(),
            Expression::BinaryOperator(b) => b.write_string(),
            Expression::Conditional(c) => c.write_string(),
            Expression::Cast(c) => c.write_string(),

            Expression::Comma(exprs) => {
                let comma_exprs = exprs
                    .iter()
                    .map(|e| e.write_string())
                    .collect::<Vec<_>>()
                    .join(", ");

                format!("({})", comma_exprs)
            }

            Expression::CompoundLiteral(c) => c.write_string(),

            Expression::OffsetOf(o) => o.write_string(),

            Expression::VaArg(v) => v.write_string(),
            // 非普通语句，语句表达式，来自gnu c extension
            // int x = ({
            //     int a = 1;
            //     int b = 2;
            //     a + b;
            // }); 整个 { ... } 是一个 expression, 值是最后一个表达式的值 `a+b`
            Expression::Statement(s) => {
                format!("({})", s.write_string()) // 这里没考虑缩进
            }

            Expression::GenericSelection(g) => g.write_string(),
        }
    }
}

impl WriteString for Constant {
    fn write_string(&self) -> String {
        match self {
            Constant::Integer(i) => i.write_string(),
            Constant::Float(f) => f.write_string(),
            Constant::Character(c) => format!("'{}'", c),
        }
    }
}

impl WriteString for Integer {
    fn write_string(&self) -> String {
        let mut p = match self.base {
            IntegerBase::Decimal => String::new(),
            IntegerBase::Octal => "0".to_string(),
            IntegerBase::Hexadecimal => "0x".to_string(),
            IntegerBase::Binary => "0b".to_string(),
        };
        // 这里number里不包含了基的信息：0 / 0x / 0b
        let mut s = format!("{}{}", p, self.number);
        if self.suffix.unsigned {
            s.push('u');
        }
        match self.suffix.size {
            IntegerSize::Int => {}
            IntegerSize::Long => s.push('l'),
            IntegerSize::LongLong => s.push_str("ll"),
        }

        if self.suffix.imaginary {
            s.push('i');
        }
        s
    }
}
impl WriteString for Float {
    fn write_string(&self) -> String {
        let mut p = match self.base {
            FloatBase::Decimal => String::new(),
            FloatBase::Hexadecimal => String::from("0x"),
        };

        let mut s = format!("{}{}", p, self.number);
        match self.suffix.format {
            FloatFormat::Float => s.push('f'),
            FloatFormat::Double => {} // 默认double
            FloatFormat::LongDouble => s.push('l'),
            FloatFormat::TS18661Format(_) => {} // 暂时忽略
        }
        if self.suffix.imaginary {
            s.push('i');
        }
        s
    }
}
//把 Vec<String> 拼成一个带引号的字符串
impl WriteString for StringLiteral {
    fn write_string(&self) -> String {
        let mut result = String::from("\"");

        for part in self {
            result.push_str(part);
        }

        result.push('"');
        result
    }
}
impl WriteString for CallExpression {
    fn write_string(&self) -> String {
        let callee = self.callee.write_string();
        let args = self
            .arguments
            .iter()
            .map(|arg| arg.write_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!("{}({})", callee, args)
    }
}
impl WriteString for MemberExpression {
    fn write_string(&self) -> String {
        let expr = self.expression.write_string();
        let ident = self.identifier.node.name.clone();
        let op = match self.operator.node {
            MemberOperator::Direct => ".",
            MemberOperator::Indirect => "->",
        };
        format!("({}{}{})", expr, op, ident)
    }
}

impl WriteString for UnaryOperatorExpression {
    fn write_string(&self) -> String {
        let op = self.operand.write_string();
        match self.operator.node {
            UnaryOperator::PostIncrement => format!("({}++)", op),
            UnaryOperator::PostDecrement => format!("({}--)", op),

            UnaryOperator::PreIncrement => format!("(++{})", op),
            UnaryOperator::PreDecrement => format!("(--{})", op),

            UnaryOperator::Address => format!("(&{})", op),
            UnaryOperator::Indirection => format!("(*{})", op),

            UnaryOperator::Plus => format!("(+{})", op),
            UnaryOperator::Minus => format!("(-{})", op),

            UnaryOperator::Complement => format!("(~{})", op),
            UnaryOperator::Negate => format!("(!{})", op),
        }
    }
}
impl WriteString for BinaryOperatorExpression {
    fn write_string(&self) -> String {
        let lhs = self.lhs.write_string();
        let rhs = self.rhs.write_string();

        let op = match self.operator.node {
            BinaryOperator::Index => return format!("{}[{}]", lhs, rhs),

            BinaryOperator::Multiply => "*",
            BinaryOperator::Divide => "/",
            BinaryOperator::Modulo => "%",

            BinaryOperator::Plus => "+",
            BinaryOperator::Minus => "-",

            BinaryOperator::ShiftLeft => "<<",
            BinaryOperator::ShiftRight => ">>",

            BinaryOperator::Less => "<",
            BinaryOperator::Greater => ">",
            BinaryOperator::LessOrEqual => "<=",
            BinaryOperator::GreaterOrEqual => ">=",

            BinaryOperator::Equals => "==",
            BinaryOperator::NotEquals => "!=",

            BinaryOperator::BitwiseAnd => "&",
            BinaryOperator::BitwiseXor => "^",
            BinaryOperator::BitwiseOr => "|",

            BinaryOperator::LogicalAnd => "&&",
            BinaryOperator::LogicalOr => "||",

            BinaryOperator::Assign => "=",
            BinaryOperator::AssignMultiply => "*=",
            BinaryOperator::AssignDivide => "/=",
            BinaryOperator::AssignModulo => "%=",
            BinaryOperator::AssignPlus => "+=",
            BinaryOperator::AssignMinus => "-=",
            BinaryOperator::AssignShiftLeft => "<<=",
            BinaryOperator::AssignShiftRight => ">>=",
            BinaryOperator::AssignBitwiseAnd => "&=",
            BinaryOperator::AssignBitwiseXor => "^=",
            BinaryOperator::AssignBitwiseOr => "|=",
        };

        format!("({} {} {})", lhs, op, rhs)
    }
}

impl WriteString for ConditionalExpression {
    fn write_string(&self) -> String {
        let cond = self.condition.write_string();
        let then_expr = self.then_expression.write_string();
        let else_expr = self.else_expression.write_string();

        format!("({} ? {} : {})", cond, then_expr, else_expr)
    }
}

impl WriteString for CastExpression {
    fn write_string(&self) -> String {
        let ty = self.type_name.write_string();
        let expr = self.expression.write_string();

        format!("(({}) {})", ty, expr)
    }
}

impl WriteString for CompoundLiteral {
    // 复合子面量：在表达式里临时创建一个对象，并立刻用初始化列表给它赋值,可以对其取地址
    // e.g. (int[]){2, 4}, (struct Point){.x = 1, .y = 2}
    // (type_name){ initializer_list }
    fn write_string(&self) -> String {
        let type_name = self.type_name.node.write_string();
        let init_list = self
            .initializer_list
            .iter()
            .map(|init_list_item| init_list_item.write_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!("(({}){{{}}})", type_name, init_list) // {{}}转义花括号
    }
}
impl WriteString for InitializerListItem {
    fn write_string(&self) -> String {
        let designation = self
            .designation // designation may be empty
            .iter()
            .map(|designator| designator.write_string())
            .collect::<Vec<String>>()
            .join("");
        let initializer = self.initializer.write_string();
        if designation.is_empty() {
            initializer // no `=`
        } else {
            format!("{} = {}", designation, initializer)
        }
    }
}
impl WriteString for Designator {
    fn write_string(&self) -> String {
        match self {
            Designator::Index(expr) => format!("[{}]", expr.write_string()),
            Designator::Member(id) => format!(".{}", id.node.name),
            Designator::Range(rg) => format!(
                "[{} ... {}]",
                rg.node.from.write_string(),
                rg.node.to.write_string()
            ),
        }
    }
}
impl WriteString for Initializer {
    fn write_string(&self) -> String {
        match self {
            Self::Expression(expr) => expr.write_string(),
            Self::List(init_list_items) => {
                let init_list = init_list_items
                    .iter()
                    .map(|init_list_item| init_list_item.write_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{}}}", init_list)
            }
        }
    }
}
// OffsetOfExpression: 成员字段在类中的偏移量
// offsetof(type, member-designator)
impl WriteString for OffsetOfExpression {
    fn write_string(&self) -> String {
        let type_name = self.type_name.write_string();
        let member_designator = self.designator.write_string();
        format!("offsetof({}, {})", type_name, member_designator)
    }
}
// OffsetDesignator: {base: Identifier(起始), members: Vec<_>(后续访问链)}
// e.g. a.b.c[3]->d is a OffsetDesignator whose base is 'a'
// each OffsetMember has 3 variants: 1. Member: .field 2. Indirect Member : ->field 3. Index: [expr]
impl WriteString for OffsetDesignator {
    fn write_string(&self) -> String {
        let mut res = self.base.node.name.clone();
        for member in &self.members {
            let s = match &member.node {
                OffsetMember::Member(ident) => {
                    format!(".{}", ident.node.name)
                }
                OffsetMember::IndirectMember(ident) => {
                    format!("->{}", ident.node.name)
                }
                OffsetMember::Index(expr) => {
                    format!("[{}]", expr.write_string())
                }
            };
            res.push_str(&s); // String impls DeRef<str> trait
        }
        res
    }
}
// refer to C11 7.16.1.4 $6
// variable argument for variadic function
// e.g. int printf(const char *fmt, ...);
// va_list ap; 一个指针，指向当前要读取的参数位置
// macro `va_start`: va_start(ap, last_named_param); last_named_param: 最后一个已知参数，ap会指向指向它后面的第一个可变参数
// va_arg(ap, type) 取出当前参数，并移动指针ap. e.g. int x = va_arg(ap, int);
// va_end(ap); 清理
// va_copy(dest, src) e.g. va_copy(ap2, ap); 复制当前“读取进度”
impl WriteString for VaArgExpression {
    fn write_string(&self) -> String {
        format!(
            "va_arg({}, {})",
            self.va_list.write_string(),
            self.type_name.write_string()
        )
    }
}

// 语句节点可以独立成为一行(多行)代码
impl WriteLine for Statement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            Statement::Labeled(stmt) => {
                write_indent(indent, write)?;
                writeln!(write, "{}: ", stmt.node.label.write_string())?;
                stmt.node.statement.write_line(indent + 1, write)
            }
            // {
            //     block_item1
            //     block_item2
            //     ...
            // }
            Statement::Compound(items) => {
                write_indent(indent, write)?;
                writeln!(write, "{{")?;
                for item in items {
                    // BlockItem是declaration/statement/static_assert
                    item.write_line(indent + 1, write)?;
                }
                write_indent(indent, write)?;
                writeln!(write, "}}")?;
                Ok(())
            }
            // 表达式本身也可以用作语句(如a+=3)，且空表达式产生空语句` ;`
            Statement::Expression(expr_opt) => {
                write_indent(indent, write)?;
                if let Some(expr) = expr_opt {
                    write!(write, "{}", expr.write_string())?;
                }
                writeln!(write, ";")?;
                Ok(())
            }
            Statement::If(stmt) => {
                write_indent(indent, write)?;
                writeln!(write, "if ({}) ", stmt.node.condition.write_string())?;

                stmt.node.then_statement.write_line(indent + 1, write)?;

                if let Some(else_stmt) = &stmt.node.else_statement {
                    write_indent(indent, write)?;
                    writeln!(write, "else")?;
                    else_stmt.write_line(indent + 1, write)?;
                }
                Ok(())
            }
            Statement::Switch(stmt) => {
                write_indent(indent, write)?;
                writeln!(write, "switch ({}) ", stmt.node.expression.write_string())?;

                stmt.node.statement.write_line(indent, write)?; // 通常是compound statement `{...}`
                Ok(())
            }
            Statement::While(stmt) => {
                write_indent(indent, write)?;
                writeln!(write, "while ({}) ", stmt.node.expression.write_string())?;

                stmt.node.statement.write_line(indent, write)?;
                Ok(())
            }
            Statement::DoWhile(stmt) => {
                write_indent(indent, write)?;
                writeln!(write, "do")?;

                stmt.node.statement.write_line(indent, write)?;

                write_indent(indent, write)?;
                writeln!(write, "while ({});", stmt.node.expression.write_string())?;
                Ok(())
            }
            Statement::For(stmt) => {
                write_indent(indent, write)?;
                let for_header = format!(
                    "for ({}; {}; {})",
                    stmt.node.initializer.write_string(),
                    stmt.node
                        .condition
                        .as_ref()
                        .map_or(String::new(), |e| e.write_string()),
                    stmt.node
                        .step
                        .as_ref()
                        .map_or(String::new(), |e| e.write_string()),
                );
                writeln!(write, "{}", for_header)?;
                stmt.node.statement.write_line(indent, write)?;
                Ok(())
            }
            Statement::Goto(id) => {
                write_indent(indent, write)?;
                writeln!(write, "goto {};", id.node.name)?;
                Ok(())
            }
            Statement::Continue => {
                write_indent(indent, write)?;
                writeln!(write, "continue;")?;
                Ok(())
            }
            Statement::Break => {
                write_indent(indent, write)?;
                writeln!(write, "break;")?;
                Ok(())
            }
            Statement::Return(expr_opt) => {
                write_indent(indent, write)?;
                writeln!(
                    write,
                    "return{};",
                    expr_opt
                        .as_ref()
                        .map_or(String::new(), |e| format!(" {}", e.write_string()))
                )?;
                Ok(())
            }
            Statement::Asm(asm_stmt) => {
                panic!("Statement::Asm")
            }
        }
    }
}

impl WriteString for Statement {
    fn write_string(&self) -> String {
        let mut buf = Vec::new();

        // 用 write_line 写进去（从 indent=0 开始）
        self.write_line(0, &mut buf).unwrap();

        // 转成 String
        let s = String::from_utf8(buf).unwrap();

        // 去掉末尾换行（很重要）
        s.trim_end().to_string()
    }
}

impl WriteString for Label {
    fn write_string(&self) -> String {
        match self {
            Label::Identifier(id) => id.node.name.clone(),
            Label::Case(expr) => {
                format!("case {}", expr.write_string())
            }
            Label::CaseRange(case_rng) => {
                format!(
                    "case {} ... {}",
                    case_rng.node.low.write_string(),
                    case_rng.node.high.write_string()
                )
            }
            Label::Default => "default".to_string(),
        }
    }
}

impl WriteLine for BlockItem {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            BlockItem::Declaration(decl) => decl.write_line(indent, write),
            BlockItem::Statement(stmt) => stmt.write_line(indent, write),
            BlockItem::StaticAssert(static_assert) => static_assert.write_line(indent, write),
        }
    }
}

impl WriteString for ForInitializer {
    fn write_string(&self) -> String {
        match self {
            ForInitializer::Empty => "".into(),
            ForInitializer::Expression(expr) => expr.write_string(),
            ForInitializer::Declaration(decl) => decl.write_string(),
            ForInitializer::StaticAssert(sa) => sa.write_string(),
        }
    }
}

impl WriteString for InitDeclarator {
    fn write_string(&self) -> String {
        match &self.initializer {
            Some(init) => {
                format!(
                    "{} = {}",
                    self.declarator.write_string(),
                    init.write_string()
                )
            }
            None => self.declarator.write_string(),
        }
    }
}

// C11 grammar 根据 expression 的类型，在编译期选择一个表达式, 所以expression不会被求值
// _Generic ( expression ,
//     type1 : expr1 ,
//     type2 : expr2 ,
//     default : exprN
// )
// 简化单行输出 _Generic(expr, type1: expr1, type2: expr2, default: expr3)
impl WriteString for GenericSelection {
    fn write_string(&self) -> String {
        let expr = self.expression.write_string();

        let assoc = self
            .associations
            .iter()
            .map(|a| a.write_string())
            .collect::<Vec<_>>()
            .join(", ");

        format!("_Generic({}, {})", expr, assoc)
    }
}
impl WriteString for GenericAssociation {
    fn write_string(&self) -> String {
        match self {
            GenericAssociation::Type(t) => {
                format!(
                    "{}: {}",
                    t.node.type_name.write_string(),
                    t.node.expression.write_string()
                )
            }
            GenericAssociation::Default(expr) => {
                format!("default: {}", expr.write_string())
            }
        }
    }
}
// hard
// pub struct Declarator {
//     pub kind: Node<DeclaratorKind>,   // 核心（identifier 或嵌套）
//     pub derived: Vec<Node<DerivedDeclarator>>, // 修饰链
// }
// pub enum DeclaratorKind {
//     Abstract, // 递归边界，表示无标识符(匿名) : (int *)
//     Identifier(Node<Identifier>), // 递归边界 如 a
//     Declarator(Box<Node<Declarator>>), 非边界
// }
// pub enum DerivedDeclarator {
//     Pointer(...)
//     Array(...)
//     Function(...)
// }
// 修饰链：给定一个当前类型`T`
// Pointer: 变成 pointer to T
// Array[n]: 变成 array[n] of T
// Function(params): 变成 function(params) returning T
// derived_declarator precedence: ()  >  []  >  *
// e.g. int *(*f[10])(int)
// 从外向内构造类型：
// int
// ↑
// *        → int *
// ↑
// (int)    → function(int) -> int *
// ↑
// *        → pointer to that function
// ↑
// [10]     → array of those pointers
// 从内向外
//Identifier: f
// → Array[10]
// → Pointer
// → Function(int)
// → Pointer
// → Base type: int
impl WriteString for Declarator {
    fn write_string(&self) -> String {
        // 递归处理DeclaratorKind,作为基类
        let mut s = match &self.kind.node {
            DeclaratorKind::Abstract => String::new(),
            DeclaratorKind::Declarator(decl) => {
                format!("({})", decl.write_string())
            }
            DeclaratorKind::Identifier(id) => id.node.name.clone(),
        };

        // 逐层应用derived
        // 数组 / 函数：从内到外（正序）贴在右边
        // 指针：从内到外（逆序）贴在左边
        let mut pointers = vec![];
        let mut suffixes = vec![];
        for d in &self.derived {
            match &d.node {
                DerivedDeclarator::Pointer(_) => pointers.push(d),
                _ => suffixes.push(d), // array / (KR)func
            }
        }

        // 处理suffixes
        for d in suffixes {
            match &d.node {
                DerivedDeclarator::Array(arr) => {
                    if s.starts_with("*") {
                        s = format!("({})", s);
                    }
                    let size = match &arr.node.size {
                        ArraySize::Unknown => "".to_string(),
                        ArraySize::VariableExpression(expr) => expr.write_string(),
                        ArraySize::StaticExpression(expr) => expr.write_string(),
                        ArraySize::VariableUnknown => "*".to_string(),
                    };
                    s = format!("{}[{}]", s, size);
                }
                DerivedDeclarator::Function(func_decl) => {
                    // 如果当前 s 以 '*' 开头，说明是函数指针，必须加括号：(*s)()
                    if s.starts_with("*") {
                        s = format!("({})", s);
                    }
                    s = format!("{}({})", s, func_decl.write_string());
                }
                DerivedDeclarator::KRFunction(ids) => {
                    // guarantee parameter list is empty
                    if s.starts_with('*') {
                        s = format!("({})", s);
                    }
                    let params = ids
                        .iter()
                        .map(|id| id.node.name.clone())
                        .collect::<Vec<_>>()
                        .join(", ");
                    s = format!("{}({})", s, params);
                }
                _ => panic!("DerivedDeclarator::Block"),
            }
        }
        for d in pointers.into_iter().rev() {
            match &d.node {
                DerivedDeclarator::Pointer(quals) => {
                    let mut ptr = String::from("*");
                    // qualifiers
                    for q in quals {
                        ptr.push(' ');
                        ptr.push_str(&q.write_string());
                    }

                    if s.is_empty() {
                        s = ptr;
                    } else if ptr.contains(' ') {
                        // 有限定符时，如 * const，加空格
                        s = format!("{} {}", ptr, s);
                    } else {
                        // 无限定符指针，如*p
                        s = format!("{}{}", ptr, s)
                    }
                }
                _ => panic!("pointers should have DerivedDeclarator::Pointer type"),
            }
        }

        s
    }
}

impl WriteString for PointerQualifier {
    fn write_string(&self) -> String {
        match self {
            PointerQualifier::TypeQualifier(tq) => tq.write_string(),
            PointerQualifier::Extension(_) => panic!("PointerQualifier::Extension"),
        }
    }
}

impl WriteString for FunctionDeclarator {
    fn write_string(&self) -> String {
        let params = self
            .parameters
            .iter()
            .map(|p| p.write_string())
            .collect::<Vec<_>>()
            .join(", ");
        params
    }
}

impl WriteString for ParameterDeclaration {
    fn write_string(&self) -> String {
        let spec = self
            .specifiers
            .iter()
            .map(|s| s.write_string())
            .collect::<Vec<_>>()
            .join(" ");
        let decl = self
            .declarator
            .as_ref()
            .map(|d| d.write_string())
            .unwrap_or_default();
        if decl.is_empty() {
            spec
        } else {
            format!("{} {}", spec, decl)
        }
    }
}

// return_type declarator
// declarations (K&R 可选)
// body
// e.g.
// int foo(a, b)
// int a;
// int b;
// {
//     return a + b;
// }
impl WriteLine for FunctionDefinition {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        let specs = self
            .specifiers
            .iter()
            .map(|s| s.write_string())
            .collect::<Vec<_>>()
            .join(" ");

        let decl = self.declarator.write_string();

        if specs.is_empty() {
            writeln!(write, "{}", decl)?;
        } else {
            writeln!(write, "{} {}", specs, decl)?;
        }
        // K & R declarations (如果有)
        for d in &self.declarations {
            d.write_line(indent + 1, write)?;
        }

        self.statement.write_line(indent, write)?;

        Ok(())
    }
}
