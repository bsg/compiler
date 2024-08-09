// TODO debug and display impls are i can't even...

use std::{
    fmt::{self},
    rc::Rc,
};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Span {
    pub start_line: usize,
    pub start_col: usize,
    pub end_line: usize,
    pub end_col: usize,
}

impl Span {
    // TODO rename
    pub fn merge(&self, other: &Span) -> Span {
        // TODO
        // assert!(self.start_line <= other.start_line);
        // if self.start_line == other.start_line {
        //     assert!(self.start_col <= other.start_col);
        // }

        Span {
            start_line: self.start_line,
            start_col: self.start_col,
            end_line: other.end_line,
            end_col: other.end_col,
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "Line: {}, Col: {}",
            self.start_line, self.start_col
        ))
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Op {
    Assign(Option<Rc<Op>>), // TODO this is kinda stupid and inefficient, maybe make separate variants for each case
    Eq,
    NotEq,
    Lt,
    Gt,
    Le,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Neg,
    Not,
    And,
    Or,
    Xor,
    BitwiseOr,
    BitwiseAnd,
    BitwiseXor,
    Call,
    Index,
    Ref,
    Deref,
    Dot,
    ScopeRes,
    Cast,
    StructLiteral,
    Turbofish,
}

impl std::fmt::Debug for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op::Assign(op) => {
                if let Some(op) = op {
                    write!(f, "{:?} assign", op)
                } else {
                    write!(f, "assign")
                }
            }
            Op::Eq => write!(f, "eq"),
            Op::NotEq => write!(f, "neq"),
            Op::Lt => write!(f, "lt"),
            Op::Gt => write!(f, "gt"),
            Op::Le => write!(f, "le"),
            Op::Ge => write!(f, "ge"),
            Op::Add => write!(f, "add"),
            Op::Sub => write!(f, "sub"),
            Op::Mul => write!(f, "mul"),
            Op::Div => write!(f, "div"),
            Op::Mod => write!(f, "mod"),
            Op::Neg => write!(f, "neg"),
            Op::Not => write!(f, "not"),
            Op::And => write!(f, "and"),
            Op::Or => write!(f, "or"),
            Op::Xor => write!(f, "xor"),
            Op::BitwiseAnd => write!(f, "bitwise_and"),
            Op::BitwiseOr => write!(f, "bitwise_or"),
            Op::BitwiseXor => write!(f, "bitwise_xor"),
            Op::Call => write!(f, "call"),
            Op::Index => write!(f, "index"),
            Op::Ref => write!(f, "ref"),
            Op::Deref => write!(f, "deref"),
            Op::Dot => write!(f, "dot"),
            Op::ScopeRes => write!(f, "scoperes"),
            Op::Cast => write!(f, "cast"),
            Op::StructLiteral => write!(f, "struct_literal"),
            Op::Turbofish => write!(f, "turbofish"),
        }
    }
}

impl Op {
    pub fn precedence(&self) -> i32 {
        match self {
            Op::Eq | Op::NotEq => 1,
            Op::Lt | Op::Gt | Op::Le | Op::Ge => 2,
            Op::Add | Op::Sub => 3,
            Op::Mul | Op::Div | Op::Mod => 4,
            Op::Cast => 5,
            Op::Neg | Op::Not | Op::Deref | Op::Ref | Op::Dot | Op::ScopeRes | Op::Index => 6,
            Op::Call | Op::StructLiteral => 7,
            Op::Turbofish => 8,
            _ => 0,
        }
    }
}
pub type NodeRef = Rc<Node>;

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum FnParam {
    SelfByVal,
    SelfByRef,
    Pair { ident: Rc<str>, ty: Rc<TypeAnnotation> },
}

impl FnParam {
    pub fn ident(&self) -> Rc<str> {
        match self {
            FnParam::SelfByVal => "self".into(),
            FnParam::SelfByRef => "self".into(),
            FnParam::Pair { ident, .. } => ident.clone(),
        }
    }

    pub fn ty(&self) -> Rc<TypeAnnotation> {
        match self {
            FnParam::SelfByVal => TypeAnnotation::SelfByVal.into(),
            FnParam::SelfByRef => TypeAnnotation::SelfByRef.into(),
            FnParam::Pair { ty, .. } => ty.clone(),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct StructField {
    pub ident: Rc<str>,
    pub ty: Rc<TypeAnnotation>,
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct StructLiteralField {
    pub ident: Rc<str>,
    pub val: NodeRef,
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct MatchArm {
    pub pattern: Rc<[NodeRef]>,
    pub stmt: NodeRef, // TODO rename to expr and treat this as such when we have block exprs
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum TypeAnnotation {
    Simple {
        // TODO rename
        ident: Rc<str>,
        generics: Rc<[Rc<TypeAnnotation>]>,
    },
    Fn {
        param_tys: Rc<[Rc<TypeAnnotation>]>,
        ret_ty: Rc<TypeAnnotation>,
    },
    Ptr {
        pointee_ty: Rc<TypeAnnotation>,
    },
    Ref {
        referent_ty: Rc<TypeAnnotation>,
    },
    Array {
        elem_ty: Rc<TypeAnnotation>,
    },
    Slice {
        elem_ty: Rc<TypeAnnotation>,
        len: usize,
    },
    SelfByVal,
    SelfByRef,
}

impl TypeAnnotation {
    pub fn is_generic(&self) -> bool {
        match self {
            TypeAnnotation::Simple { generics, .. } => generics.len() > 0,
            TypeAnnotation::Ptr { pointee_ty } => pointee_ty.is_generic(),
            TypeAnnotation::Ref { referent_ty } => referent_ty.is_generic(),
            _ => false, // TODO
        }
    }
}

impl fmt::Display for TypeAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeAnnotation::Simple { ident, generics } => f.write_fmt(format_args!(
                "{}{}",
                ident,
                if !generics.is_empty() {
                    format!(
                        "<{}>",
                        generics
                            .iter()
                            .map(|g| g.to_string())
                            .collect::<Vec<String>>()
                            .join(",")
                    )
                } else {
                    String::new()
                }
            )),
            TypeAnnotation::Fn {
                param_tys: params,
                ret_ty,
            } => f.write_fmt(format_args!(
                "fn({}) -> {}",
                params
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<String>>()
                    .join(","),
                ret_ty
            )),
            TypeAnnotation::Ptr { pointee_ty } => f.write_fmt(format_args!("*{}", pointee_ty)),
            TypeAnnotation::Ref { referent_ty } => f.write_fmt(format_args!("&{}", referent_ty)),
            TypeAnnotation::Array { elem_ty } => f.write_fmt(format_args!("[{}]", elem_ty)),
            TypeAnnotation::Slice { elem_ty, len } => f.write_fmt(format_args!("[{}; {}]", elem_ty, len)),
            TypeAnnotation::SelfByVal => f.write_str("Self"),
            TypeAnnotation::SelfByRef => f.write_str("&Self"),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct PathSegment {
    pub ident: Rc<str>,
    pub generics: Rc<[Rc<TypeAnnotation>]>,
}

impl fmt::Display for PathSegment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let generics = if !self.generics.is_empty() {
            format!(
                "<{}>",
                self.generics
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<String>>()
                    .join(",")
            )
        } else {
            String::new()
        };

        f.write_fmt(format_args!("{}{}", self.ident, generics))
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum NodeKind {
    NullPtr,
    Ident {
        name: Rc<str>,
    },
    Path {
        // TODO full path
        segment: PathSegment,
    },
    Int {
        value: u64,
    },
    Bool {
        value: bool,
    },
    Str {
        value: Rc<str>,
    },
    Char {
        value: Rc<u8>,
    },
    UnOp {
        op: Op,
        rhs: NodeRef,
    },
    BinOp {
        op: Op,
        lhs: NodeRef,
        rhs: NodeRef,
    },
    Let {
        ty: Rc<TypeAnnotation>,
        lhs: NodeRef,
        rhs: Option<NodeRef>,
    },
    // TODO could be merged with let as 'binding'
    Const {
        ty: Rc<TypeAnnotation>,
        lhs: NodeRef,
        rhs: Option<NodeRef>,
    },
    Return {
        expr: Option<NodeRef>,
    },
    If {
        condition: NodeRef,
        then_block: NodeRef,
        else_block: Option<NodeRef>,
    },
    While {
        condition: NodeRef,
        body: NodeRef,
    },
    Block {
        statements: Rc<[NodeRef]>,
    },
    Fn {
        ident: Rc<str>,
        params: Rc<[FnParam]>,
        ret_ty: Rc<TypeAnnotation>,
        generics: Rc<[Rc<TypeAnnotation>]>,
        is_extern: bool,
        linkage: Option<Rc<str>>,
        body: Option<NodeRef>,
    },
    Call {
        path: PathSegment, // TODO use Path
        args: Rc<[NodeRef]>,
    },
    Struct {
        ident: Rc<str>,
        fields: Rc<[StructField]>,
        generics: Rc<[Rc<TypeAnnotation>]>, // TODO BoundedTy or something
        attributes: Option<Rc<[Rc<str>]>>,
    },
    Impl {
        ident: Rc<str>,
        methods: Rc<[NodeRef]>,
        impl_generics: Rc<[Rc<str>]>,
        type_generics: Rc<[Rc<str>]>,
    },
    Array {
        elems: Rc<[NodeRef]>,
    },
    StructLiteral {
        path: PathSegment,
        fields: Rc<[StructLiteralField]>,
    },
    ExternBlock {
        linkage: Option<Rc<str>>,
        block: NodeRef,
    },
    Match {
        scrutinee: NodeRef,
        arms: Rc<[MatchArm]>,
        num_cases: usize,
    },
    Break,
    Continue,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Node {
    pub kind: NodeKind,
    pub span: Span,
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO append to a single string instance instead of creating so many new strings
        // or find a way to recurse with &mut f
        fn fmt_with_indent(node: &Node, indent_level: usize, on_new_line: bool) -> String {
            let mut s = String::new();
            if on_new_line {
                s += "\n";
            }
            s += "    ".repeat(indent_level).as_str();

            s += match &node.kind {
                NodeKind::NullPtr => "nullptr".to_string(),
                NodeKind::Ident { name } => format!("ident {}", name),
                NodeKind::Path { segment } => format!("{}", segment),
                NodeKind::Int { value } => format!("{}", value),
                NodeKind::Bool { value } => format!("{}", value),
                NodeKind::Str { value } => format!("{:?}", value),
                NodeKind::Char { value } => {
                    format!("'{}'", unsafe { char::from_u32_unchecked(**value as u32) })
                }
                NodeKind::UnOp { op, rhs } => {
                    format!("{:?}{}", op, fmt_with_indent(rhs, indent_level + 1, true))
                }
                NodeKind::BinOp { op, lhs, rhs } => {
                    format!(
                        "{:?}{}{}",
                        op,
                        fmt_with_indent(lhs, indent_level + 1, true),
                        fmt_with_indent(rhs, indent_level + 1, true)
                    )
                }
                NodeKind::Let { ty, lhs, rhs } => {
                    format!(
                        "let {}{}{}",
                        ty,
                        fmt_with_indent(lhs, indent_level + 1, true),
                        if rhs.is_some() {
                            fmt_with_indent(rhs.as_ref().unwrap(), indent_level + 1, true)
                        } else {
                            "".to_string()
                        }
                    )
                }
                NodeKind::Const { ty, lhs, rhs } => {
                    format!(
                        "const {}{}{}",
                        ty,
                        fmt_with_indent(lhs, indent_level + 1, true),
                        if rhs.is_some() {
                            fmt_with_indent(rhs.as_ref().unwrap(), indent_level + 1, true)
                        } else {
                            "".to_string()
                        }
                    )
                }
                NodeKind::Return { expr } => match expr {
                    Some(expr) => {
                        format!("return{}", fmt_with_indent(expr, indent_level + 1, true))
                    }
                    None => "return".to_string(),
                },
                NodeKind::If {
                    condition,
                    then_block,
                    else_block,
                } => {
                    if let Some(else_block) = else_block {
                        format!(
                            "if{}\n{}then{}\n{}else{}",
                            fmt_with_indent(condition, indent_level + 1, true),
                            "    ".repeat(indent_level),
                            fmt_with_indent(then_block, indent_level + 1, true),
                            "    ".repeat(indent_level),
                            fmt_with_indent(else_block, indent_level + 1, true)
                        )
                    } else {
                        format!(
                            "if{}\n{}then{}",
                            fmt_with_indent(condition, indent_level + 1, true),
                            "    ".repeat(indent_level),
                            fmt_with_indent(then_block, indent_level + 1, true),
                        )
                    }
                }
                NodeKind::While { condition, body } => {
                    format!(
                        "while{}{}",
                        fmt_with_indent(condition, indent_level + 1, true),
                        fmt_with_indent(body, indent_level + 1, true)
                    )
                }
                NodeKind::Block { statements } => {
                    let mut b = "block".to_string();
                    for stmt in statements.iter() {
                        b += fmt_with_indent(stmt, indent_level + 1, true).as_str();
                    }
                    b
                }
                NodeKind::Fn {
                    ident,
                    params,
                    ret_ty,
                    generics,
                    body,
                    is_extern,
                    linkage,
                } => {
                    let params_str = params
                        .iter()
                        .map(|param| format!("{}: {}", param.ident(), param.ty()))
                        .collect::<Vec<String>>()
                        .join(", ");

                    // TODO this is duplicated, maybe have a struct holding generics with a .to_string() method
                    let generics_str = if generics.len() > 0 {
                        format!(
                            "<{}>",
                            generics
                                .iter()
                                .map(|g| g.to_string())
                                .collect::<Vec<String>>()
                                .join(",")
                        )
                    } else {
                        "".to_string()
                    };

                    if *is_extern {
                        format!(
                            "extern {:?} fn {}{}({}) -> {}{}",
                            linkage.clone().unwrap(),
                            ident,
                            generics_str,
                            params_str,
                            ret_ty,
                            if let Some(body) = body {
                                fmt_with_indent(body, indent_level + 1, true)
                            } else {
                                "".to_string()
                            }
                        )
                    } else {
                        format!(
                            "fn {}{}({}) -> {}{}",
                            ident,
                            generics_str,
                            params_str,
                            ret_ty,
                            if let Some(body) = body {
                                fmt_with_indent(body, indent_level + 1, true)
                            } else {
                                "".to_string()
                            }
                        )
                    }
                }
                NodeKind::Call { path, args } => {
                    let mut c = format!("call {}", path);
                    for arg in args.iter() {
                        c += fmt_with_indent(arg, indent_level + 1, true).as_str();
                    }
                    c
                }
                NodeKind::Struct {
                    ident,
                    fields,
                    generics,
                    ..
                } => {
                    let fields_str = fields.iter().fold(String::new(), |mut acc, field| {
                        acc += "\n";
                        acc += "    ";
                        acc += &field.ident;
                        acc += " ";
                        acc += &field.ty.to_string();
                        acc
                    });

                    let generics_str = if generics.len() > 0 {
                        format!(
                            "<{}>",
                            generics
                                .iter()
                                .map(|t| t.to_string())
                                .collect::<Vec<String>>()
                                .join(",")
                        )
                    } else {
                        "".to_string()
                    };

                    format!("struct {}{}{}", ident, generics_str, fields_str)
                }
                NodeKind::Impl {
                    ident,
                    methods,
                    impl_generics,
                    type_generics,
                } => {
                    let methods_str = methods.iter().fold(String::new(), |mut acc, method| {
                        acc += "\n";
                        acc += fmt_with_indent(method, indent_level + 1, false).as_str();
                        acc
                    });

                    let impl_generics_str = if impl_generics.len() > 0 {
                        format!("<{}>", impl_generics.join(","))
                    } else {
                        "".to_string()
                    };

                    let type_generics_str = if type_generics.len() > 0 {
                        format!("<{}>", type_generics.join(","))
                    } else {
                        "".to_string()
                    };

                    format!(
                        "impl{} {}{}{}",
                        impl_generics_str, ident, type_generics_str, methods_str
                    )
                }
                NodeKind::Array { elems } => {
                    let elems_str = elems.iter().fold(String::new(), |mut acc, method| {
                        acc += "\n";
                        acc += fmt_with_indent(method, indent_level + 1, false).as_str();
                        acc
                    });

                    format!("array{}", elems_str)
                }
                NodeKind::StructLiteral { path, fields } => {
                    let fields_str = fields.iter().fold(String::new(), |mut acc, field| {
                        acc += "\n";
                        acc += &"    ".repeat(indent_level + 1);
                        acc += &field.ident;
                        acc += "\n";
                        acc += &fmt_with_indent(&field.val, indent_level + 2, false);
                        acc
                    });
                    format!("struct_literal {}{}", path, fields_str)
                }
                NodeKind::ExternBlock { linkage, block } => {
                    if let Some(linkage) = linkage {
                        format!(
                            "extern \"{}\"{}",
                            linkage,
                            fmt_with_indent(block, indent_level + 1, true)
                        )
                    } else {
                        format!("extern {}", fmt_with_indent(block, indent_level + 1, true))
                    }
                }
                NodeKind::Match {
                    scrutinee, arms, ..
                } => {
                    // FIXME awful
                    let arms_formatted = arms
                        .iter()
                        .map(|arm| {
                            let pattern_formatted = arm
                                .pattern
                                .iter()
                                .map(|pattern| {
                                    format!(
                                        "\n{}case {}",
                                        "    ".repeat(indent_level + 1),
                                        fmt_with_indent(pattern, 0, false)
                                    )
                                })
                                .collect::<Vec<String>>()
                                .join("");
                            format!(
                                "{}{}",
                                pattern_formatted,
                                fmt_with_indent(&arm.stmt, indent_level + 2, true)
                            )
                        })
                        .collect::<Vec<String>>()
                        .join("");
                    format!(
                        "match {}{}",
                        fmt_with_indent(scrutinee, 0, false),
                        arms_formatted
                    )
                }
                NodeKind::Break => "break".to_owned(),
                NodeKind::Continue => "continue".to_owned(),
            }
            .as_str();

            s
        }

        f.write_str((fmt_with_indent(self, 0, false) + "\n").as_str())
    }
}
