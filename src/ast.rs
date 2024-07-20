// TODO debug and display impls are i can't even...

use std::{
    fmt::{self},
    rc::Rc,
};

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
            Op::Neg
            | Op::Not
            | Op::Ref
            | Op::Deref
            | Op::Dot
            | Op::ScopeRes
            | Op::Index
            | Op::StructLiteral => 6,
            Op::Call => 7,
            _ => 0,
        }
    }
}
pub type NodeRef = Rc<Node>;

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum Arg {
    SelfVal,
    SelfRef,
    Pair { ident: Rc<str>, ty: Rc<str> },
}

impl Arg {
    pub fn ident(&self) -> Rc<str> {
        match self {
            Arg::SelfVal => "self".into(),
            Arg::SelfRef => "self".into(),
            Arg::Pair { ident, .. } => ident.clone(),
        }
    }

    pub fn ty(&self) -> Rc<str> {
        match self {
            Arg::SelfVal => "Self".into(),
            Arg::SelfRef => "&Self".into(),
            Arg::Pair { ty, .. } => ty.clone(),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct StructField {
    pub ident: Rc<str>,
    pub ty: Rc<str>,
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

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Node {
    NullPtr,
    Ident {
        name: Rc<str>,
    },
    Int {
        value: i64,
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
        ty: Option<Rc<str>>,
        lhs: NodeRef,
        rhs: Option<NodeRef>,
    },
    // TODO could be merged with let
    Const {
        ty: Option<Rc<str>>,
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
        args: Rc<[Arg]>,
        ret_ty: Rc<str>,
        is_extern: bool,
        linkage: Option<Rc<str>>,
        body: Option<NodeRef>,
    },
    Call {
        ident: Rc<str>,
        args: Rc<[NodeRef]>,
    },
    Struct {
        ident: Rc<str>,
        fields: Rc<[StructField]>,
        generics: Rc<[Rc<str>]>,
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
        ident: Rc<str>,
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

            s += match node {
                Node::NullPtr => "nullptr".to_string(),
                Node::Ident { name } => format!("ident {}", name),
                Node::Int { value } => format!("{}", value),
                Node::Bool { value } => format!("{}", value),
                Node::Str { value } => format!("{:?}", value),
                Node::Char { value } => {
                    format!("'{}'", unsafe { char::from_u32_unchecked(**value as u32) })
                }
                Node::UnOp { op, rhs } => {
                    format!("{:?}{}", op, fmt_with_indent(rhs, indent_level + 1, true))
                }
                Node::BinOp { op, lhs, rhs } => {
                    format!(
                        "{:?}{}{}",
                        op,
                        fmt_with_indent(lhs, indent_level + 1, true),
                        fmt_with_indent(rhs, indent_level + 1, true)
                    )
                }
                Node::Let { ty, lhs, rhs } => {
                    format!(
                        "let {}{}{}",
                        match ty {
                            Some(ty) => ty,
                            None => "",
                        },
                        fmt_with_indent(lhs, indent_level + 1, true),
                        if rhs.is_some() {
                            fmt_with_indent(rhs.as_ref().unwrap(), indent_level + 1, true)
                        } else {
                            "".to_string()
                        }
                    )
                }
                Node::Const { ty, lhs, rhs } => {
                    format!(
                        "const {}{}{}",
                        match ty {
                            Some(ty) => ty,
                            None => "",
                        },
                        fmt_with_indent(lhs, indent_level + 1, true),
                        if rhs.is_some() {
                            fmt_with_indent(rhs.as_ref().unwrap(), indent_level + 1, true)
                        } else {
                            "".to_string()
                        }
                    )
                }
                Node::Return { expr: stmt } => match stmt {
                    Some(stmt) => {
                        format!("return{}", fmt_with_indent(stmt, indent_level + 1, true))
                    }
                    None => "return".to_string(),
                },
                Node::If {
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
                Node::While { condition, body } => {
                    format!(
                        "while{}{}",
                        fmt_with_indent(condition, indent_level + 1, true),
                        fmt_with_indent(body, indent_level + 1, true)
                    )
                }
                Node::Block { statements } => {
                    let mut b = "block".to_string();
                    for stmt in statements.iter() {
                        b += fmt_with_indent(stmt, indent_level + 1, true).as_str();
                    }
                    b
                }
                Node::Fn {
                    ident,
                    args,
                    ret_ty,
                    body,
                    is_extern,
                    linkage,
                } => {
                    let args_str = args
                        .iter()
                        .map(|arg| format!("{}: {}", arg.ident(), arg.ty()))
                        .collect::<Vec<String>>()
                        .join(", ");

                    if *is_extern {
                        format!(
                            "extern {:?} fn {}({}) -> {}{}",
                            linkage.clone().unwrap(),
                            ident,
                            args_str,
                            ret_ty,
                            if let Some(body) = body {
                                fmt_with_indent(body, indent_level + 1, true)
                            } else {
                                "".to_string()
                            }
                        )
                    } else {
                        format!(
                            "fn {}({}) -> {}{}",
                            ident,
                            args_str,
                            ret_ty,
                            if let Some(body) = body {
                                fmt_with_indent(body, indent_level + 1, true)
                            } else {
                                "".to_string()
                            }
                        )
                    }
                }
                Node::Call { ident, args } => {
                    let mut c = format!("call {}", ident);
                    for arg in args.iter() {
                        c += fmt_with_indent(arg, indent_level + 1, true).as_str();
                    }
                    c
                }
                Node::Struct {
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
                        acc += &field.ty;
                        acc
                    });

                    let generics_str = if generics.len() > 0 {
                        format!("<{}>", generics.join(","))
                    } else {
                        "".to_string()
                    };

                    format!("struct {}{}{}", ident, generics_str, fields_str)
                }
                Node::Impl {
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
                Node::Array { elems } => {
                    let elems_str = elems.iter().fold(String::new(), |mut acc, method| {
                        acc += "\n";
                        acc += fmt_with_indent(method, indent_level + 1, false).as_str();
                        acc
                    });

                    format!("array{}", elems_str)
                }
                Node::StructLiteral { ident, fields } => {
                    let fields_str = fields.iter().fold(String::new(), |mut acc, field| {
                        acc += "\n";
                        acc += &"    ".repeat(indent_level + 1);
                        acc += &field.ident;
                        acc += "\n";
                        acc += &fmt_with_indent(&field.val, indent_level + 2, false);
                        acc
                    });
                    format!("struct_literal {}{}", ident, fields_str)
                }
                Node::ExternBlock { linkage, block } => {
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
                Node::Match {
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
            }
            .as_str();

            s
        }

        f.write_str((fmt_with_indent(self, 0, false) + "\n").as_str())
    }
}
