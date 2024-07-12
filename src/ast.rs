// TODO debug and display impls are i can't even...

use std::{
    fmt::{self},
    rc::Rc,
};

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Op {
    Assign,
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
    Call,
    Index,
    Ref,
    Deref,
    Dot,
    ScopeRes,
    Cast,
}

impl std::fmt::Debug for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op::Assign => write!(f, "assign"),
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
            Op::Call => write!(f, "call"),
            Op::Index => write!(f, "index"),
            Op::Ref => write!(f, "ref"),
            Op::Deref => write!(f, "deref"),
            Op::Dot => write!(f, "dot"),
            Op::ScopeRes => write!(f, "scoperes"),
            Op::Cast => write!(f, "cast"),
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
            Op::Neg | Op::Not | Op::Ref | Op::Deref | Op::Dot | Op::ScopeRes | Op::Index => 6,
            Op::Call => 7,
            _ => 0,
        }
    }
}
pub type NodeRef = Rc<Node>;

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Arg {
    pub ident: Rc<str>,
    pub ty: Rc<str>,
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct StructField {
    pub ident: Rc<str>,
    pub ty: Rc<str>,
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
        ty: Rc<str>,
        lhs: NodeRef,
        rhs: Option<NodeRef>,
    },
    // TODO could be merged with let
    Const {
        ty: Rc<str>,
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
                        ty,
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
                        ty,
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
                        .map(|arg| format!("{}: {}", arg.ident, arg.ty))
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
            }
            .as_str();

            s
        }

        f.write_str((fmt_with_indent(self, 0, false) + "\n").as_str())
    }
}
