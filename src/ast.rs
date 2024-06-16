// TODO debug and display impls are i can't even...

use std::{
    fmt::{self},
    rc::Rc,
};

#[derive(Debug, Clone, PartialEq, Eq)]
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
    Colon,
}

impl Op {
    pub fn precedence(&self) -> i32 {
        match self {
            Op::Eq | Op::NotEq => 1,
            Op::Lt | Op::Gt | Op::Le | Op::Ge => 2,
            Op::Add | Op::Sub => 3,
            Op::Mul | Op::Div | Op::Mod => 4,
            _ => 0,
        }
    }
}
pub type NodeRef = Rc<Node>;

#[derive(Clone, PartialEq)]
pub struct BlockStmt {
    pub statements: Rc<[NodeRef]>,
}

#[derive(Clone, PartialEq)]
pub struct IfStmt {
    pub condition: NodeRef,
}

#[derive(PartialEq, Clone)]
pub struct FnStmt {
    pub ident: Rc<str>,
    pub args: Rc<[Rc<str>]>,
    pub ret_ty: Rc<str>,
}

#[derive(Clone, PartialEq)]
pub struct CallStmt {
    pub ident: Rc<str>,
    pub args: Rc<[NodeRef]>,
}

#[derive(Clone, PartialEq)]
pub struct IndexStmt {
    pub ident: Rc<str>,
    pub index: NodeRef,
}

#[derive(Clone, PartialEq)]
pub struct PairStmt {
    pub key: NodeRef,
    pub value: NodeRef,
}

#[derive(Clone, PartialEq)]
pub struct LetStmt {
    pub ty: Rc<str>,
} 

#[derive(Clone, PartialEq)]
pub enum NodeKind {
    Ident(Rc<str>),
    Int(i64),
    Bool(bool),
    Str(Rc<str>),
    InfixOp(Op),
    PrefixOp(Op),
    Let(LetStmt),
    Return,
    If(IfStmt),
    Block(BlockStmt),
    Fn(FnStmt),
    Call(CallStmt),
    Array(Vec<Rc<Node>>),
    Index(IndexStmt),
    Pair(PairStmt),
}

#[derive(Clone, PartialEq)]
pub struct Node {
    pub kind: NodeKind,
    pub left: Option<NodeRef>,
    pub right: Option<NodeRef>,
}

impl fmt::Debug for NodeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(arg0) => write!(f, "Ident({})", arg0),
            Self::Int(arg0) => f.debug_tuple("Int").field(arg0).finish(),
            Self::Bool(arg0) => f.debug_tuple("Bool").field(arg0).finish(),
            Self::Str(arg0) => f.debug_tuple("Str").field(arg0).finish(),
            Self::InfixOp(arg0) => f.debug_tuple("Op").field(arg0).finish(),
            Self::PrefixOp(arg0) => f.debug_tuple("Op").field(arg0).finish(),
            Self::Let(l) => write!(f, "Let {}", l.ty),
            Self::Return => write!(f, "Return"),
            Self::If(arg0) => f.write_fmt(format_args!("If\n{:?}", arg0)),
            Self::Block(arg0) => f.debug_tuple("Block").field(arg0).finish(),
            Self::Fn(arg0) => write!(f, "Fn {:?}({:?}) -> {}", arg0.ident, arg0, arg0.ret_ty),
            Self::Call(arg0) => write!(f, "Call(\n{:?})", arg0),
            Self::Array(arg0) => write!(f, "Array{:?}", arg0),
            Self::Index(arg0) => write!(f, "{:?}", arg0),
            Self::Pair(pair) => write!(f, "Pair({:?}, {:?})", pair.key, pair.value),
        }
    }
}

impl fmt::Display for FnStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.args.join(", ").as_str())
    }
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn fmt_with_indent(node: &Node, f: &mut fmt::Formatter, indent: usize) -> fmt::Result {
            (0..indent).for_each(|_| _ = f.write_str("-"));

            f.write_fmt(format_args!(
                "{}",
                match &node.kind {
                    NodeKind::Ident(s) => format!("Ident({})\n", s),
                    NodeKind::Int(i) => format!("Int({})\n", i),
                    NodeKind::Bool(b) => format!("Bool({})\n", b),
                    NodeKind::Str(s) => format!("Str({})\n", s),
                    NodeKind::InfixOp(op) => format!("{:?}\n", op),
                    NodeKind::PrefixOp(op) => format!("{:?}\n", op),
                    NodeKind::Let(l) => format!("Let {}\n", l.ty),
                    NodeKind::Return => "Return\n".to_string(),
                    NodeKind::If(_) => "If\n".to_string(),
                    NodeKind::Fn(f) => format!("Fn {}({}) -> {}\n", f.ident, f, f.ret_ty),
                    NodeKind::Block(_) => "Block\n".to_string(),
                    NodeKind::Call(call) => format!("Call {}\n", call.ident),
                    NodeKind::Array(a) => format!("Array{:?}\n", a),
                    NodeKind::Index(idx) => format!("{:?}\n", idx),
                    NodeKind::Pair(pair) => format!("Pair({:?}, {:?})\n", pair.key, pair.value),
                }
            ))?;
            match &node.kind {
                NodeKind::Block(block) => {
                    for stmt in block.statements.iter() {
                        fmt_with_indent(stmt, f, indent + 1)?
                    }
                }
                NodeKind::If(c) => {
                    fmt_with_indent(&c.condition, f, indent + 1)?;

                    if let Some(node) = &node.left {
                        f.write_fmt(format_args!("{}Then\n", "-".repeat(indent)))?;
                        fmt_with_indent(node, f, indent + 1)?;
                    }

                    if let Some(node) = &node.right {
                        f.write_fmt(format_args!("{}Else\n", "-".repeat(indent)))?;
                        fmt_with_indent(node, f, indent + 1)?;
                    }

                    return Ok(());
                }

                NodeKind::Call(c) => {
                    for arg in c.args.iter() {
                        fmt_with_indent(arg, f, indent + 1)?;
                    }
                }
                _ => (),
            }

            if let Some(lhs) = node.left.as_ref() {
                fmt_with_indent(lhs, f, indent + 1)?;
            }

            if let Some(rhs) = node.right.as_ref() {
                fmt_with_indent(rhs, f, indent + 1)?;
            }

            Ok(())
        }
        fmt_with_indent(self, f, 0)?;
        Ok(())
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn fmt_with_indent(node: &Node, f: &mut fmt::Formatter, indent: usize) -> fmt::Result {
            (0..indent).for_each(|_| _ = f.write_str("-"));
            f.write_fmt(format_args!("{:?}\n", node.kind))?;

            if let Some(lhs) = node.left.as_ref() {
                fmt_with_indent(lhs, f, indent + 1)?;
            }

            if let Some(rhs) = node.right.as_ref() {
                fmt_with_indent(rhs, f, indent + 1)?
            }

            Ok(())
        }
        fmt_with_indent(self, f, 0)?;
        Ok(())
    }
}

impl fmt::Debug for BlockStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for stmt in self.statements.iter() {
            f.write_fmt(format_args!("{:?}", stmt))?;
        }
        Ok(())
    }
}

impl fmt::Debug for IfStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?})", self.condition))
    }
}

impl fmt::Debug for FnStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?})", self.args))
    }
}

impl fmt::Debug for CallStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?})", self.args))
    }
}

impl fmt::Debug for IndexStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.ident, self.index))
    }
}
