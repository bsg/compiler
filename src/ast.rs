// TODO debug and display impls are i can't even...

use std::{
    fmt::{self},
    rc::Rc,
};

#[derive(Clone, PartialEq, Eq)]
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

impl std::fmt::Debug for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Assign => write!(f, "assign"),
            Self::Eq => write!(f, "eq"),
            Self::NotEq => write!(f, "neq"),
            Self::Lt => write!(f, "lt"),
            Self::Gt => write!(f, "gt"),
            Self::Le => write!(f, "le"),
            Self::Ge => write!(f, "ge"),
            Self::Add => write!(f, "add"),
            Self::Sub => write!(f, "sub"),
            Self::Mul => write!(f, "mul"),
            Self::Div => write!(f, "div"),
            Self::Mod => write!(f, "mod"),
            Self::Neg => write!(f, "neg"),
            Self::Not => write!(f, "not"),
            Self::And => write!(f, "and"),
            Self::Or => write!(f, "or"),
            Self::Call => write!(f, "call"),
            Self::Index => write!(f, "index"),
            Self::Colon => write!(f, "colon"),
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
    pub args: Rc<[(Rc<str>, Rc<str>)]>,
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
            Self::Ident(arg0) => write!(f, "ident {}", arg0),
            Self::Int(arg0) => write!(f, "{}", arg0),
            Self::Bool(arg0) => f.debug_tuple("bool").field(arg0).finish(),
            Self::Str(arg0) => f.debug_tuple("str").field(arg0).finish(),
            Self::InfixOp(arg0) => f.debug_tuple("op").field(arg0).finish(),
            Self::PrefixOp(arg0) => f.debug_tuple("op").field(arg0).finish(),
            Self::Let(l) => write!(f, "let {}", l.ty),
            Self::Return => write!(f, "return"),
            Self::If(arg0) => f.write_fmt(format_args!("if\n{:?}", arg0)),
            Self::Block(arg0) => f.debug_tuple("block").field(arg0).finish(),
            Self::Fn(arg0) => write!(f, "fn {:?}({:?}) -> {}", arg0.ident, arg0, arg0.ret_ty),
            Self::Call(arg0) => write!(f, "call(\n{:?})", arg0),
            Self::Array(arg0) => write!(f, "array{:?}", arg0),
            Self::Index(arg0) => write!(f, "{:?}", arg0),
            Self::Pair(pair) => write!(f, "pair({:?}, {:?})", pair.key, pair.value),
        }
    }
}

impl fmt::Display for FnStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(
            self.args
                .iter()
                .map(|arg| format!("{}: {}", arg.0, arg.1))
                .collect::<Vec<String>>()
                .join(", ")
                .as_str(),
        )
    }
}

// TODO merge the debug impl into this and make this impl fmt::Debug
impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn fmt_with_indent(node: &Node, f: &mut fmt::Formatter, indent: usize) -> fmt::Result {
            (0..indent).for_each(|_| _ = f.write_str("    "));

            match &node.kind {
                NodeKind::Ident(s) => writeln!(f, "ident {}", s),
                NodeKind::Int(i) => writeln!(f, "{}", i),
                NodeKind::Bool(b) => writeln!(f, "{}", b),
                NodeKind::Str(s) => writeln!(f, "{:?}", s),
                NodeKind::InfixOp(op) => writeln!(f, "{:?}", op),
                NodeKind::PrefixOp(op) => writeln!(f, "{:?}", op),
                NodeKind::Let(l) => writeln!(f, "let {}", l.ty),
                NodeKind::Return => writeln!(f, "return"),
                NodeKind::If(_) => writeln!(f, "if"),
                NodeKind::Fn(fstmt) => {
                    writeln!(f, "fn {}({}) -> {}", fstmt.ident, fstmt, fstmt.ret_ty)
                }
                NodeKind::Block(_) => writeln!(f, "block"),
                NodeKind::Call(call) => writeln!(f, "call {}", call.ident),
                NodeKind::Array(a) => writeln!(f, "array{:?}", a),
                NodeKind::Index(idx) => writeln!(f, "{:?}", idx),
                NodeKind::Pair(pair) => writeln!(f, "pair({:?}, {:?})", pair.key, pair.value),
            }?;

            match &node.kind {
                NodeKind::Block(block) => {
                    for stmt in block.statements.iter() {
                        fmt_with_indent(stmt, f, indent + 1)?
                    }
                }
                NodeKind::If(c) => {
                    fmt_with_indent(&c.condition, f, indent + 1)?;

                    if let Some(node) = &node.left {
                        writeln!(f, "{}then", "    ".repeat(indent))?;
                        fmt_with_indent(node, f, indent + 1)?;
                    }

                    if let Some(node) = &node.right {
                        writeln!(f, "{}else", "    ".repeat(indent))?;
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
            (0..indent).for_each(|_| _ = f.write_str("  "));
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
