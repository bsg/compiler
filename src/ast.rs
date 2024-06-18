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
pub struct BlockNode {
    pub statements: Rc<[NodeRef]>,
}

#[derive(Clone, PartialEq)]
pub struct IfNode {
    pub condition: NodeRef,
    pub then_block: NodeRef,
    pub else_block: Option<NodeRef>,
}

#[derive(PartialEq, Clone)]
pub struct FnNode {
    pub ident: Rc<str>,
    pub args: Rc<[(Rc<str>, Rc<str>)]>,
    pub ret_ty: Rc<str>,
    pub body: NodeRef,
}

#[derive(Clone, PartialEq)]
pub struct CallNode {
    pub ident: IdentNode,
    pub args: Rc<[NodeRef]>,
}

#[derive(Clone, PartialEq)]
pub struct IndexNode {
    pub ident: IdentNode,
    pub index: NodeRef,
}

#[derive(Clone, PartialEq)]
pub struct PairNode {
    pub key: NodeRef,
    pub value: NodeRef,
}

#[derive(Clone, PartialEq)]
pub struct LetNode {
    pub ty: Rc<str>,
    pub lhs: NodeRef,
    pub rhs: NodeRef,
}

#[derive(Clone, PartialEq)]
pub struct IdentNode {
    pub name: Rc<str>,
}

#[derive(Clone, PartialEq)]
pub struct IntNode {
    pub value: i64,
}

#[derive(Clone, PartialEq)]
pub struct BoolNode {
    pub value: bool,
}

#[derive(Clone, PartialEq)]
pub struct StrNode {
    pub value: Rc<str>,
}

#[derive(Clone, PartialEq)]
pub struct UnOpNode {
    pub op: Op,
    pub rhs: NodeRef,
}

#[derive(Clone, PartialEq)]
pub struct BinOpNode {
    pub op: Op,
    pub lhs: NodeRef,
    pub rhs: NodeRef,
}

#[derive(Clone, PartialEq)]
pub struct ArrayNode {
    pub value: Vec<NodeRef>,
}

#[derive(Clone, PartialEq)]
pub struct ReturnNode {
    pub stmt: Option<NodeRef>,
}

#[derive(Clone, PartialEq)]
pub enum Node {
    Ident(IdentNode),
    Int(IntNode),
    Bool(BoolNode),
    Str(StrNode),
    UnOp(UnOpNode),
    BinOp(BinOpNode),
    Let(LetNode),
    Return(ReturnNode),
    If(IfNode),
    Block(BlockNode),
    Fn(FnNode),
    Call(CallNode),
    Array(Vec<Rc<Node>>),
    Index(IndexNode),
    Pair(PairNode),
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(x) => write!(f, "ident {}", x.name),
            Self::Int(x) => write!(f, "{}", x.value),
            Self::Bool(x) => f.debug_tuple("bool").field(&x.value).finish(),
            Self::Str(x) => f.debug_tuple("str").field(&x.value).finish(),
            Self::UnOp(x) => f.debug_tuple("op").field(&x.op).finish(),
            Self::BinOp(x) => f.debug_tuple("op").field(&x.op).finish(),
            Self::Let(l) => write!(f, "let {}", l.ty),
            Self::Return(_) => write!(f, "return"),
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

impl fmt::Display for FnNode {
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

            use Node::*;
            match node {
                Ident(s) => writeln!(f, "ident {}", s.name),
                Int(i) => writeln!(f, "{}", i.value),
                Bool(b) => writeln!(f, "{}", b.value),
                Str(s) => writeln!(f, "{:?}", s.value),
                UnOp(op) => writeln!(f, "{:?}", op.op),
                BinOp(op) => writeln!(f, "{:?}", op.op),
                Let(l) => writeln!(f, "let {}", l.ty),
                Return(_) => writeln!(f, "return"),
                If(_) => writeln!(f, "if"),
                Fn(fstmt) => {
                    writeln!(f, "fn {}({}) -> {}", fstmt.ident, fstmt, fstmt.ret_ty)
                }
                Block(_) => writeln!(f, "block"),
                Call(call) => writeln!(f, "call {}", call.ident.name),
                Array(a) => writeln!(f, "array{:?}", a),
                Index(idx) => writeln!(f, "{:?}", idx),
                Pair(pair) => writeln!(f, "pair({:?}, {:?})", pair.key, pair.value),
            }?;

            match node {
                Block(block) => {
                    for stmt in block.statements.iter() {
                        fmt_with_indent(stmt, f, indent + 1)?
                    }
                }
                If(if_node) => {
                    fmt_with_indent(&if_node.condition, f, indent + 1)?;

                    writeln!(f, "{}then", "    ".repeat(indent))?;
                    fmt_with_indent(&if_node.then_block, f, indent + 1)?;

                    if let Some(else_node) = &if_node.else_block {
                        writeln!(f, "{}else", "    ".repeat(indent))?;
                        fmt_with_indent(else_node, f, indent + 1)?;
                    }

                    return Ok(());
                }

                Call(c) => {
                    for arg in c.args.iter() {
                        fmt_with_indent(arg, f, indent + 1)?;
                    }
                }
                _ => (),
            }

            // TODO yeah...
            // if let Some(lhs) = node.left.as_ref() {
            //     fmt_with_indent(lhs, f, indent + 1)?;
            // }

            // if let Some(rhs) = node.right.as_ref() {
            //     fmt_with_indent(rhs, f, indent + 1)?;
            // }

            Ok(())
        }

        fmt_with_indent(self, f, 0)?;
        Ok(())
    }
}

// impl fmt::Debug for Node {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         fn fmt_with_indent(node: &Node, f: &mut fmt::Formatter, indent: usize) -> fmt::Result {
//             (0..indent).for_each(|_| _ = f.write_str("  "));
//             f.write_fmt(format_args!("{:?}\n", node.kind))?;

//             if let Some(lhs) = node.left.as_ref() {
//                 fmt_with_indent(lhs, f, indent + 1)?;
//             }

//             if let Some(rhs) = node.right.as_ref() {
//                 fmt_with_indent(rhs, f, indent + 1)?
//             }

//             Ok(())
//         }
//         fmt_with_indent(self, f, 0)?;
//         Ok(())
//     }
// }

impl fmt::Debug for BlockNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for stmt in self.statements.iter() {
            f.write_fmt(format_args!("{:?}", stmt))?;
        }
        Ok(())
    }
}

impl fmt::Debug for IfNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?})", self.condition))
    }
}

impl fmt::Debug for FnNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?})", self.args))
    }
}

impl fmt::Debug for CallNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?})", self.args))
    }
}

impl fmt::Debug for IndexNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{}[{:?}]", self.ident.name, self.index))
    }
}
