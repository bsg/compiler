use std::{collections::HashMap, fmt::format, fs, rc::Rc};

use ast::{NodeKind, NodeRef, Op};
use clap::Parser;

mod ast;
mod lexer;
mod parser;

#[derive(Parser)]
#[command()]
struct Args {
    path: Option<String>,
    #[clap(long, short, action)]
    ast: bool,
}

fn main() {
    let args = Args::parse();
    if args.path.is_none() {
        return;
    }

    let code = fs::read_to_string(args.path.unwrap()).unwrap();

    let mut ir = String::new();
    if let Some(node) = crate::parser::Parser::new(&code).parse_expression(0) {
        if args.ast {
            println!("{}", node);
        } else {
            match &node.kind {
                NodeKind::Fn(_) => ir += &emit_fn(node),
                _ => (),
            }
        }
    }

    println!("{}", ir);
}

struct FnCtx {
    next_reg: usize,
    env: HashMap<String, usize>,
}

impl FnCtx {
    pub fn next_reg(&mut self) -> usize {
        let reg = self.next_reg;
        self.next_reg += 1;
        reg
    }
}

fn emit_fn(node: NodeRef) -> String {
    let mut fn_ctx = FnCtx {
        next_reg: 1usize,
        env: HashMap::new(),
    };
    match (&node.kind, &node.right) {
        (NodeKind::Fn(fn_stmt), Some(body)) => {
            let ident = &fn_stmt.ident;
            let ret_type = &fn_stmt.ret_ty;
            let body = emit_block(body.clone(), &mut fn_ctx);
            format!("define {ret_type} @{ident}() {{{body}\n}}")
        }
        _ => panic!(),
    }
}

fn emit_block(node: NodeRef, fn_ctx: &mut FnCtx) -> String {
    let mut body = String::new();

    if let NodeKind::Block(block) = &node.kind {
        for stmt in block.statements.iter() {
            body += "\n";
            body += &emit_stmt(stmt.clone(), fn_ctx);
        }
        body
    } else {
        panic!()
    }
}

fn emit_stmt(node: NodeRef, fn_ctx: &mut FnCtx) -> String {
    match &node.kind {
        NodeKind::Return => match emit_expr(node.right.clone().unwrap(), fn_ctx) {
            EmitExprRes::Imm(expr) => format!("ret i32 {expr}"),
            EmitExprRes::Reg(expr, reg) => format!("{expr}ret i32 %{reg}"),
        },
        NodeKind::Let(let_stmt) => {
            let reg = fn_ctx.next_reg();
            if let NodeKind::Ident(ident) = &node.left.clone().unwrap().kind {
                fn_ctx.env.insert(ident.to_string(), reg);
                match emit_expr(node.right.clone().unwrap(), fn_ctx) {
                    EmitExprRes::Imm(code) => format!(
                        "%{reg} = alloca i32, align 4\nstore i32 {code}, ptr %{reg}, align 4\n"
                    ),
                    EmitExprRes::Reg(code, res_reg) => format!(
                        "%{reg} = alloca i32, align 4\n{code}\nstore i32 %{res_reg}, ptr %{reg}, align 4\n"
                    ),
                }
            } else {
                panic!()
            }
        }
        _ => "".to_string(),
    }
}

enum EmitExprRes {
    Imm(String),
    Reg(String, usize),
}

fn emit_expr(node: NodeRef, fn_ctx: &mut FnCtx) -> EmitExprRes {
    match &node.kind {
        NodeKind::Int(i) => EmitExprRes::Imm(format!("{}", i)),
        NodeKind::Ident(ident) => {
            let reg = fn_ctx.next_reg();
            EmitExprRes::Reg(
                format!(
                    "%{reg} = load i32, ptr %{}\n",
                    fn_ctx.env.get(ident.as_ref()).unwrap()
                ),
                reg,
            )
        }
        NodeKind::InfixOp(op) => {
            let lhs = emit_expr(node.left.clone().unwrap(), fn_ctx);
            let rhs = emit_expr(node.right.clone().unwrap(), fn_ctx);
            let op = match op {
                Op::Add => "add nsw i32",
                Op::Sub => "sub nsw i32",
                Op::Mul => "mul nsw i32",
                Op::Div => "sdiv i32",
                Op::Assign => "",
                _ => unimplemented!(),
            };
            let reg = fn_ctx.next_reg();
            match (lhs, rhs) {
                (EmitExprRes::Imm(lhs), EmitExprRes::Imm(rhs)) => {
                    EmitExprRes::Reg(format!("%{reg} = {op} {lhs}, {rhs}\n",), reg)
                }
                (EmitExprRes::Imm(lhs), EmitExprRes::Reg(rhs, rhs_reg)) => {
                    EmitExprRes::Reg(format!("{rhs}%{reg} = {op} {lhs}, %{rhs_reg}\n",), reg)
                }
                (EmitExprRes::Reg(lhs, lhs_reg), EmitExprRes::Imm(rhs)) => {
                    EmitExprRes::Reg(format!("{lhs}%{reg} = {op} %{lhs_reg}, {rhs}\n",), reg)
                }
                (EmitExprRes::Reg(lhs, lhs_reg), EmitExprRes::Reg(rhs, rhs_reg)) => {
                    EmitExprRes::Reg(
                        format!("{lhs}{rhs}%{reg} = {op} %{lhs_reg}, %{rhs_reg}\n",),
                        reg,
                    )
                }
            }
        }
        _ => panic!(),
    }
}
