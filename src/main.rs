use std::{collections::HashMap, fs};

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
    let ast = crate::parser::Parser::new(&code).parse();
    for node in ast {
        if args.ast {
            println!("{}\n", node);
        } else {
            match &node.kind {
                NodeKind::Fn(_) => ir += &emit_fn(node),
                _ => (),
            }
            ir += "\n\n";
        }
    }

    println!("{}", ir);
}

#[derive(Clone)]
struct Var {
    is_arg: bool,
    reg: usize,
}

struct FnCtx {
    next_reg: usize,
    env: HashMap<String, Var>,
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
        next_reg: 0usize,
        env: HashMap::new(),
    };
    match (&node.kind, &node.right) {
        (NodeKind::Fn(fn_stmt), Some(body)) => {
            let ident = &fn_stmt.ident;
            let ret_type = &fn_stmt.ret_ty;
            let mut args = String::new();
            for arg in fn_stmt.args.iter() {
                let reg = fn_ctx.next_reg();
                args += &format!("i32 %{reg}, ");
                fn_ctx
                    .env
                    .insert(arg.0.to_string(), Var { is_arg: true, reg });
            }
            // pop trailing comma and whitespace
            args.pop();
            args.pop();
            fn_ctx.next_reg();
            let body = emit_block(body.clone(), &mut fn_ctx);
            format!("define {ret_type} @{ident}({args}) {{{body}\n}}")
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
                fn_ctx
                    .env
                    .insert(ident.to_string(), Var { is_arg: false, reg });
                match emit_expr(node.right.clone().unwrap(), fn_ctx) {
                    EmitExprRes::Imm(code) => format!(
                        "%{reg} = alloca i32, align 4\nstore i32 {code}, ptr %{reg}, align 4\n"
                    ),
                    EmitExprRes::Reg(code, res_reg) => format!(
                        "%{reg} = alloca i32, align 4\n{code}store i32 %{res_reg}, ptr %{reg}, align 4"
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
            let var = fn_ctx.env.get(ident.as_ref()).unwrap().clone();
            if var.is_arg {
                EmitExprRes::Imm(format!("%{}", var.reg))
            } else {
                let reg = fn_ctx.next_reg();
                EmitExprRes::Reg(format!("%{reg} = load i32, ptr %{}\n", var.reg), reg)
            }
        },
        NodeKind::Call(call) => {
            let mut args = String::new();
            let mut code = String::new();
            for node in call.args.iter() {
                match emit_expr(node.clone(), fn_ctx) {
                    EmitExprRes::Imm(code) => 
                    {args += &format!("i32 {}, ", code)
                },
                    EmitExprRes::Reg(c, res_reg) => {
                        code += &c;
                        args += &format!("i32 %{}, ", res_reg)
                    },
                }
            }
            // remove trailing comma and whitespace
            args.pop();
            args.pop();
            
            let reg = fn_ctx.next_reg();
            EmitExprRes::Reg(format!("{code}%{reg} = call i32 @{}({})\n", call.ident, args), reg)
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
