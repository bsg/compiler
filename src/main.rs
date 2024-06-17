use std::{collections::HashMap, fs};

use ast::{NodeKind, NodeRef, Op};
use clap::Parser;

mod ast;
mod lexer;
mod parser;

#[derive(Clone)]
enum LlvmTy {
    Void,
    I1,
    I32,
    Ptr,
}

impl LlvmTy {
    fn as_str(&self) -> &'static str {
        match self {
            LlvmTy::Void => "void",
            LlvmTy::I1 => "i1",
            LlvmTy::I32 => "i32",
            LlvmTy::Ptr => "ptr",
        }
    }
}

#[derive(Clone)]
struct Type {
    ident: String,
    llvm_ty: LlvmTy,
}

#[derive(Clone)]
struct Var {
    is_arg: bool,
    reg: usize,
    ty: Type,
}

struct Ctx {
    types: HashMap<String, Type>,
}

impl Default for Ctx {
    fn default() -> Self {
        let mut types = HashMap::new();
        types.insert(
            "bool".to_string(),
            Type {
                ident: "bool".to_string(),
                llvm_ty: LlvmTy::I1,
            },
        );
        types.insert(
            "i32".to_string(),
            Type {
                ident: "i32".to_string(),
                llvm_ty: LlvmTy::I32,
            },
        );
        types.insert(
            "u32".to_string(),
            Type {
                ident: "u32".to_string(),
                llvm_ty: LlvmTy::I32,
            },
        );
        Self { types }
    }
}

struct FnCtx {
    next_reg: usize,
    next_label: usize,
    env: HashMap<String, Var>,
}

impl FnCtx {
    pub fn next_reg(&mut self) -> usize {
        let reg = self.next_reg;
        self.next_reg += 1;
        reg
    }
}

fn emit_fn(ctx: &mut Ctx, node: NodeRef) -> String {
    let mut fn_ctx = FnCtx {
        next_reg: 0usize,
        next_label: 0usize,
        env: HashMap::new(),
    };
    match (&node.kind, &node.right) {
        (NodeKind::Fn(fn_stmt), Some(body)) => {
            let ident = &fn_stmt.ident;
            let ret_type = &ctx
                .types
                .get(&fn_stmt.ret_ty.to_string())
                .unwrap()
                .llvm_ty
                .clone();
            let mut args = String::new();
            for arg in fn_stmt.args.iter() {
                let reg = fn_ctx.next_reg();
                args += &format!("{} %{reg}, ", ctx.types.get(arg.1.as_ref()).unwrap().llvm_ty.as_str());
                fn_ctx.env.insert(
                    arg.0.to_string(),
                    Var {
                        is_arg: true,
                        reg,
                        ty: Type {
                            ident: arg.1.to_string(),
                            llvm_ty: ctx.types.get(arg.1.as_ref()).unwrap().llvm_ty.clone(),
                        },
                    },
                );
            }
            // pop trailing comma and whitespace
            args.pop();
            args.pop();
            fn_ctx.next_reg();
            let body = emit_block(ctx, &mut fn_ctx, body.clone());
            format!("define {} @{ident}({args}) {{{body}\n}}", ret_type.as_str())
        }
        _ => panic!(),
    }
}

fn emit_block(ctx: &mut Ctx, fn_ctx: &mut FnCtx, node: NodeRef) -> String {
    let mut body = String::new();

    if let NodeKind::Block(block) = &node.kind {
        for stmt in block.statements.iter() {
            body += "\n";
            body += &emit_stmt(ctx, fn_ctx, stmt.clone());
        }
        body
    } else {
        panic!()
    }
}

fn emit_stmt(ctx: &mut Ctx, fn_ctx: &mut FnCtx, node: NodeRef) -> String {
    match &node.kind {
        NodeKind::Return => match emit_expr(ctx, fn_ctx, node.right.clone().unwrap()) {
            EmitExprRes::Imm(imm) => format!("ret {} {}", imm.ty.llvm_ty.as_str(), imm.code),
            EmitExprRes::Reg(r) => format!("{}ret i32 %{}", r.code, r.reg),
        },
        NodeKind::Let(let_stmt) => {
            let reg = fn_ctx.next_reg();
            if let NodeKind::Ident(ident) = &node.left.clone().unwrap().kind {
                fn_ctx.env.insert(
                    ident.to_string(),
                    Var {
                        is_arg: false,
                        reg,
                        ty: Type {
                            ident: ident.to_string(),
                            llvm_ty: ctx.types.get(let_stmt.ty.as_ref()).unwrap().llvm_ty.clone(),
                        },
                    },
                );
                match emit_expr(ctx, fn_ctx, node.right.clone().unwrap()) {
                    EmitExprRes::Imm(imm) => format!(
                        "%{reg} = alloca i32, align 4\nstore i32 {}, ptr %{reg}, align 4\n",
                        imm.code
                    ),
                    EmitExprRes::Reg(r) => format!(
                        "%{reg} = alloca i32, align 4\n{}store i32 %{}, ptr %{reg}, align 4",
                        r.code, r.reg
                    ),
                }
            } else {
                panic!()
            }
        }
        _ => "".to_string(),
    }
}

struct Imm {
    ty: Type,
    code: String,
}

struct Reg {
    ty: Type,
    code: String,
    reg: usize,
}

enum EmitExprRes {
    Imm(Imm),
    Reg(Reg),
}

fn emit_expr(_ctx: &mut Ctx, fn_ctx: &mut FnCtx, node: NodeRef) -> EmitExprRes {
    match &node.kind {
        NodeKind::Int(i) => EmitExprRes::Imm(Imm {
            ty: Type {
                ident: "i32".to_string(),
                llvm_ty: LlvmTy::I32,
            },
            code: format!("{}", i),
        }),
        NodeKind::Ident(ident) => {
            let var = fn_ctx.env.get(ident.as_ref()).unwrap().clone();
            if var.is_arg {
                EmitExprRes::Imm(Imm {
                    ty: var.ty,
                    code: format!("%{}", var.reg),
                })
            } else {
                let reg = fn_ctx.next_reg();
                EmitExprRes::Reg(Reg {
                    ty: var.ty.clone(),
                    code: format!(
                        "%{reg} = load {}, ptr %{}\n",
                        var.ty.llvm_ty.as_str(),
                        var.reg
                    ),
                    reg,
                })
            }
        }
        NodeKind::Call(call) => {
            let mut args = String::new();
            let mut code = String::new();
            for node in call.args.iter() {
                match emit_expr(_ctx, fn_ctx, node.clone()) {
                    EmitExprRes::Imm(imm) => args += &format!("i32 {}, ", imm.code),
                    EmitExprRes::Reg(r) => {
                        code += &r.code;
                        args += &format!("i32 %{}, ", r.reg)
                    }
                }
            }
            // remove trailing comma and whitespace
            args.pop();
            args.pop();

            let reg = fn_ctx.next_reg();
            // TODO fn return type lookup
            EmitExprRes::Reg(Reg {
                ty: Type {
                    ident: "u32".to_string(),
                    llvm_ty: LlvmTy::I32,
                },
                code: format!("{code}%{reg} = call i32 @{}({})\n", call.ident, args),
                reg,
            })
        }
        NodeKind::InfixOp(op) => {
            let lhs = emit_expr(_ctx, fn_ctx, node.left.clone().unwrap());
            let rhs = emit_expr(_ctx, fn_ctx, node.right.clone().unwrap());
            let op = match op {
                Op::Add => "add nsw i32",
                Op::Sub => "sub nsw i32",
                Op::Mul => "mul nsw i32",
                Op::Div => "sdiv i32",
                Op::Assign => "",
                _ => unimplemented!(),
            };
            let reg = fn_ctx.next_reg();
            // TODO type checking
            match (lhs, rhs) {
                (EmitExprRes::Imm(lhs), EmitExprRes::Imm(rhs)) => EmitExprRes::Reg(Reg {
                    ty: lhs.ty,
                    code: format!("%{reg} = {op} {}, {}\n", lhs.code, rhs.code),
                    reg,
                }),
                (EmitExprRes::Imm(lhs), EmitExprRes::Reg(rhs)) => EmitExprRes::Reg(Reg {
                    ty: lhs.ty,
                    code: format!("{}%{reg} = {op} {}, %{}\n", rhs.reg, lhs.code, rhs.reg),
                    reg,
                }),
                (EmitExprRes::Reg(lhs), EmitExprRes::Imm(rhs)) => EmitExprRes::Reg(Reg {
                    ty: lhs.ty,
                    code: format!("{}%{reg} = {op} %{}, {}\n", lhs.code, lhs.reg, rhs.code),
                    reg,
                }),
                (EmitExprRes::Reg(lhs), EmitExprRes::Reg(rhs)) => EmitExprRes::Reg(Reg {
                    ty: lhs.ty,
                    code: format!(
                        "{}{}%{reg} = {op} %{}, %{}\n",
                        lhs.code, rhs.code, lhs.reg, rhs.reg
                    ),
                    reg,
                }),
            }
        }
        _ => panic!(),
    }
}

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

    let mut ctx = Ctx::default();
    let mut ir = String::new();
    let ast = crate::parser::Parser::new(&code).parse();
    for node in ast {
        if args.ast {
            println!("{}\n", node);
        } else {
            match &node.kind {
                NodeKind::Fn(_) => ir += &emit_fn(&mut ctx, node),
                _ => (),
            }
            ir += "\n\n";
        }
    }

    println!("{}", ir);
}
