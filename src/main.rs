use std::{collections::HashMap, fs};

use ast::{BinOpNode, IfNode, Node, NodeRef, Op};
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
    align: u8,
}

impl Type {
    pub fn new(ident: &str, llvm_ty: LlvmTy, align: u8) -> Self {
        Type {
            ident: ident.to_string(),
            llvm_ty,
            align,
        }
    }
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

impl Ctx {
    pub fn get_type(&self, name: &str) -> Option<Type> {
        self.types.get(name).cloned()
    }
}

impl Default for Ctx {
    fn default() -> Self {
        let mut types = HashMap::new();
        types.insert("void".to_string(), Type::new("void", LlvmTy::Void, 1));
        types.insert("bool".to_string(), Type::new("bool", LlvmTy::I1, 1));
        types.insert("i32".to_string(), Type::new("i32", LlvmTy::I32, 4));
        types.insert("u32".to_string(), Type::new("u32", LlvmTy::I32, 4));
        Self { types }
    }
}

// TODO env accessor
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

    pub fn next_label(&mut self) -> usize {
        let label = self.next_label;
        self.next_label += 1;
        label
    }
}

fn emit_fn(ctx: &mut Ctx, node: NodeRef) -> String {
    let mut fn_ctx = FnCtx {
        next_reg: 0usize,
        next_label: 0usize,
        env: HashMap::new(),
    };
    if let Node::Fn(fn_node) = &*node {
        let ident = &fn_node.ident;
        let ret_type = &ctx.get_type(&fn_node.ret_ty).unwrap().llvm_ty;
        let mut args = String::new();
        for arg in fn_node.args.iter() {
            let reg = fn_ctx.next_reg();
            let ty = ctx.get_type(arg.1.as_ref()).unwrap();
            args += &format!("{} %{reg}, ", ty.llvm_ty.as_str());
            fn_ctx.env.insert(
                arg.0.to_string(),
                Var {
                    is_arg: true,
                    reg,
                    ty: ty.clone(),
                },
            );
        }
        // pop trailing comma and whitespace
        args.pop();
        args.pop();
        fn_ctx.next_reg();
        let body = emit_block(ctx, &mut fn_ctx, fn_node.body.clone());
        format!(
            "define {} @{ident}({args}) {{{}\n}}",
            ret_type.as_str(),
            body.code
        )
    } else {
        panic!()
    }
}

struct IrBlock {
    code: String,
    is_terminal: bool,
}

fn emit_block(ctx: &mut Ctx, fn_ctx: &mut FnCtx, node: NodeRef) -> IrBlock {
    let mut body = String::new();
    let mut is_terminal = false;

    if let Node::Block(block) = &*node {
        for stmt in block.statements.iter() {
            let stmt = emit_stmt(ctx, fn_ctx, stmt.clone());
            if stmt.is_terminal {
                if !is_terminal {
                    is_terminal = true;
                } else {
                    // TODO stmt is unreachable
                    todo!()
                }
            }
            body += "\n";
            body += &stmt.code;
        }
        IrBlock {
            code: body,
            is_terminal,
        }
    } else {
        panic!()
    }
}

struct IrStmt {
    code: String,
    is_terminal: bool,
}

fn emit_stmt(ctx: &mut Ctx, fn_ctx: &mut FnCtx, node: NodeRef) -> IrStmt {
    use Node::*;
    match &*node {
        Return(node) => match &node.stmt {
            Some(rhs) => match emit_expr(ctx, fn_ctx, rhs.clone()) {
                IrExpr::Imm(imm) => IrStmt {
                    code: format!("ret {} {}", imm.ty.llvm_ty.as_str(), imm.code),
                    is_terminal: true,
                },
                IrExpr::Reg(r) => IrStmt {
                    code: format!("{}ret {} %{}", r.code, r.ty.llvm_ty.as_str(), r.reg),
                    is_terminal: true,
                },
            },
            None => IrStmt {
                code: "ret void".to_owned(),
                is_terminal: true,
            },
        },
        Let(node) => {
            let reg = fn_ctx.next_reg();
            if let Ident(ident) = &*node.lhs {
                fn_ctx.env.insert(
                    ident.name.to_string(),
                    Var {
                        is_arg: false,
                        reg,
                        ty: ctx.get_type(node.ty.as_ref()).unwrap(),
                    },
                );
                match emit_expr(ctx, fn_ctx, node.rhs.clone()) {
                    IrExpr::Imm(imm) => IrStmt {
                        code: format!(
                            "%{reg} = alloca {}, align {}\nstore {} {}, ptr %{reg}, align {}",
                            imm.ty.llvm_ty.as_str(),
                            imm.ty.align,
                            imm.ty.llvm_ty.as_str(),
                            imm.code,
                            imm.ty.align,
                        ),
                        is_terminal: false,
                    },
                    IrExpr::Reg(r) => IrStmt {
                        code: format!(
                            "%{reg} = alloca {}, align {}\n{}store {} %{}, ptr %{reg}, align {}",
                            r.ty.llvm_ty.as_str(),
                            r.ty.align,
                            r.code,
                            r.ty.llvm_ty.as_str(),
                            r.reg,
                            r.ty.align,
                        ),
                        is_terminal: false,
                    },
                }
            } else {
                panic!()
            }
        }
        If(IfNode {
            condition,
            then_block,
            else_block,
        }) => {
            let mut then_block = emit_block(ctx, fn_ctx, then_block.clone());
            // FIXME optional else
            let mut else_block = emit_block(ctx, fn_ctx, else_block.clone().unwrap());
            let l_true = fn_ctx.next_label();
            let l_false = fn_ctx.next_label();
            let mut exit_point: String = String::new();

            if then_block.is_terminal || else_block.is_terminal {
                let exit_to = fn_ctx.next_label();

                if !then_block.is_terminal {
                    then_block.code += &format!("\nbr label %l{}", exit_to);
                }

                if !else_block.is_terminal {
                    else_block.code += &format!("\nbr label %l{}", exit_to);
                }

                exit_point = format!("\nl{}:", exit_to);
            }

            match emit_expr(ctx, fn_ctx, condition.clone()) {
                IrExpr::Imm(imm) => IrStmt {
                    code: format!(
                        "br i1 {}, label %l{l_true}, label %l{l_false}\nl{l_true}:{}\nl{l_false}:{}{}",
                        then_block.code,
                        imm.code,
                        else_block.code,
                        exit_point,
                    ),
                    is_terminal: then_block.is_terminal && else_block.is_terminal,
                },
                IrExpr::Reg(r) => IrStmt {
                    code: format!(
                        "{}br i1 %{}, label %l{l_true}, label %l{l_false}\nl{l_true}:{}\nl{l_false}:{}{}",
                        r.code,
                        r.reg,
                        then_block.code,
                        else_block.code,
                        exit_point
                    ),
                    is_terminal: then_block.is_terminal && else_block.is_terminal,
                }
            }
        }
        BinOp(BinOpNode { op, lhs, rhs }) => match op {
            Op::Assign => {
                if let Ident(ident_node) = &**lhs {
                    let lhs = fn_ctx.env.get(&ident_node.name.to_string()).unwrap().reg;
                    match emit_expr(ctx, fn_ctx, rhs.clone()) {
                        IrExpr::Imm(imm) => IrStmt {
                            code: format!(
                                "store {} {}, ptr %{}, align {}",
                                imm.ty.llvm_ty.as_str(),
                                imm.code,
                                lhs,
                                imm.ty.align
                            ),
                            is_terminal: false,
                        },
                        IrExpr::Reg(r) => IrStmt {
                            code: format!(
                                "{}store {} %{}, ptr %{}, align {}",
                                r.code,
                                r.ty.llvm_ty.as_str(),
                                r.reg,
                                lhs,
                                r.ty.align
                            ),
                            is_terminal: false,
                        },
                    }
                } else {
                    panic!()
                }
            }
            _ => unimplemented!(),
        },
        _ => unimplemented!(),
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

enum IrExpr {
    Imm(Imm),
    Reg(Reg),
}

fn emit_expr(_ctx: &mut Ctx, fn_ctx: &mut FnCtx, node: NodeRef) -> IrExpr {
    use Node::*;

    match &*node {
        Int(i) => IrExpr::Imm(Imm {
            ty: Type::new("i32", LlvmTy::I32, 4),
            code: format!("{}", i.value),
        }),
        Bool(b) => IrExpr::Imm(Imm {
            ty: Type::new("bool", LlvmTy::I1, 1),
            code: format!("{}", b.value),
        }),
        Ident(ident) => {
            let var = fn_ctx.env.get(&*ident.name).unwrap().clone();
            if var.is_arg {
                IrExpr::Imm(Imm {
                    ty: var.ty,
                    code: format!("%{}", var.reg),
                })
            } else {
                let reg = fn_ctx.next_reg();
                IrExpr::Reg(Reg {
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
        Call(call) => {
            let mut args = String::new();
            let mut code = String::new();
            for node in call.args.iter() {
                match emit_expr(_ctx, fn_ctx, node.clone()) {
                    IrExpr::Imm(imm) => args += &format!("i32 {}, ", imm.code),
                    IrExpr::Reg(r) => {
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
            IrExpr::Reg(Reg {
                ty: Type::new("u32", LlvmTy::I32, 4),
                code: format!("{code}%{reg} = call i32 @{}({})\n", call.ident.name, args),
                reg,
            })
        }
        BinOp(BinOpNode { op, lhs, rhs }) => {
            let lhs = emit_expr(_ctx, fn_ctx, lhs.clone());
            let rhs = emit_expr(_ctx, fn_ctx, rhs.clone());
            // TODO ret_bool is temporary, impl emit_op()
            let (op, ret_bool) = match op {
                Op::Add => ("add nsw", false),
                Op::Sub => ("sub nsw", false),
                Op::Mul => ("mul nsw", false),
                Op::Div => ("sdiv", false),
                Op::Gt => ("icmp sgt", true),
                Op::Lt => ("icmp slt", true),
                _ => unimplemented!(),
            };
            let reg = fn_ctx.next_reg();
            // TODO type checking
            match (lhs, rhs) {
                (IrExpr::Imm(lhs), IrExpr::Imm(rhs)) => IrExpr::Reg(Reg {
                    ty: if ret_bool {
                        Type::new("bool", LlvmTy::I1, 1)
                    } else {
                        lhs.ty.clone()
                    },
                    code: format!(
                        "%{reg} = {op} {} {}, {}\n",
                        lhs.ty.llvm_ty.as_str(),
                        lhs.code,
                        rhs.code
                    ),
                    reg,
                }),
                (IrExpr::Imm(lhs), IrExpr::Reg(rhs)) => IrExpr::Reg(Reg {
                    ty: if ret_bool {
                        Type::new("bool", LlvmTy::I1, 1)
                    } else {
                        lhs.ty.clone()
                    },
                    code: format!(
                        "{}%{reg} = {op} {} {}, %{}\n",
                        rhs.reg,
                        lhs.ty.llvm_ty.as_str(),
                        lhs.code,
                        rhs.reg
                    ),
                    reg,
                }),
                (IrExpr::Reg(lhs), IrExpr::Imm(rhs)) => IrExpr::Reg(Reg {
                    ty: if ret_bool {
                        Type::new("bool", LlvmTy::I1, 1)
                    } else {
                        lhs.ty.clone()
                    },
                    code: format!(
                        "{}%{reg} = {op} {} %{}, {}\n",
                        lhs.code,
                        lhs.ty.llvm_ty.as_str(),
                        lhs.reg,
                        rhs.code
                    ),
                    reg,
                }),
                (IrExpr::Reg(lhs), IrExpr::Reg(rhs)) => IrExpr::Reg(Reg {
                    ty: if ret_bool {
                        Type::new("bool", LlvmTy::I1, 1)
                    } else {
                        lhs.ty.clone()
                    },
                    code: format!(
                        "{}{}%{reg} = {op} {} %{}, %{}\n",
                        lhs.code,
                        rhs.code,
                        lhs.ty.llvm_ty.as_str(),
                        lhs.reg,
                        rhs.reg
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
            if let Node::Fn(_) = *node {
                ir += &emit_fn(&mut ctx, node)
            }
            ir += "\n\n";
        }
    }

    println!("{}", ir);
}
