use llvm_sys::core::*;
use llvm_sys::prelude::*;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::ffi::CString;
use std::rc::Rc;

use crate::ast::*;

trait ToCStr {
    fn to_cstring(self) -> CString;
}

impl ToCStr for &str {
    fn to_cstring(self) -> CString {
        CString::new(self).unwrap()
    }
}

impl ToCStr for String {
    fn to_cstring(self) -> CString {
        CString::new(self).unwrap()
    }
}

pub enum Type {
    None,
    Bool,
    Int {
        /// width in bits
        width: usize,
        signed: bool,
    },
    Ptr {
        // TODO type id
        pointee_ty: Rc<str>,
    },
}

impl Type {
    pub fn get_llvm_type(&self, env: &Env) -> LLVMTypeRef {
        match self {
            Type::None => unsafe { LLVMVoidType() },
            Type::Bool => unsafe { LLVMInt1Type() },
            Type::Int { width, .. } => match width {
                8 => unsafe { LLVMInt8Type() },
                16 => unsafe { LLVMInt16Type() },
                32 => unsafe { LLVMInt32Type() },
                64 => unsafe { LLVMInt64Type() },
                128 => unsafe { LLVMInt128Type() },
                _ => todo!(),
            },
            Type::Ptr { pointee_ty } => unsafe {
                LLVMPointerType(env.get_type(pointee_ty).unwrap().get_llvm_type(env), 0)
            },
        }
    }
}

pub struct Var {
    val: LLVMValueRef,
    ty: LLVMTypeRef,
}

pub struct Func {
    val: LLVMValueRef,
    ty: LLVMTypeRef,
    env: Rc<UnsafeCell<Env>>,
    body: LLVMBasicBlockRef,
}

pub struct Env {
    parent: Option<Rc<UnsafeCell<Env>>>,
    vars: HashMap<String, Var>,
    types: HashMap<String, Type>,
    funcs: HashMap<String, Func>,
}

impl Env {
    pub fn new() -> Self {
        let mut types: HashMap<String, Type> = HashMap::new();
        types.insert("void".to_owned(), Type::None);
        types.insert(
            "u8".to_owned(),
            Type::Int {
                width: 8,
                signed: false,
            },
        );
        types.insert(
            "i8".to_owned(),
            Type::Int {
                width: 8,
                signed: true,
            },
        );
        types.insert(
            "u32".to_owned(),
            Type::Int {
                width: 32,
                signed: false,
            },
        );
        types.insert(
            "i32".to_owned(),
            Type::Int {
                width: 32,
                signed: true,
            },
        );
        types.insert("bool".to_owned(), Type::Bool);
        types.insert(
            "*void".to_owned(),
            Type::Ptr {
                pointee_ty: "void".into(),
            },
        );
        types.insert(
            "*u8".to_owned(),
            Type::Ptr {
                pointee_ty: "u8".into(),
            },
        );
        types.insert(
            "*i8".to_owned(),
            Type::Ptr {
                pointee_ty: "i8".into(),
            },
        );
        types.insert(
            "*u32".to_owned(),
            Type::Ptr {
                pointee_ty: "u32".into(),
            },
        );
        types.insert(
            "*i32".to_owned(),
            Type::Ptr {
                pointee_ty: "i32".into(),
            },
        );
        types.insert(
            "*bool".to_owned(),
            Type::Ptr {
                pointee_ty: "bool".into(),
            },
        );

        Env {
            parent: None,
            vars: HashMap::new(),
            types,
            funcs: HashMap::new(),
        }
    }

    // heh
    pub fn make_child(parent: Rc<UnsafeCell<Env>>) -> Self {
        Env {
            parent: Some(parent),
            vars: HashMap::new(),
            types: HashMap::new(),
            funcs: HashMap::new(),
        }
    }

    pub fn insert_type(&mut self, ident: &str, ty: Type) {
        self.types.insert(ident.to_string(), ty);
    }

    pub fn get_type(&self, ident: &str) -> Option<&Type> {
        match self.types.get(ident) {
            Some(ty) => Some(ty),
            None => {
                if let Some(parent) = &self.parent {
                    let p = unsafe { &*parent.get() };
                    p.get_type(ident)
                } else {
                    None
                }
            }
        }
    }

    pub fn insert_var(&mut self, ident: &str, val: LLVMValueRef, ty: LLVMTypeRef) {
        self.vars.insert(ident.to_string(), Var { val, ty });
    }

    pub fn get_var(&self, ident: &str) -> Option<&Var> {
        match self.vars.get(ident) {
            v @ Some(_) => v,
            None => {
                if let Some(parent) = &self.parent {
                    let p = unsafe { &*parent.get() };
                    p.get_var(ident)
                } else {
                    None
                }
            }
        }
    }

    pub fn insert_func(
        &mut self,
        ident: &str,
        val: LLVMValueRef,
        ty: LLVMTypeRef,
        env: Rc<UnsafeCell<Env>>,
        body: LLVMBasicBlockRef,
    ) {
        self.funcs
            .insert(ident.to_string(), Func { val, ty, env, body });
    }

    pub fn get_func(&self, ident: &str) -> Option<&Func> {
        match self.funcs.get(ident) {
            v @ Some(_) => v,
            None => {
                if let Some(parent) = &self.parent {
                    let p = unsafe { &*parent.get() };
                    p.get_func(ident)
                } else {
                    None
                }
            }
        }
    }
}

// TODO rename
struct Val {
    ty: Type,
    llvm_val: LLVMValueRef,
}

pub struct ModuleBuilder {
    name: String,
    module: LLVMModuleRef,
    builder: LLVMBuilderRef,
    // because fuck it
    env: Rc<UnsafeCell<Env>>,
    current_func_ident: Option<Rc<str>>,
}

impl ModuleBuilder {
    pub fn new(name: &str) -> Self {
        let mod_name = name.to_cstring().as_ptr();
        let module = unsafe { LLVMModuleCreateWithName(mod_name) };
        let builder = unsafe { LLVMCreateBuilder() };

        Self {
            name: name.to_owned(),
            module,
            builder,
            env: Rc::new(UnsafeCell::new(Env::new())),
            current_func_ident: None,
        }
    }

    fn build_unop(&mut self, env: Rc<UnsafeCell<Env>>, node: NodeRef) -> LLVMValueRef {
        if let Node::UnOp { op, rhs } = &*node {
            match op {
                Op::Ref => self.build_expr(env, rhs.clone(), true),
                Op::Deref => unsafe {
                    LLVMBuildLoad2(
                        self.builder,
                        LLVMInt32Type(),
                        self.build_expr(env, rhs.clone(), false),
                        "".to_cstring().as_ptr(),
                    )
                },
                _ => todo!(),
            }
        } else {
            todo!()
        }
    }

    fn build_binop(&mut self, env: Rc<UnsafeCell<Env>>, node: NodeRef) -> LLVMValueRef {
        if let Node::BinOp { op, lhs, rhs } = &*node {
            match op {
                Op::Add => unsafe {
                    LLVMBuildAdd(
                        self.builder,
                        self.build_expr(env.clone(), lhs.clone(), false),
                        self.build_expr(env, rhs.clone(), false),
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Sub => unsafe {
                    LLVMBuildSub(
                        self.builder,
                        self.build_expr(env.clone(), lhs.clone(), false),
                        self.build_expr(env, rhs.clone(), false),
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Mul => unsafe {
                    LLVMBuildMul(
                        self.builder,
                        self.build_expr(env.clone(), lhs.clone(), false),
                        self.build_expr(env, rhs.clone(), false),
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Div => unsafe {
                    // TODO
                    LLVMBuildUDiv(
                        self.builder,
                        self.build_expr(env.clone(), lhs.clone(), false),
                        self.build_expr(env, rhs.clone(), false),
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Eq => unsafe {
                    LLVMBuildICmp(
                        self.builder,
                        llvm_sys::LLVMIntPredicate::LLVMIntEQ,
                        self.build_expr(env.clone(), lhs.clone(), false),
                        self.build_expr(env, rhs.clone(), false),
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Gt => unsafe {
                    LLVMBuildICmp(
                        self.builder,
                        llvm_sys::LLVMIntPredicate::LLVMIntSGT, // TODO
                        self.build_expr(env.clone(), lhs.clone(), false),
                        self.build_expr(env, rhs.clone(), false),
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Lt => unsafe {
                    LLVMBuildICmp(
                        self.builder,
                        llvm_sys::LLVMIntPredicate::LLVMIntSLT, // TODO
                        self.build_expr(env.clone(), lhs.clone(), false),
                        self.build_expr(env, rhs.clone(), false),
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Assign => unsafe {
                    match &**lhs {
                        Node::Ident { .. } => LLVMBuildStore(
                            self.builder,
                            self.build_expr(env.clone(), rhs.clone(), false),
                            self.build_expr(env, lhs.clone(), true),
                        ),
                        Node::UnOp {
                            op: Op::Deref,
                            rhs: deref_rhs,
                        } => match &**deref_rhs {
                            Node::Ident { .. } => LLVMBuildStore(
                                self.builder,
                                self.build_expr(env.clone(), rhs.clone(), false),
                                self.build_expr(env, deref_rhs.clone(), false),
                            ),
                            _ => todo!(),
                        },
                        _ => panic!("cannot assign to whatever this is"),
                    }
                },
                _ => unimplemented!(),
            }
        } else {
            todo!()
        }
    }

    fn build_expr(
        &mut self,
        env: Rc<UnsafeCell<Env>>,
        node: NodeRef,
        ident_no_load: bool,
    ) -> LLVMValueRef {
        match &*node {
            Node::Int { value } => {
                // FIXME int type
                // TODO sign extend
                unsafe { LLVMConstInt(LLVMInt32Type(), (*value).try_into().unwrap(), 0) }
            }
            Node::Bool { value } => unsafe {
                LLVMConstInt(LLVMInt1Type(), if *value { 1 } else { 0 }, 0)
            },
            Node::Ident { name } => unsafe {
                if let Some(var) = (*env.get()).get_var(name) {
                    if ident_no_load {
                        var.val
                    } else {
                        LLVMBuildLoad2(self.builder, var.ty, var.val, "".to_cstring().as_ptr())
                    }
                } else {
                    panic!("unresolved ident {}", name)
                }
            },
            Node::UnOp { .. } => self.build_unop(env, node.clone()),
            Node::BinOp { .. } => self.build_binop(env, node.clone()),
            Node::Call {
                ident,
                args: arg_exprs,
            } => {
                // TODO LLVMGetNamedFunction for extern fns
                let func = (unsafe { &*env.get() }).get_func(ident).unwrap();
                let mut args: Vec<LLVMValueRef> = Vec::new();
                for arg in arg_exprs.iter() {
                    args.push(self.build_expr(env.clone(), arg.clone(), false));
                }
                unsafe {
                    LLVMBuildCall2(
                        self.builder,
                        func.ty,
                        func.val,
                        args.as_mut_slice().as_mut_ptr(),
                        args.len().try_into().unwrap(),
                        "".to_cstring().as_ptr(),
                    )
                }
            }
            _ => panic!("unimplemented!\n {:?}", node),
        }
    }

    fn build_stmt(&mut self, env: Rc<UnsafeCell<Env>>, node: NodeRef) -> LLVMValueRef {
        match &*node {
            Node::Return { stmt } => {
                if let Some(rhs) = &stmt {
                    let v = self.build_expr(env, rhs.clone(), false);
                    unsafe { LLVMBuildRet(self.builder, v) }
                } else {
                    unsafe { LLVMBuildRetVoid(self.builder) }
                }
            }
            Node::Let { ty, lhs, rhs } => unsafe {
                if let Node::Ident { name } = &**lhs {
                    let reg = LLVMBuildAlloca(
                        self.builder,
                        (*env.get())
                            .get_type(ty)
                            .unwrap()
                            .get_llvm_type(&*(*env).get()),
                        "".to_cstring().as_ptr(),
                    );
                    let rhs = self.build_expr(env.clone(), rhs.clone(), false);
                    let ty = (*env.get()).get_type(ty).unwrap();
                    (*env.get()).insert_var(name, reg, ty.get_llvm_type(&*(*env).get()));
                    LLVMBuildStore(self.builder, rhs, reg)
                } else {
                    panic!()
                }
            },
            Node::If {
                condition,
                then_block,
                else_block,
            } => unsafe {
                if let Some(fn_ident) = &self.current_func_ident {
                    let current_func = (*self.env.get()).get_func(fn_ident).unwrap();

                    // FIXME i hate the ordering of nested blocks in the IR. need to build depth first
                    let bb_then = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    let bb_else = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    let bb_exit = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    let cond = LLVMBuildCondBr(
                        self.builder,
                        self.build_expr(env.clone(), condition.clone(), false),
                        bb_then,
                        bb_else,
                    );

                    LLVMPositionBuilderAtEnd(self.builder, bb_then);
                    self.build_block(env.clone(), then_block.clone());
                    LLVMBuildBr(self.builder, bb_exit);

                    LLVMPositionBuilderAtEnd(self.builder, bb_else);
                    if let Some(else_block) = else_block {
                        self.build_block(env.clone(), else_block.clone());
                    }
                    LLVMBuildBr(self.builder, bb_exit);

                    LLVMPositionBuilderAtEnd(self.builder, bb_exit);
                    cond
                } else {
                    panic!("if stmt outside fn")
                }
            },
            Node::While { condition, body } => unsafe {
                if let Some(fn_ident) = &self.current_func_ident {
                    let current_func = (*self.env.get()).get_func(fn_ident).unwrap();

                    // FIXME i hate the ordering of nested blocks in the IR. need to build depth first
                    let bb_test = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    LLVMBuildBr(self.builder, bb_test);
                    let bb_body = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    let bb_exit = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());

                    LLVMPositionBuilderAtEnd(self.builder, bb_test);
                    let cond = LLVMBuildCondBr(
                        self.builder,
                        self.build_expr(env.clone(), condition.clone(), false),
                        bb_body,
                        bb_exit,
                    );

                    LLVMPositionBuilderAtEnd(self.builder, bb_body);
                    self.build_block(env.clone(), body.clone());
                    LLVMBuildBr(self.builder, bb_test);

                    LLVMPositionBuilderAtEnd(self.builder, bb_exit);
                    cond
                } else {
                    panic!("while stmt outside fn")
                }
            },
            _ => self.build_expr(env, node, false),
        }
    }

    fn build_block(&mut self, env: Rc<UnsafeCell<Env>>, node: NodeRef) {
        if let Node::Block { statements } = &*node {
            for stmt in statements.iter() {
                self.build_stmt(env.clone(), stmt.clone());
            }
        } else {
            panic!()
        }
    }

    pub fn build_func(&mut self, node: NodeRef) {
        let env = self.env.clone();
        let env = unsafe { &*env.get() };
        if let Node::Fn {
            ident, body, args, ..
        } = &*node
        {
            let f = env.get_func(ident).unwrap();
            self.current_func_ident = Some(ident.clone());
            unsafe { LLVMPositionBuilderAtEnd(self.builder, f.body) };

            let fn_env = unsafe { &mut *f.env.get() };

            for (i, arg) in args.iter().enumerate() {
                let ty = env.get_type(&arg.ty).unwrap();
                let argp = unsafe {
                    LLVMBuildAlloca(
                        self.builder,
                        ty.get_llvm_type(env),
                        "".to_cstring().as_ptr(),
                    )
                };
                unsafe {
                    LLVMBuildStore(
                        self.builder,
                        LLVMGetParam(f.val, i.try_into().unwrap()),
                        argp,
                    )
                };
                fn_env.insert_var(&arg.ident, argp, ty.get_llvm_type(env));
            }

            self.build_block(f.env.clone(), body.clone());
            unsafe { LLVMBuildRetVoid(self.builder) }; // TODO
            self.current_func_ident = None;
        }
    }

    pub fn build_symtable(&mut self, ast: &[NodeRef]) {
        let env = self.env.clone();
        let env = unsafe { &mut *env.get() };
        for node in ast {
            if let Node::Fn {
                ident,
                args: fn_args,
                ret_ty,
                ..
            } = &**node
            {
                let func_ty = env.get_type(ret_ty).unwrap();
                let mut args: Vec<LLVMTypeRef> = Vec::new();
                for arg in fn_args.iter() {
                    let arg_ty = env.get_type(&arg.ty);

                    if let Some(ty) = arg_ty {
                        args.push(ty.get_llvm_type(env));
                    } else {
                        panic!("unresolved type {}", &arg.ty);
                    }
                }
                let func_ty = unsafe {
                    LLVMFunctionType(
                        func_ty.get_llvm_type(env),
                        args.as_mut_slice().as_mut_ptr(),
                        args.len().try_into().unwrap(),
                        0,
                    )
                };
                let val =
                    unsafe { LLVMAddFunction(self.module, ident.to_cstring().as_ptr(), func_ty) };

                let fn_env = Env::make_child(self.env.clone());
                env.insert_func(
                    ident,
                    val,
                    func_ty,
                    Rc::new(UnsafeCell::new(fn_env)),
                    unsafe { LLVMAppendBasicBlock(val, "".to_string().to_cstring().as_ptr()) },
                );
            }
        }
    }

    pub unsafe fn get_llvm_module_ref(&mut self) -> LLVMModuleRef {
        self.module
    }
}

impl Drop for ModuleBuilder {
    fn drop(&mut self) {
        unsafe { LLVMDisposeBuilder(self.builder) };
    }
}
