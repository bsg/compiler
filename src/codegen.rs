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

pub struct Var {
    val: LLVMValueRef,
    ty: LLVMTypeRef,
    is_fn_arg: bool,
}

pub struct Func {
    val: LLVMValueRef,
    ty: LLVMTypeRef,
    env: Rc<UnsafeCell<Env>>,
}

pub struct Env {
    parent: Option<Rc<UnsafeCell<Env>>>,
    vars: HashMap<String, Var>,
    types: HashMap<String, LLVMTypeRef>,
    funcs: HashMap<String, Func>,
}

impl Env {
    pub fn new() -> Self {
        let mut types = HashMap::new();
        types.insert("void".to_owned(), unsafe { LLVMVoidType() });
        types.insert("u32".to_owned(), unsafe { LLVMInt32Type() });
        types.insert("i32".to_owned(), unsafe { LLVMInt32Type() });
        types.insert("*void".to_owned(), unsafe {
            LLVMPointerType(LLVMVoidType(), 0)
        });
        types.insert("*u32".to_owned(), unsafe {
            LLVMPointerType(LLVMInt32Type(), 0)
        });
        types.insert("*i32".to_owned(), unsafe {
            LLVMPointerType(LLVMInt32Type(), 0)
        });

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

    pub fn insert_type(&mut self, ident: &str, ty: LLVMTypeRef) {
        self.types.insert(ident.to_string(), ty);
    }

    pub fn get_type(&self, ident: &str) -> Option<LLVMTypeRef> {
        match self.types.get(ident) {
            Some(ty) => Some(*ty),
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

    pub fn insert_var(&mut self, ident: &str, val: LLVMValueRef, ty: LLVMTypeRef, is_fn_arg: bool) {
        self.vars
            .insert(ident.to_string(), Var { val, ty, is_fn_arg });
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
    ) {
        self.funcs.insert(ident.to_string(), Func { val, ty, env });
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

pub struct ModuleBuilder {
    name: String,
    module: LLVMModuleRef,
    builder: LLVMBuilderRef,
    // because fuck it
    env: Rc<UnsafeCell<Env>>,
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
        }
    }

    fn build_value(&mut self, node: NodeRef) -> LLVMValueRef {
        match &*node {
            Node::Int { value } => {
                // FIXME int type
                // TODO sign extend
                unsafe { LLVMConstInt(LLVMInt32Type(), (*value).try_into().unwrap(), 0) }
            }
            _ => unimplemented!(),
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
        is_ref: bool,
    ) -> LLVMValueRef {
        match &*node {
            Node::Int { .. } => self.build_value(node),
            Node::Ident { name } => unsafe {
                if let Some(var) = (*env.get()).get_var(name) {
                    if is_ref {
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
            _ => unimplemented!(),
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
                        (*env.get()).get_type(ty).unwrap(),
                        "".to_cstring().as_ptr(),
                    );
                    let rhs = self.build_expr(env.clone(), rhs.clone(), false);
                    let ty = (*env.get()).get_type(ty).unwrap();
                    (*env.get()).insert_var(name, reg, ty, false);
                    LLVMBuildStore(self.builder, rhs, reg)
                } else {
                    panic!()
                }
            },
            _ => unimplemented!(),
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
            let entry_block =
                unsafe { LLVMAppendBasicBlock(f.val, "".to_string().to_cstring().as_ptr()) };
            unsafe { LLVMPositionBuilderAtEnd(self.builder, entry_block) };

            let fn_env = unsafe { &mut *f.env.get() };

            for (i, arg) in args.iter().enumerate() {
                let ty = env.get_type(&arg.ty).unwrap();
                let argp = unsafe { LLVMBuildAlloca(self.builder, ty, "".to_cstring().as_ptr()) };
                unsafe {
                    LLVMBuildStore(
                        self.builder,
                        LLVMGetParam(f.val, i.try_into().unwrap()),
                        argp,
                    )
                };
                fn_env.insert_var(&arg.ident, argp, ty, true);
            }

            self.build_block(f.env.clone(), body.clone());
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
                let func_ty_str = env.get_type(ret_ty).unwrap();
                let mut args: Vec<LLVMTypeRef> = Vec::new();
                for arg in fn_args.iter() {
                    let arg_ty = env.get_type(&arg.ty);

                    if let Some(ty) = arg_ty {
                        args.push(ty);
                    } else {
                        panic!("unresolved type {}", &arg.ty);
                    }
                }
                let func_ty = unsafe {
                    LLVMFunctionType(
                        func_ty_str,
                        args.as_mut_slice().as_mut_ptr(),
                        args.len().try_into().unwrap(),
                        0,
                    )
                };
                let val =
                    unsafe { LLVMAddFunction(self.module, ident.to_cstring().as_ptr(), func_ty) };

                let fn_env = Env::make_child(self.env.clone());
                env.insert_func(ident, val, func_ty, Rc::new(UnsafeCell::new(fn_env)));
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
