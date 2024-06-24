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

#[derive(Clone)]
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

    // TODO numeric id
    pub fn id(&self) -> &str {
        match self {
            Type::None => "void",
            Type::Bool => "bool",
            Type::Int { width, signed } => match width {
                8 => {
                    if *signed {
                        "u8"
                    } else {
                        "i8"
                    }
                }
                16 => {
                    if *signed {
                        "u16"
                    } else {
                        "i16"
                    }
                }
                32 => {
                    if *signed {
                        "u32"
                    } else {
                        "i32"
                    }
                }
                64 => {
                    if *signed {
                        "u64"
                    } else {
                        "i64"
                    }
                }
                128 => {
                    if *signed {
                        "u128"
                    } else {
                        "i128"
                    }
                }
                _ => todo!(),
            },
            Type::Ptr { .. } => todo!(),
        }
    }

    pub fn to_ref_type(&self) -> Type {
        Type::Ptr {
            pointee_ty: self.id().into(),
        }
    }
}

pub struct Var {
    val: LLVMValueRef,
    ty: Type,
}

pub struct Func {
    val: LLVMValueRef,
    ty: LLVMTypeRef, // TODO remove if this is the llvm return type and use ret_ty
    ret_ty: Type,
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

    pub fn insert_var(&mut self, ident: &str, val: LLVMValueRef, ty: Type) {
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
        ret_ty: Type,
        env: Rc<UnsafeCell<Env>>,
        body: LLVMBasicBlockRef,
    ) {
        self.funcs.insert(
            ident.to_string(),
            Func {
                val,
                ty,
                ret_ty,
                env,
                body,
            },
        );
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

    fn build_unop(&mut self, env: Rc<UnsafeCell<Env>>, node: NodeRef) -> Val {
        if let Node::UnOp { op, rhs } = &*node {
            match op {
                Op::Ref => {
                    let val = self.build_expr(env, rhs.clone(), true);

                    Val {
                        ty: val.ty.to_ref_type(),
                        llvm_val: val.llvm_val,
                    }
                }
                Op::Deref => unsafe {
                    let val = self.build_expr(env.clone(), rhs.clone(), false);
                    let llvm_val = LLVMBuildLoad2(
                        self.builder,
                        LLVMInt32Type(),
                        val.llvm_val,
                        "".to_cstring().as_ptr(),
                    );

                    let ty = match val.ty {
                        Type::Ptr { pointee_ty } => {
                            (*env.get()).get_type(&pointee_ty).unwrap().clone()
                        }
                        _ => panic!("cannot deref"),
                    };

                    Val { ty, llvm_val }
                },
                _ => todo!(),
            }
        } else {
            todo!()
        }
    }

    fn build_binop(&mut self, env: Rc<UnsafeCell<Env>>, node: NodeRef) -> Val {
        if let Node::BinOp { op, lhs, rhs } = &*node {
            let llvm_val = match op {
                Op::Add => unsafe {
                    let lhs_val = self.build_expr(env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), rhs.clone(), false);
                    LLVMBuildAdd(
                        self.builder,
                        lhs_val.llvm_val,
                        rhs_val.llvm_val,
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Sub => unsafe {
                    let lhs_val = self.build_expr(env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), rhs.clone(), false);
                    LLVMBuildSub(
                        self.builder,
                        lhs_val.llvm_val,
                        rhs_val.llvm_val,
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Mul => unsafe {
                    let lhs_val = self.build_expr(env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), rhs.clone(), false);
                    LLVMBuildMul(
                        self.builder,
                        lhs_val.llvm_val,
                        rhs_val.llvm_val,
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Div => unsafe {
                    let lhs_val = self.build_expr(env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), rhs.clone(), false);
                    // TODO
                    LLVMBuildUDiv(
                        self.builder,
                        lhs_val.llvm_val,
                        rhs_val.llvm_val,
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Eq => unsafe {
                    let lhs_val = self.build_expr(env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), rhs.clone(), false);
                    LLVMBuildICmp(
                        self.builder,
                        llvm_sys::LLVMIntPredicate::LLVMIntEQ, // TODO
                        lhs_val.llvm_val,
                        rhs_val.llvm_val,
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Gt => unsafe {
                    let lhs_val = self.build_expr(env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), rhs.clone(), false);
                    LLVMBuildICmp(
                        self.builder,
                        llvm_sys::LLVMIntPredicate::LLVMIntSGT, // TODO
                        lhs_val.llvm_val,
                        rhs_val.llvm_val,
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Lt => unsafe {
                    let lhs_val = self.build_expr(env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), rhs.clone(), false);
                    LLVMBuildICmp(
                        self.builder,
                        llvm_sys::LLVMIntPredicate::LLVMIntSLT, // TODO
                        lhs_val.llvm_val,
                        rhs_val.llvm_val,
                        "".to_cstring().as_ptr(),
                    )
                },
                Op::Assign => unsafe {
                    match &**lhs {
                        Node::Ident { .. } => {
                            let lhs_val = self.build_expr(env.clone(), lhs.clone(), true);
                            let rhs_val = self.build_expr(env.clone(), rhs.clone(), false);
                            LLVMBuildStore(self.builder, rhs_val.llvm_val, lhs_val.llvm_val)
                        }
                        Node::UnOp {
                            op: Op::Deref,
                            rhs: deref_rhs,
                        } => match &**deref_rhs {
                            Node::Ident { .. } => {
                                let lhs_val = self.build_expr(env.clone(), deref_rhs.clone(), false);
                                let rhs_val = self.build_expr(env.clone(), rhs.clone(), false);
                                LLVMBuildStore(self.builder, rhs_val.llvm_val, lhs_val.llvm_val)
                            }
                            _ => todo!(),
                        },
                        _ => panic!("cannot assign to whatever this is"),
                    }
                },
                _ => unimplemented!(),
            };

            Val {
                ty: (unsafe { &*env.get() }).get_type("u32").unwrap().clone(), // TODO
                llvm_val,
            }
        } else {
            todo!()
        }
    }

    fn build_expr(&mut self, env: Rc<UnsafeCell<Env>>, node: NodeRef, ident_no_load: bool) -> Val {
        match &*node {
            Node::Int { value } => unsafe {
                // FIXME int type
                // TODO sign extend
                let llvm_val = LLVMConstInt(LLVMInt32Type(), (*value).try_into().unwrap(), 0);

                Val {
                    ty: (*env.get()).get_type("u32").unwrap().clone(),
                    llvm_val,
                }
            },
            Node::Bool { value } => unsafe {
                let llvm_val = LLVMConstInt(LLVMInt1Type(), if *value { 1 } else { 0 }, 0);

                Val {
                    ty: (*env.get()).get_type("bool").unwrap().clone(),
                    llvm_val,
                }
            },
            Node::Ident { name } => unsafe {
                if let Some(var) = (*env.get()).get_var(name) {
                    let llvm_val = if ident_no_load {
                        var.val
                    } else {
                        LLVMBuildLoad2(
                            self.builder,
                            var.ty.get_llvm_type(&*env.get()),
                            var.val,
                            "".to_cstring().as_ptr(),
                        )
                    };

                    Val {
                        ty: var.ty.clone(),
                        llvm_val,
                    }
                } else {
                    panic!("unresolved ident {}", name)
                }
            },
            Node::UnOp { .. } => {
                let val = self.build_unop(env, node.clone());

                Val {
                    ty: val.ty,
                    llvm_val: val.llvm_val,
                }
            }
            Node::BinOp { .. } => {
                let val = self.build_binop(env, node.clone());

                Val {
                    ty: val.ty,
                    llvm_val: val.llvm_val,
                }
            }
            Node::Call {
                ident,
                args: arg_exprs,
            } => {
                // TODO LLVMGetNamedFunction for extern fns
                let func = (unsafe { &*env.get() }).get_func(ident).unwrap();
                let mut args: Vec<LLVMValueRef> = Vec::new();
                for arg in arg_exprs.iter() {
                    args.push(self.build_expr(env.clone(), arg.clone(), false).llvm_val);
                }
                let llvm_val = unsafe {
                    LLVMBuildCall2(
                        self.builder,
                        func.ty,
                        func.val,
                        args.as_mut_slice().as_mut_ptr(),
                        args.len().try_into().unwrap(),
                        "".to_cstring().as_ptr(),
                    )
                };

                Val {
                    ty: func.ret_ty.clone(),
                    llvm_val,
                }
            }
            _ => panic!("unimplemented!\n {:?}", node),
        }
    }

    fn build_stmt(&mut self, env: Rc<UnsafeCell<Env>>, node: NodeRef) -> Val {
        match &*node {
            Node::Return { stmt } => {
                let llvm_val = if let Some(rhs) = &stmt {
                    let v = self.build_expr(env.clone(), rhs.clone(), false);
                    unsafe { LLVMBuildRet(self.builder, v.llvm_val) }
                } else {
                    unsafe { LLVMBuildRetVoid(self.builder) }
                };

                Val {
                    ty: unsafe { (*env.get()).get_type("void").unwrap().clone() },
                    llvm_val,
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
                    (*env.get()).insert_var(name, reg, ty.clone());
                    let llvm_val = LLVMBuildStore(self.builder, rhs.llvm_val, reg);

                    Val {
                        ty: ty.clone(),
                        llvm_val,
                    }
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
                        self.build_expr(env.clone(), condition.clone(), false)
                            .llvm_val,
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

                    Val {
                        ty: (*env.get()).get_type("void").unwrap().clone(),
                        llvm_val: cond,
                    }
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
                        self.build_expr(env.clone(), condition.clone(), false)
                            .llvm_val,
                        bb_body,
                        bb_exit,
                    );

                    LLVMPositionBuilderAtEnd(self.builder, bb_body);
                    self.build_block(env.clone(), body.clone());
                    LLVMBuildBr(self.builder, bb_test);

                    LLVMPositionBuilderAtEnd(self.builder, bb_exit);

                    Val {
                        ty: (*env.get()).get_type("void").unwrap().clone(),
                        llvm_val: cond,
                    }
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
                fn_env.insert_var(&arg.ident, argp, ty.clone());
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
                let ret_ty = env.get_type(ret_ty).unwrap();
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
                        ret_ty.get_llvm_type(env),
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
                    ret_ty.clone(),
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
