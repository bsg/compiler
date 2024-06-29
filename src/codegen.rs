// TODO see all those Rc<UnsafeCell<_> in fn signatures. maybe pass references instead?

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
        pointee_ty: usize,
    },
    Struct {
        type_id: usize,
        field_indices: HashMap<String, usize>,
        fields: Vec<Type>,
        static_methods: HashMap<String, String>,
        member_methods: HashMap<String, String>,
    },
}

impl Type {
    pub fn llvm_type(&self, env: &TypeEnv) -> LLVMTypeRef {
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
                LLVMPointerType(env.get_type_by_id(*pointee_ty).unwrap().llvm_type(env), 0)
            },
            Type::Struct { fields, .. } => unsafe {
                let mut llvm_types: Vec<LLVMTypeRef> =
                    fields.iter().map(|f| f.llvm_type(env)).collect();
                // TODO packed
                LLVMStructType(llvm_types.as_mut_ptr(), fields.len() as u32, 0)
            },
        }
    }

    // TODO numeric id
    pub fn id(&self, env: &TypeEnv) -> usize {
        match self {
            Type::None => env.get_type_id_by_name("void"),
            Type::Bool => env.get_type_id_by_name("bool"),
            Type::Int { width, signed } => match width {
                8 => {
                    if *signed {
                        env.get_type_id_by_name("u8")
                    } else {
                        env.get_type_id_by_name("i8")
                    }
                }
                16 => {
                    if *signed {
                        env.get_type_id_by_name("u16")
                    } else {
                        env.get_type_id_by_name("i16")
                    }
                }
                32 => {
                    if *signed {
                        env.get_type_id_by_name("u32")
                    } else {
                        env.get_type_id_by_name("i32")
                    }
                }
                _ => todo!(),
            },
            Type::Ptr { .. } => todo!(),
            Type::Struct { type_id, .. } => *type_id,
        }
    }

    pub fn to_ref_type(&self, env: &TypeEnv) -> Type {
        Type::Ptr {
            pointee_ty: self.id(env),
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

static mut NEXT_TYPE_ID: usize = 0;

pub struct TypeEnv {
    parent: Option<Rc<UnsafeCell<TypeEnv>>>,
    types: UnsafeCell<HashMap<usize, Type>>,
    type_ids: UnsafeCell<HashMap<String, usize>>,
}

impl TypeEnv {
    pub fn new() -> Self {
        let env = TypeEnv {
            parent: None,
            types: UnsafeCell::new(HashMap::new()),
            type_ids: UnsafeCell::new(HashMap::new()),
        };

        env.insert_type_by_name("void", Type::None);

        // TODO make_int_type macro
        env.insert_type_by_name(
            "u8",
            Type::Int {
                width: 8,
                signed: false,
            },
        );
        env.insert_type_by_name(
            "i8",
            Type::Int {
                width: 8,
                signed: true,
            },
        );
        env.insert_type_by_name(
            "u16",
            Type::Int {
                width: 8,
                signed: false,
            },
        );
        env.insert_type_by_name(
            "i16",
            Type::Int {
                width: 8,
                signed: true,
            },
        );
        env.insert_type_by_name(
            "u32",
            Type::Int {
                width: 32,
                signed: false,
            },
        );
        env.insert_type_by_name(
            "i32",
            Type::Int {
                width: 32,
                signed: true,
            },
        );
        env.insert_type_by_name("bool", Type::Bool);

        env
    }

    pub fn make_child(parent: Rc<UnsafeCell<TypeEnv>>) -> Self {
        TypeEnv {
            parent: Some(parent),
            types: UnsafeCell::new(HashMap::new()),
            type_ids: UnsafeCell::new(HashMap::new()),
        }
    }

    pub fn insert_type_by_name(&self, name: &str, ty: Type) {
        // This should not mutate parents at all. Types are resolvable only within and below the scope they are defined in
        (unsafe { &mut *self.types.get() }).insert(self.get_type_id_by_name(name), ty);
    }

    // TODO make sure this is sound
    /// reserves id for ident if it's not registered
    fn get_type_id_by_name(&self, type_ident: &str) -> usize {
        // This should not mutate parents at all. Types are resolvable only within and below the scope they are defined in
        match (unsafe { &*self.type_ids.get() }).get(type_ident) {
            Some(type_id) => *type_id,
            None => {
                let type_id = unsafe { NEXT_TYPE_ID };
                unsafe { NEXT_TYPE_ID += 1 };

                (unsafe { &mut *self.type_ids.get() }).insert(type_ident.into(), type_id);
                type_id
            }
        }
    }

    pub fn get_type_by_id(&self, type_id: usize) -> Option<&Type> {
        // This is only for local types, do not traverse the parent chain
        (unsafe { &mut *self.types.get() }).get(&type_id)
    }

    pub fn get_type_by_id_mut(&self, type_id: usize) -> Option<&mut Type> {
        // This is only for local types, do not traverse the parent chain
        (unsafe { &mut *self.types.get() }).get_mut(&type_id)
    }

    pub fn get_type_by_name(&self, name: &str) -> Option<&Type> {
        match self.get_type_by_id(self.get_type_id_by_name(name)) {
            Some(ty) => Some(ty),
            None => {
                if name.starts_with('*') {
                    self.insert_type_by_name(
                        name,
                        Type::Ptr {
                            pointee_ty: self.get_type_id_by_name(name.strip_prefix('*').unwrap()),
                        },
                    );
                    self.get_type_by_name(name)
                } else if name == "Self" || name == "*Self" {
                    None
                } else if let Some(parent) = &self.parent {
                    (unsafe { &*parent.get() }).get_type_by_name(name)
                } else {
                    None
                }
            }
        }
    }

    // TODO duplicate code
    pub fn get_type_by_name_mut(&self, name: &str) -> Option<&mut Type> {
        match self.get_type_by_id_mut(self.get_type_id_by_name(name)) {
            Some(ty) => Some(ty),
            None => {
                if name.starts_with('*') {
                    self.insert_type_by_name(
                        name,
                        Type::Ptr {
                            pointee_ty: self.get_type_id_by_name(name.strip_prefix('*').unwrap()),
                        },
                    );
                    self.get_type_by_name_mut(name)
                } else if name == "Self" || name == "*Self" {
                    None
                } else if let Some(parent) = &self.parent {
                    (unsafe { &*parent.get() }).get_type_by_name_mut(name)
                } else {
                    None
                }
            }
        }
    }
}

pub struct ImplEnv {
    env: Rc<UnsafeCell<Env>>,
    type_env: Rc<UnsafeCell<TypeEnv>>,
}

pub struct Env {
    parent: Option<Rc<UnsafeCell<Env>>>,
    vars: HashMap<String, Var>,
    funcs: HashMap<String, Func>,
    // TODO this probably has no business being in here since it's only used to pass info to subsequent passes
    impl_envs: HashMap<String, ImplEnv>,
}

impl Env {
    pub fn new() -> Self {
        Env {
            parent: None,
            vars: HashMap::new(),
            funcs: HashMap::new(),
            impl_envs: HashMap::new(),
        }
    }

    // heh
    pub fn make_child(parent: Rc<UnsafeCell<Env>>) -> Self {
        Env {
            parent: Some(parent),
            vars: HashMap::new(),
            funcs: HashMap::new(),
            impl_envs: HashMap::new(),
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

    // impls are top level statements for now
    pub fn insert_impl_env(&mut self, impl_ident: &str, env: ImplEnv) {
        self.impl_envs.insert(impl_ident.to_string(), env);
    }

    // impls are top level statements for now
    pub fn get_impl_env_mut(&mut self, impl_ident: &str) -> Option<&mut ImplEnv> {
        self.impl_envs.get_mut(impl_ident)
    }
}

// TODO rename
struct Val {
    ty: Type,
    llvm_val: LLVMValueRef,
}

// TODO type_env accessors
pub struct ModuleBuilder {
    module: LLVMModuleRef,
    builder: LLVMBuilderRef,
    // because fuck it
    type_env: Rc<UnsafeCell<TypeEnv>>,
    env: Rc<UnsafeCell<Env>>,
    current_func_ident: Option<Rc<str>>,
}

impl ModuleBuilder {
    pub fn new(name: &str) -> Self {
        let mod_name = name.to_cstring().as_ptr();
        let module = unsafe { LLVMModuleCreateWithName(mod_name) };
        let builder = unsafe { LLVMCreateBuilder() };

        Self {
            module,
            builder,
            type_env: Rc::new(UnsafeCell::new(TypeEnv::new())),
            env: Rc::new(UnsafeCell::new(Env::new())),
            current_func_ident: None,
        }
    }

    fn build_deref_ptr(&mut self, env: Rc<UnsafeCell<Env>>, type_env: Rc<UnsafeCell<TypeEnv>>, node: NodeRef, as_lvalue: bool) -> Val {
        unsafe {
            let val = self.build_expr(env.clone(), type_env.clone(), node.clone(), false);
            let ty = match val.ty {
                Type::Ptr { pointee_ty } => (*type_env.get())
                    .get_type_by_id(pointee_ty)
                    .unwrap()
                    .clone(),
                _ => panic!("cannot deref"),
            };

            let llvm_val = if as_lvalue {
                val.llvm_val
            } else {
                LLVMBuildLoad2(
                    self.builder,
                    LLVMInt32Type(),
                    val.llvm_val,
                    "".to_cstring().as_ptr(),
                )
            };

            Val { ty, llvm_val }
        }
    }

    fn build_unop(&mut self, env: Rc<UnsafeCell<Env>>, type_env: Rc<UnsafeCell<TypeEnv>>, node: NodeRef, as_lvalue: bool) -> Val {
        if let Node::UnOp { op, rhs } = &*node {
            match op {
                Op::Ref => {
                    let val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), true);

                    Val {
                        ty: val.ty.to_ref_type(unsafe { &*type_env.get() }),
                        llvm_val: val.llvm_val,
                    }
                }
                Op::Deref => self.build_deref_ptr(env, type_env, rhs.clone(), as_lvalue),
                _ => todo!(),
            }
        } else {
            todo!()
        }
    }

    fn build_binop(&mut self, env: Rc<UnsafeCell<Env>>, type_env: Rc<UnsafeCell<TypeEnv>>, node: NodeRef, as_lvalue: bool) -> Val {
        let type_env_ref = unsafe { &mut *type_env.get() };
        if let Node::BinOp { op, lhs, rhs } = &*node {
            let (llvm_val, ty) = match op {
                Op::Add => unsafe {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    (
                        LLVMBuildAdd(
                            self.builder,
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        type_env_ref.get_type_by_name("u32").unwrap().clone(),
                    )
                },
                Op::Sub => unsafe {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    (
                        LLVMBuildSub(
                            self.builder,
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        type_env_ref.get_type_by_name("u32").unwrap().clone(),
                    )
                },
                Op::Mul => unsafe {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    (
                        LLVMBuildMul(
                            self.builder,
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        type_env_ref.get_type_by_name("u32").unwrap().clone(),
                    )
                },
                Op::Div => unsafe {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    // TODO
                    (
                        LLVMBuildUDiv(
                            self.builder,
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        type_env_ref.get_type_by_name("u32").unwrap().clone(),
                    )
                },
                Op::Eq => unsafe {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    (
                        LLVMBuildICmp(
                            self.builder,
                            llvm_sys::LLVMIntPredicate::LLVMIntEQ,
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        type_env_ref.get_type_by_name("bool").unwrap().clone(),
                    )
                },
                Op::Gt => unsafe {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    (
                        LLVMBuildICmp(
                            self.builder,
                            llvm_sys::LLVMIntPredicate::LLVMIntSGT, // TODO
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        type_env_ref.get_type_by_name("bool").unwrap().clone(),
                    )
                },
                Op::Lt => unsafe {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    (
                        LLVMBuildICmp(
                            self.builder,
                            llvm_sys::LLVMIntPredicate::LLVMIntSLT, // TODO
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        type_env_ref.get_type_by_name("bool").unwrap().clone(),
                    )
                },
                Op::Assign => unsafe {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), true);
                    let rhs_val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    (
                        LLVMBuildStore(self.builder, rhs_val.llvm_val, lhs_val.llvm_val),
                        type_env_ref.get_type_by_name("void").unwrap().clone(),
                    )
                },
                Op::Dot => unsafe {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), true);
                    match lhs_val.ty.clone() {
                        Type::Struct {
                            field_indices,
                            fields,
                            ..
                        } => {
                            if let Node::Ident { name } = &**rhs {
                                let field_idx = match field_indices.get(&**name) {
                                    Some(idx) => idx,
                                    None => panic!("no member {}", name),
                                };
                                let field_ty = fields.get(*field_idx).unwrap();
                                let ptr = LLVMBuildStructGEP2(
                                    self.builder,
                                    lhs_val.ty.llvm_type(type_env_ref),
                                    lhs_val.llvm_val,
                                    *field_idx as u32,
                                    "".to_cstring().as_ptr(),
                                );

                                if as_lvalue {
                                    (ptr, field_ty.clone())
                                } else {
                                    (
                                        LLVMBuildLoad2(
                                            self.builder,
                                            field_ty.llvm_type(type_env_ref),
                                            ptr,
                                            "".to_cstring().as_ptr(),
                                        ),
                                        field_ty.clone(),
                                    )
                                }
                            } else {
                                todo!()
                            }
                        }
                        _ => todo!(),
                    }
                },
                _ => todo!(),
            };

            Val {
                ty, // TODO
                llvm_val,
            }
        } else {
            todo!()
        }
    }

    fn build_expr(&mut self, env: Rc<UnsafeCell<Env>>, type_env: Rc<UnsafeCell<TypeEnv>>, node: NodeRef, as_lvalue: bool) -> Val {
        match &*node {
            Node::Int { value } => unsafe {
                // FIXME int type
                // TODO sign extend
                let llvm_val = LLVMConstInt(LLVMInt32Type(), (*value).try_into().unwrap(), 0);

                Val {
                    ty: (*type_env.get())
                        .get_type_by_name("u32")
                        .unwrap()
                        .clone(),
                    llvm_val,
                }
            },
            Node::Bool { value } => unsafe {
                let llvm_val = LLVMConstInt(LLVMInt1Type(), if *value { 1 } else { 0 }, 0);

                Val {
                    ty: (*type_env.get())
                        .get_type_by_name("bool")
                        .unwrap()
                        .clone(),
                    llvm_val,
                }
            },
            Node::Ident { name } => unsafe {
                if let Some(var) = (*env.get()).get_var(name) {
                    let llvm_val = if as_lvalue {
                        var.val
                    } else {
                        LLVMBuildLoad2(
                            self.builder,
                            var.ty.llvm_type(&*type_env.get()),
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
                let val = self.build_unop(env, type_env, node.clone(), as_lvalue);

                Val {
                    ty: val.ty,
                    llvm_val: val.llvm_val,
                }
            }
            Node::BinOp { .. } => {
                let val = self.build_binop(env, type_env.clone(), node.clone(), as_lvalue);

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
                    args.push(self.build_expr(env.clone(), type_env.clone(), arg.clone(), false).llvm_val);
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

    fn build_stmt(
        &mut self,
        env: Rc<UnsafeCell<Env>>,
        type_env: Rc<UnsafeCell<TypeEnv>>,
        node: NodeRef,
    ) -> Val {
        match &*node {
            Node::Return { stmt } => {
                let llvm_val = if let Some(rhs) = &stmt {
                    let v = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    unsafe { LLVMBuildRet(self.builder, v.llvm_val) }
                } else {
                    unsafe { LLVMBuildRetVoid(self.builder) }
                };

                Val {
                    ty: unsafe {
                        (*type_env.get())
                            .get_type_by_name("void")
                            .unwrap()
                            .clone()
                    },
                    llvm_val,
                }
            }
            Node::Let { ty, lhs, rhs } => unsafe {
                // TODO alloca the var and let assign do the rest?
                if let Node::Ident { name } = &**lhs {
                    let ty = match (*type_env.get()).get_type_by_name(ty) {
                        Some(t) => t,
                        None => panic!("unknown type {}", ty),
                    };
                    let reg = LLVMBuildAlloca(
                        self.builder,
                        ty.llvm_type(&*(*type_env).get()),
                        "".to_cstring().as_ptr(),
                    );

                    (*env.get()).insert_var(name, reg, ty.clone());

                    if let Some(rhs) = rhs {
                        let rhs = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                        LLVMBuildStore(self.builder, rhs.llvm_val, reg);
                    };

                    // TODO llvm_val should be optional
                    Val {
                        ty: Type::None,
                        llvm_val: LLVMConstInt(LLVMInt1Type(), 0, 0),
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
                    let current_func = (*env.get()).get_func(fn_ident).unwrap();

                    // FIXME i hate the ordering of nested blocks in the IR. need to build depth first
                    let bb_then = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    let bb_else = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    let bb_exit = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    let cond = LLVMBuildCondBr(
                        self.builder,
                        self.build_expr(env.clone(), type_env.clone(), condition.clone(), false)
                            .llvm_val,
                        bb_then,
                        bb_else,
                    );

                    LLVMPositionBuilderAtEnd(self.builder, bb_then);
                    self.build_block(env.clone(), type_env.clone(), then_block.clone());
                    LLVMBuildBr(self.builder, bb_exit);

                    LLVMPositionBuilderAtEnd(self.builder, bb_else);
                    if let Some(else_block) = else_block {
                        self.build_block(env.clone(), type_env.clone(), else_block.clone());
                    }
                    LLVMBuildBr(self.builder, bb_exit);

                    LLVMPositionBuilderAtEnd(self.builder, bb_exit);

                    Val {
                        ty: (*type_env.get()).get_type_by_name("void").unwrap().clone(),
                        llvm_val: cond,
                    }
                } else {
                    panic!("if stmt outside fn")
                }
            },
            Node::While { condition, body } => unsafe {
                if let Some(fn_ident) = &self.current_func_ident {
                    let current_func = (*env.get()).get_func(fn_ident).unwrap();

                    // FIXME i hate the ordering of nested blocks in the IR. need to build depth first
                    let bb_test = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    LLVMBuildBr(self.builder, bb_test);
                    let bb_body = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    let bb_exit = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());

                    LLVMPositionBuilderAtEnd(self.builder, bb_test);
                    let cond = LLVMBuildCondBr(
                        self.builder,
                        self.build_expr(env.clone(), type_env.clone(), condition.clone(), false)
                            .llvm_val,
                        bb_body,
                        bb_exit,
                    );

                    LLVMPositionBuilderAtEnd(self.builder, bb_body);
                    self.build_block(env.clone(), type_env.clone(), body.clone());
                    LLVMBuildBr(self.builder, bb_test);

                    LLVMPositionBuilderAtEnd(self.builder, bb_exit);

                    Val {
                        ty: (*type_env.get()).get_type_by_name("void").unwrap().clone(),
                        llvm_val: cond,
                    }
                } else {
                    panic!("while stmt outside fn")
                }
            },
            _ => self.build_expr(env, type_env.clone(), node, false),
        }
    }

    fn build_block(
        &mut self,
        env: Rc<UnsafeCell<Env>>,
        type_env: Rc<UnsafeCell<TypeEnv>>,
        node: NodeRef,
    ) {
        if let Node::Block { statements } = &*node {
            for stmt in statements.iter() {
                self.build_stmt(env.clone(), type_env.clone(), stmt.clone());
            }
        } else {
            panic!()
        }
    }

    // TODO rename
    fn build_fn_1(
        &mut self,
        env: Rc<UnsafeCell<Env>>,
        type_env: Rc<UnsafeCell<TypeEnv>>,
        ident: &str,
        mangled_name: Option<&str>,
        args: Rc<[Arg]>,
        ret_ty: Rc<str>,
    ) {
        let env_ref = unsafe { &mut *env.get() };
        let type_env_ref = unsafe { &*type_env.get() };
        let ret_ty = match type_env_ref.get_type_by_name(&ret_ty) {
            Some(ty) => ty,
            None => panic!("unresolved type {}", ret_ty),
        };
        let mut arg_vals: Vec<LLVMTypeRef> = Vec::new();
        for arg in args.iter() {
            let arg_ty = type_env_ref.get_type_by_name(&arg.ty);

            if let Some(ty) = arg_ty {
                arg_vals.push(ty.llvm_type(type_env_ref));
            } else {
                panic!("unresolved type {}", &arg.ty);
            }
        }
        let func_ty = unsafe {
            LLVMFunctionType(
                ret_ty.llvm_type(&*type_env.get()),
                arg_vals.as_mut_slice().as_mut_ptr(),
                arg_vals.len().try_into().unwrap(),
                0,
            )
        };
        let val = unsafe {
            LLVMAddFunction(
                self.module,
                mangled_name.unwrap_or(ident).to_cstring().as_ptr(),
                func_ty,
            )
        };

        let fn_env = Env::make_child(env.clone());
        env_ref.insert_func(
            ident,
            val,
            func_ty,
            ret_ty.clone(),
            Rc::new(UnsafeCell::new(fn_env)),
            unsafe { LLVMAppendBasicBlock(val, "".to_string().to_cstring().as_ptr()) },
        );
    }

    // TODO rename
    fn build_fn_2(
        &mut self,
        env: Rc<UnsafeCell<Env>>,
        type_env: Rc<UnsafeCell<TypeEnv>>,
        ident: Rc<str>,
        args: Rc<[Arg]>,
        body: NodeRef,
    ) {
        let type_env_ref = unsafe { &*type_env.get() };
        let env_ref = unsafe { &*env.get() };
        let func = env_ref.get_func(&ident).unwrap();
        self.current_func_ident = Some(ident.clone());
        unsafe { LLVMPositionBuilderAtEnd(self.builder, func.body) };

        let fn_env = unsafe { &mut *func.env.get() };

        for (i, arg) in args.iter().enumerate() {
            let ty = type_env_ref.get_type_by_name(&arg.ty).unwrap();
            let argp = unsafe {
                LLVMBuildAlloca(
                    self.builder,
                    ty.llvm_type(type_env_ref),
                    "".to_cstring().as_ptr(),
                )
            };
            unsafe {
                LLVMBuildStore(
                    self.builder,
                    LLVMGetParam(func.val, i.try_into().unwrap()),
                    argp,
                )
            };
            fn_env.insert_var(&arg.ident, argp, ty.clone());
        }

        self.build_block(func.env.clone(), type_env.clone(), body.clone());
        unsafe { LLVMBuildRetVoid(self.builder) }; // TODO
        self.current_func_ident = None;
    }

    fn pass1(&mut self, ast: &[NodeRef]) {
        let type_env = self.type_env.clone();
        let type_env = unsafe { &mut *type_env.get() };

        for node in ast {
            match &**node {
                Node::Fn {
                    ident,
                    args,
                    ret_ty,
                    ..
                } => self.build_fn_1(
                    self.env.clone(),
                    self.type_env.clone(),
                    ident,
                    None,
                    args.clone(),
                    ret_ty.clone(),
                ),
                Node::Struct { ident, .. } => {
                    type_env.get_type_id_by_name(ident);
                }
                _ => (),
            }
        }
    }

    fn pass2(&mut self, ast: &[NodeRef]) {
        let env = self.env.clone();
        let env = unsafe { &mut *env.get() };
        let type_env = self.type_env.clone();
        let type_env = unsafe { &mut *type_env.get() };

        for node in ast.iter() {
            match &**node {
                Node::Fn {
                    ident, body, args, ..
                } => self.build_fn_2(
                    self.env.clone(),
                    self.type_env.clone(),
                    ident.clone(),
                    args.clone(),
                    body.clone(),
                ),
                Node::Struct { ident, fields } => {
                    // TODO build a dependency tree and gen structs depth first
                    let mut field_indices: HashMap<String, usize> = HashMap::new();
                    let mut field_types: Vec<Type> = Vec::new();
                    for (idx, field) in fields.iter().enumerate() {
                        field_types.push(type_env.get_type_by_name(&field.ty).unwrap().clone());
                        field_indices.insert(field.ident.to_string(), idx);
                    }
                    let type_id = type_env.get_type_id_by_name(ident);
                    type_env.insert_type_by_name(
                        ident,
                        Type::Struct {
                            type_id,
                            field_indices,
                            fields: field_types,
                            static_methods: HashMap::new(),
                            member_methods: HashMap::new(),
                        },
                    );
                }
                Node::Impl {
                    ident: impl_ty,
                    methods,
                } => {
                    let local_env = Rc::new(UnsafeCell::new(Env::make_child(self.env.clone())));
                    let local_type_env =
                        Rc::new(UnsafeCell::new(TypeEnv::make_child(self.type_env.clone())));
                    let local_type_env_ref = unsafe { &mut *local_type_env.get() };

                    local_type_env_ref.insert_type_by_name(
                        "Self",
                        type_env.get_type_by_name(impl_ty).unwrap().clone(),
                    );

                    let (static_methods, member_methods) = if let Some(Type::Struct {
                        static_methods,
                        member_methods,
                        ..
                    }) =
                        type_env.get_type_by_name_mut(impl_ty)
                    {
                        (static_methods, member_methods)
                    } else {
                        todo!();
                    };

                    for method in methods.iter() {
                        if let Node::Fn {
                            ident: method_name,
                            args,
                            ret_ty,
                            ..
                        } = &**method
                        {
                            let is_static = if let Some(arg) = args.first() {
                                !(&*arg.ty != "Self" || &*arg.ty != "*Self")
                            } else {
                                true
                            };

                            let mangled_name = format!("__{}_{}", impl_ty, method_name);

                            if is_static {
                                static_methods
                                    .insert(method_name.to_string(), mangled_name.clone());
                            } else {
                                member_methods
                                    .insert(method_name.to_string(), mangled_name.clone());
                            }

                            self.build_fn_1(
                                local_env.clone(),
                                local_type_env.clone(),
                                method_name,
                                Some(&mangled_name),
                                args.clone(),
                                ret_ty.clone(),
                            );
                        } else {
                            todo!()
                        }
                    }

                    env.insert_impl_env(
                        impl_ty,
                        ImplEnv {
                            env: local_env.clone(),
                            type_env: local_type_env.clone(),
                        },
                    )
                }
                _ => (),
            }
        }
    }

    fn pass3(&mut self, ast: &[NodeRef]) {
        let env = self.env.clone();
        let env_ref = unsafe { &mut *env.get() };

        for node in ast.iter() {
            if let Node::Impl { ident, methods } = &**node {
                let impl_env = env_ref.get_impl_env_mut(ident).unwrap();
                for method in methods.iter() {
                    if let Node::Fn {
                        ident, args, body, ..
                    } = &**method
                    {
                        self.build_fn_2(
                            impl_env.env.clone(),
                            impl_env.type_env.clone(),
                            ident.clone(),
                            args.clone(),
                            body.clone(),
                        )
                    } else {
                        todo!()
                    }
                }
            }
        }
    }

    pub fn build(&mut self, ast: &[NodeRef]) {
        self.pass1(ast);
        self.pass2(ast);
        self.pass3(ast);
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
