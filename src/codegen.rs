// TODO see all those Rc<UnsafeCell<_> in fn signatures. maybe pass references instead?
// TODO Scope!
// TODO impl type aliasing and make 'Self' a type alias instead of a new type
// TODO struct literals

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    None,
    Bool,
    Int {
        /// width in bits
        width: usize,
        signed: bool,
    },
    Ptr {
        // TODO make this an Rc<Type>
        pointee_type_id: usize,
    },
    Ref {
        // TODO make this an Rc<Type>
        referent_type_id: usize,
    },
    Struct {
        // TODO make this an Rc<Type>
        type_id: usize,
        field_indices: HashMap<String, usize>,
        field_type_ids: Vec<usize>,
        static_methods: HashMap<String, String>,
        member_methods: HashMap<String, String>,
    },
    Array {
        // TODO make this an Rc<Type>
        elem_type_id: usize,
        len: usize,
    },
}

impl Type {
    pub fn llvm_type(&self, type_env: &TypeEnv) -> LLVMTypeRef {
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
            Type::Ref { referent_type_id } => unsafe {
                LLVMPointerType(
                    type_env
                        .get_type_by_id(*referent_type_id)
                        .unwrap()
                        .llvm_type(type_env),
                    0,
                )
            },
            Type::Ptr { pointee_type_id } => unsafe {
                LLVMPointerType(
                    type_env
                        .get_type_by_id(*pointee_type_id)
                        .unwrap()
                        .llvm_type(type_env),
                    0,
                )
            },
            Type::Struct { field_type_ids, .. } => unsafe {
                let mut llvm_types: Vec<LLVMTypeRef> = field_type_ids
                    .iter()
                    .map(|f| type_env.get_type_by_id(*f).unwrap().llvm_type(type_env))
                    .collect();
                // TODO packed
                LLVMStructType(llvm_types.as_mut_ptr(), field_type_ids.len() as u32, 0)
            },
            Type::Array { elem_type_id, len } => unsafe {
                LLVMArrayType2(
                    type_env
                        .get_type_by_id(*elem_type_id)
                        .unwrap()
                        .llvm_type(type_env),
                    *len as u64,
                )
            },
        }
    }

    pub fn id(&self, type_env: &TypeEnv) -> usize {
        match self {
            Type::None => type_env.get_type_id_by_name("void"),
            Type::Bool => type_env.get_type_id_by_name("bool"),
            Type::Int { width, signed } => match width {
                8 => {
                    if *signed {
                        type_env.get_type_id_by_name("u8")
                    } else {
                        type_env.get_type_id_by_name("i8")
                    }
                }
                16 => {
                    if *signed {
                        type_env.get_type_id_by_name("u16")
                    } else {
                        type_env.get_type_id_by_name("i16")
                    }
                }
                32 => {
                    if *signed {
                        type_env.get_type_id_by_name("u32")
                    } else {
                        type_env.get_type_id_by_name("i32")
                    }
                }
                _ => todo!(),
            },
            Type::Ref { .. } => todo!(),
            Type::Ptr { .. } => todo!(),
            Type::Struct { type_id, .. } => *type_id,
            Type::Array { elem_type_id, len } => {
                let elem_ty = type_env.get_type_by_id(*elem_type_id).unwrap();
                type_env.get_type_id_by_name(&format!("[{}; {}]", elem_ty.name(type_env), len))
            }
        }
    }

    pub fn to_ref_type(&self, type_env: &TypeEnv) -> Type {
        Type::Ref {
            referent_type_id: self.id(type_env),
        }
    }

    pub fn name(&self, type_env: &TypeEnv) -> Rc<str> {
        // TODO impl missing
        match self {
            Type::None => "void".into(),
            Type::Bool => "bool".into(),
            Type::Int { width, signed } => match (width, signed) {
                (8, true) => "i8".into(),
                (8, false) => "u8".into(),
                (16, true) => "i16".into(),
                (16, false) => "u16".into(),
                (32, true) => "i32".into(),
                (32, false) => "u32".into(),
                _ => todo!(),
            },
            Type::Ptr { pointee_type_id } => format!(
                "*{}",
                type_env
                    .get_type_by_id(*pointee_type_id)
                    .unwrap()
                    .name(type_env)
            )
            .into(),
            Type::Ref { referent_type_id } => format!(
                "&{}",
                type_env
                    .get_type_by_id(*referent_type_id)
                    .unwrap()
                    .name(type_env)
            )
            .into(),
            Type::Struct { type_id, .. } => {
                type_env.get_type_by_id(*type_id).unwrap().name(type_env)
            }
            Type::Array { elem_type_id, len } => format!(
                "[{}; {}]",
                type_env
                    .get_type_by_id(*elem_type_id)
                    .unwrap()
                    .name(type_env),
                len
            )
            .into(),
        }
    }
}

#[derive(Debug)]
pub struct Var {
    val: LLVMValueRef,
    ty: Type,
}

#[derive(Debug)]
pub struct Func {
    env: Rc<UnsafeCell<Env>>,
    arg_tys: Vec<Type>,
    ret_ty: Type,
    val: LLVMValueRef,
    llvm_ty: LLVMTypeRef, // TODO remove if this is the llvm return type and use ret_ty
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

    pub fn insert_type_by_name(&self, name: &str, ty: Type) -> usize {
        // This should not mutate parents at all. Types are resolvable only within and below the scope they are defined in
        let type_id = self.get_type_id_by_name(name);
        (unsafe { &mut *self.types.get() }).insert(type_id, ty);
        type_id
    }

    // TODO make sure this is sound
    /// reserves id for ident if it's not registered
    fn get_type_id_by_name(&self, name: &str) -> usize {
        // This should not mutate parents at all. Types are resolvable only within and below the scope they are defined in
        match (unsafe { &*self.type_ids.get() }).get(name) {
            Some(type_id) => *type_id,
            None => {
                // FIXME FUCKING HATE THIS
                if name.starts_with('[') {
                    if let Some((elem_ty, len)) = name[1..name.len() - 1].rsplit_once(';') {
                        let type_id = unsafe { NEXT_TYPE_ID };
                        unsafe { NEXT_TYPE_ID += 1 };

                        (unsafe { &mut *self.type_ids.get() }).insert(name.into(), type_id);

                        self.insert_type_by_name(
                            name,
                            Type::Array {
                                elem_type_id: self.get_type_id_by_name(elem_ty),
                                len: str::parse(&len[1..]).unwrap(),
                            },
                        )
                    } else {
                        todo!()
                    }
                } else {
                    let type_id = unsafe { NEXT_TYPE_ID };
                    unsafe { NEXT_TYPE_ID += 1 };

                    (unsafe { &mut *self.type_ids.get() }).insert(name.into(), type_id);
                    type_id
                }
            }
        }
    }

    pub fn get_type_by_id(&self, type_id: usize) -> Option<&Type> {
        match (unsafe { &mut *self.types.get() }).get(&type_id) {
            Some(t) => Some(t),
            None => {
                if let Some(parent) = self.parent.clone() {
                    (unsafe { &*parent.get() }).get_type_by_id(type_id)
                } else {
                    None
                }
            }
        }
    }

    pub fn get_type_by_id_mut(&self, type_id: usize) -> Option<&mut Type> {
        match (unsafe { &mut *self.types.get() }).get_mut(&type_id) {
            Some(t) => Some(t),
            None => {
                if let Some(parent) = self.parent.clone() {
                    (unsafe { &*parent.get() }).get_type_by_id_mut(type_id)
                } else {
                    None
                }
            }
        }
    }

    pub fn get_type_by_name(&self, name: &str) -> Option<&Type> {
        match self.get_type_by_id(self.get_type_id_by_name(name)) {
            Some(ty) => Some(ty),
            None => {
                if name.starts_with('&') {
                    self.insert_type_by_name(
                        name,
                        Type::Ref {
                            referent_type_id: self
                                .get_type_id_by_name(name.strip_prefix('&').unwrap()),
                        },
                    );
                    self.get_type_by_name(name)
                } else if name.starts_with('*') {
                    self.insert_type_by_name(
                        name,
                        Type::Ptr {
                            pointee_type_id: self
                                .get_type_id_by_name(name.strip_prefix('*').unwrap()),
                        },
                    );
                    self.get_type_by_name(name)
                } else if name == "Self" || name == "&Self" {
                    // don't ask parents for Self if it's not defined in the current scope
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
                        Type::Ref {
                            referent_type_id: self
                                .get_type_id_by_name(name.strip_prefix('&').unwrap()),
                        },
                    );
                    self.get_type_by_name_mut(name)
                } else if name == "Self" || name == "&Self" {
                    // don't ask parents for Self if it's not defined in the current scope
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

impl std::fmt::Debug for TypeEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypeEnv")
            .field("parent", &self.parent.clone().map(|p| unsafe { &*p.get() }))
            .field("types", unsafe { &*self.types.get() })
            .field("type_ids", &self.type_ids)
            .finish()
    }
}

#[derive(Debug)]
pub struct ImplEnv {
    env: Rc<UnsafeCell<Env>>,
    type_env: Rc<UnsafeCell<TypeEnv>>,
}

#[derive(Debug)]
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

    // TODO clippy
    #[allow(clippy::too_many_arguments)]
    pub fn insert_func(
        &mut self,
        ident: &str,
        val: LLVMValueRef,
        ty: LLVMTypeRef,
        arg_tys: Vec<Type>,
        ret_ty: Type,
        env: Rc<UnsafeCell<Env>>,
        body: LLVMBasicBlockRef,
    ) {
        self.funcs.insert(
            ident.to_string(),
            Func {
                val,
                llvm_ty: ty,
                ret_ty,
                env,
                body,
                arg_tys,
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
    ty: Type, // TODO this needs to be typeid
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

    fn build_deref_ptr(
        &mut self,
        env: Rc<UnsafeCell<Env>>,
        type_env: Rc<UnsafeCell<TypeEnv>>,
        node: NodeRef,
        as_lvalue: bool,
    ) -> Val {
        unsafe {
            let val = self.build_expr(env.clone(), type_env.clone(), node.clone(), false);
            let ty = match val.ty {
                Type::Ref { referent_type_id } => (*type_env.get())
                    .get_type_by_id(referent_type_id)
                    .unwrap()
                    .clone(),
                Type::Ptr { pointee_type_id } => (*type_env.get())
                    .get_type_by_id(pointee_type_id)
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

    fn build_unop(
        &mut self,
        env: Rc<UnsafeCell<Env>>,
        type_env: Rc<UnsafeCell<TypeEnv>>,
        node: NodeRef,
        as_lvalue: bool,
    ) -> Val {
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

    fn build_binop(
        &mut self,
        env: Rc<UnsafeCell<Env>>,
        type_env: Rc<UnsafeCell<TypeEnv>>,
        node: NodeRef,
        as_lvalue: bool,
    ) -> Val {
        let env_ref = unsafe { &mut *env.get() };
        let type_env_ref = unsafe { &mut *type_env.get() };
        if let Node::BinOp { op, lhs, rhs } = &*node {
            let (llvm_val, ty) = match op {
                Op::Add => unsafe {
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);

                    match (&lhs_val.ty, rhs_val.ty) {
                        (Type::Int { .. }, Type::Int { .. }) => (
                            LLVMBuildAdd(
                                self.builder,
                                lhs_val.llvm_val,
                                rhs_val.llvm_val,
                                "".to_cstring().as_ptr(),
                            ),
                            lhs_val.ty,
                        ),
                        (Type::Ptr { pointee_type_id }, Type::Int { .. }) => {
                            // TODO type check and sext
                            let pointee_ty = type_env_ref.get_type_by_id(*pointee_type_id).unwrap();
                            (
                                LLVMBuildGEP2(
                                    self.builder,
                                    pointee_ty.llvm_type(type_env_ref),
                                    lhs_val.llvm_val,
                                    [rhs_val.llvm_val].as_mut_ptr(),
                                    1,
                                    "".to_cstring().as_ptr(),
                                ),
                                lhs_val.ty,
                            )
                        }
                        _ => todo!(),
                    }
                },
                Op::Sub => unsafe {
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    match (&lhs_val.ty, rhs_val.ty) {
                        (Type::Int { .. }, Type::Int { .. }) => (
                            LLVMBuildSub(
                                self.builder,
                                lhs_val.llvm_val,
                                rhs_val.llvm_val,
                                "".to_cstring().as_ptr(),
                            ),
                            lhs_val.ty,
                        ),
                        (Type::Ptr { pointee_type_id }, Type::Int { .. }) => {
                            // TODO type check and sext
                            let pointee_ty = type_env_ref.get_type_by_id(*pointee_type_id).unwrap();
                            let offset = LLVMBuildNeg(
                                self.builder,
                                rhs_val.llvm_val,
                                "".to_cstring().as_ptr(),
                            );
                            (
                                LLVMBuildGEP2(
                                    self.builder,
                                    pointee_ty.llvm_type(type_env_ref),
                                    lhs_val.llvm_val,
                                    [offset].as_mut_ptr(),
                                    1,
                                    "".to_cstring().as_ptr(),
                                ),
                                lhs_val.ty,
                            )
                        }
                        _ => todo!(),
                    }
                },
                Op::Mul => unsafe {
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
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
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
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
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
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
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
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
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
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
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
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
                            field_type_ids: fields,
                            member_methods,
                            ..
                        } => match &**rhs {
                            Node::Ident { name } => {
                                let field_idx = match field_indices.get(&**name) {
                                    Some(idx) => idx,
                                    None => panic!("no member {}", name),
                                };
                                let field_ty = type_env_ref
                                    .get_type_by_id(*fields.get(*field_idx).unwrap())
                                    .unwrap();
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
                            }
                            Node::Call { ident, args } => {
                                let func_ident = member_methods.get(&ident.to_string()).unwrap();
                                let func = env_ref.get_func(func_ident).unwrap();
                                let self_by_ref =
                                    if let Some(Type::Ref { .. }) = func.arg_tys.first() {
                                        // TODO type checking
                                        true
                                    } else {
                                        false
                                    };

                                let mut args = args.to_vec();
                                if self_by_ref {
                                    // hacky but works, dunno?
                                    args.insert(
                                        0,
                                        Node::UnOp {
                                            op: Op::Ref,
                                            rhs: lhs.clone(),
                                        }
                                        .into(),
                                    )
                                } else {
                                    args.insert(0, lhs.clone());
                                }

                                return self.build_call(
                                    env.clone(),
                                    type_env.clone(),
                                    func_ident,
                                    args.into(),
                                );
                            }
                            _ => todo!(),
                        },
                        _ => todo!(),
                    }
                },
                Op::Index => {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), true);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);

                    match (lhs_val.ty.clone(), rhs_val.ty) {
                        (Type::Array { elem_type_id, .. }, Type::Int { .. }) => {
                            // TODO this and bounds check
                            // if !signed {
                            //     panic!("cannot index with signed int");
                            // }

                            let elem_ty = type_env_ref.get_type_by_id(elem_type_id).unwrap();

                            let ptr = unsafe {
                                LLVMBuildInBoundsGEP2(
                                    self.builder,
                                    lhs_val.ty.llvm_type(type_env_ref),
                                    lhs_val.llvm_val,
                                    [LLVMConstInt(LLVMInt64Type(), 0, 0), rhs_val.llvm_val]
                                        .as_mut_ptr(),
                                    2,
                                    "".to_cstring().as_ptr(),
                                )
                            };
                            (
                                if as_lvalue {
                                    ptr
                                } else {
                                    unsafe {
                                        LLVMBuildLoad2(
                                            self.builder,
                                            elem_ty.llvm_type(type_env_ref),
                                            ptr,
                                            "".to_cstring().as_ptr(),
                                        )
                                    }
                                },
                                elem_ty.clone(),
                            )
                        }
                        _ => todo!(),
                    }
                }
                Op::ScopeRes => match (&**lhs, &**rhs) {
                    // TODO probably not the correct way to do this
                    (
                        Node::Ident { name: type_name },
                        Node::Call {
                            ident: fn_ident,
                            args: fn_args,
                        },
                    ) => {
                        if let Some(Type::Struct { static_methods, .. }) =
                            type_env_ref.get_type_by_name(type_name)
                        {
                            let mangled_name = static_methods.get(&**fn_ident).unwrap();

                            return self.build_call(env, type_env, mangled_name, fn_args.clone());
                        } else {
                            todo!()
                        }
                    }
                    _ => todo!(),
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

    fn build_call(
        &mut self,
        env: Rc<UnsafeCell<Env>>,
        type_env: Rc<UnsafeCell<TypeEnv>>,
        ident: &str,
        arg_exprs: Rc<[NodeRef]>,
    ) -> Val {
        // TODO LLVMGetNamedFunction for extern fns
        let func = (unsafe { &*env.get() }).get_func(ident).unwrap();
        let mut args: Vec<LLVMValueRef> = Vec::new();
        for arg in arg_exprs.iter() {
            args.push(
                self.build_expr(env.clone(), type_env.clone(), arg.clone(), false)
                    .llvm_val,
            );
        }
        let llvm_val = unsafe {
            LLVMBuildCall2(
                self.builder,
                func.llvm_ty,
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

    fn build_expr(
        &mut self,
        env: Rc<UnsafeCell<Env>>,
        type_env: Rc<UnsafeCell<TypeEnv>>,
        node: NodeRef,
        as_lvalue: bool,
    ) -> Val {
        match &*node {
            Node::Int { value } => unsafe {
                // FIXME int type
                // TODO sign extend
                let llvm_val = LLVMConstInt(LLVMInt32Type(), (*value).try_into().unwrap(), 0);

                Val {
                    ty: (*type_env.get()).get_type_by_name("u32").unwrap().clone(),
                    llvm_val,
                }
            },
            Node::Bool { value } => unsafe {
                let llvm_val = LLVMConstInt(LLVMInt1Type(), if *value { 1 } else { 0 }, 0);

                Val {
                    ty: (*type_env.get()).get_type_by_name("bool").unwrap().clone(),
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
            Node::Call { ident, args } => {
                self.build_call(env.clone(), type_env.clone(), ident, args.clone())
            }
            Node::Array { elems } => {
                let elem_vals: Vec<Val> = elems
                    .iter()
                    .map(|elem| self.build_expr(env.clone(), type_env.clone(), elem.clone(), false))
                    .collect();
                let elem_ty = elem_vals.first().unwrap().ty.clone();
                let mut elem_vals: Vec<LLVMValueRef> =
                    elem_vals.iter().map(|elem| elem.llvm_val).collect();
                let llvm_val = unsafe {
                    LLVMConstArray2(
                        elem_ty.llvm_type(&*type_env.get()),
                        elem_vals.as_mut_slice().as_mut_ptr(),
                        elem_vals.len() as u64,
                    )
                };

                Val {
                    ty: Type::Array {
                        elem_type_id: elem_ty.id(unsafe { &*type_env.get() }),
                        len: elem_vals.len(),
                    },
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
                    ty: unsafe { (*type_env.get()).get_type_by_name("void").unwrap().clone() },
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
                        let rhs =
                            self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
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
        args: Rc<[Arg]>,
        ret_ty: Rc<str>,
    ) {
        let type_env_ref = unsafe { &*type_env.get() };
        let ret_ty = match type_env_ref.get_type_by_name(&ret_ty) {
            Some(ty) => ty,
            None => panic!("unresolved type {}", ret_ty),
        };
        let mut arg_tys: Vec<Type> = Vec::new();
        let mut arg_vals: Vec<LLVMTypeRef> = Vec::new();
        for arg in args.iter() {
            let arg_ty = type_env_ref.get_type_by_name(&arg.ty);

            if let Some(ty) = arg_ty {
                arg_tys.push(ty.clone());
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
        let val = unsafe { LLVMAddFunction(self.module, ident.to_cstring().as_ptr(), func_ty) };

        let fn_env = Env::make_child(env.clone());
        // this needs to be global
        (unsafe { &mut *self.env.get() }).insert_func(
            ident,
            val,
            func_ty,
            arg_tys,
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
                    let mut field_types: Vec<usize> = Vec::new();
                    for (idx, field) in fields.iter().enumerate() {
                        field_types.push(type_env.get_type_id_by_name(&field.ty));
                        field_indices.insert(field.ident.to_string(), idx);
                    }
                    let type_id = type_env.get_type_id_by_name(ident);
                    type_env.insert_type_by_name(
                        ident,
                        Type::Struct {
                            type_id,
                            field_indices,
                            field_type_ids: field_types,
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
                                &mangled_name,
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
            if let Node::Impl {
                ident: impl_ty,
                methods,
            } = &**node
            {
                let impl_env = env_ref.get_impl_env_mut(impl_ty).unwrap();
                for method in methods.iter() {
                    if let Node::Fn {
                        ident, args, body, ..
                    } = &**method
                    {
                        let mangled_name = format!("__{}_{}", impl_ty, ident);
                        self.build_fn_2(
                            impl_env.env.clone(),
                            impl_env.type_env.clone(),
                            mangled_name.into(),
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
