// TODO Scope!
// TODO impl type aliasing and make 'Self' a type alias instead of a new type
// TODO struct literals
// TODO Fn type
// TODO check return values of llvm-sys function calls
// TODO LLVMVerifyFunction
// TODO break/continue
// TODO check if variable shadowing works as intended
// TODO type id's should be global. think of type names as aliases into type ids
// TODO llvm type aliases for compound types
// FIXME top level consts dependent will not resolve compound types on account of type not being available
// when the const is being generated
// TODO intern strings
// TODO struct default values
// FIXME function pointer related stuff resulted in a lot of duplicate code
// FIXME attributes are fucked
// TODO explicitly tagged unions, with #[explicitly_tagged] on the union and #[tag=...] on the variant?
// TODO https://doc.rust-lang.org/reference/expressions/struct-expr.html#functional-update-syntax
// FIXME assigning a struct to another seems to 'move' it instead of copying it
// FIXME sizeof doesn't seem to work for structs

use llvm_sys::core::*;
use llvm_sys::prelude::*;
use llvm_sys::target::LLVMCreateTargetData;
use llvm_sys::target::LLVMPointerSize;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::ffi::CString;
use std::ptr::null_mut;
use std::rc::Rc;

use crate::ast::*;
use crate::type_collector::TypeCollector;

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

// TODO attach id and llvm type to the variants
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
        pointee_type_name: Rc<String>,
    },
    Ref {
        referent_type_name: Rc<String>,
    },
    Struct {
        name: Rc<String>,
        field_indices: HashMap<String, usize>,
        field_type_names: Vec<Rc<String>>,
        generics: Rc<[Rc<str>]>,
        static_methods: HashMap<String, String>,
        member_methods: HashMap<String, String>,
        attributes: Option<Rc<[Rc<str>]>>,
    },
    Array {
        elem_type_name: Rc<String>,
        len: usize,
    },
    Fn {
        arg_types: Vec<String>,
        ret_type: String,
    },
}

impl Type {
    pub fn llvm_type(&self, type_env: Rc<TypeEnv>) -> LLVMTypeRef {
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
            Type::Ref { referent_type_name } => unsafe {
                if let Some(ty) = type_env.get_type_by_name(referent_type_name) {
                    LLVMPointerType(ty.llvm_type(type_env.clone()), 0)
                } else {
                    // TODO this and similar needs to be propagated up
                    panic!("unresolved type {}", referent_type_name);
                }
            },
            Type::Ptr { pointee_type_name } => unsafe {
                if let Some(ty) = type_env.get_type_by_name(pointee_type_name) {
                    LLVMPointerType(ty.llvm_type(type_env.clone()), 0)
                } else {
                    panic!(
                        "unresolved type {} = {:?}",
                        pointee_type_name,
                        type_env.get_type_by_name(pointee_type_name)
                    );
                }
            },
            Type::Struct {
                name,
                field_type_names,
                attributes,
                ..
            } => unsafe {
                let type_env = if let Some(env) = type_env.get_impl_env_mut(name) {
                    env.type_env.clone()
                } else {
                    type_env
                };
                let mut llvm_types: Vec<LLVMTypeRef> = field_type_names
                    .iter()
                    .map(|f| {
                        if let Some(ty) = type_env.get_type_by_name(f) {
                            if let Type::Fn { .. } = ty {
                                LLVMPointerType(ty.llvm_type(type_env.clone()), 0)
                            } else {
                                ty.llvm_type(type_env.clone())
                            }
                        } else {
                            panic!("unresolved type id {}", *f)
                        }
                    })
                    .collect();

                let mut packed = 0;

                if let Some(attributes) = attributes {
                    for attr in attributes.iter() {
                        if &**attr == "packed" {
                            packed = 1;
                        }
                    }
                };

                LLVMStructType(
                    llvm_types.as_mut_ptr(),
                    field_type_names.len() as u32,
                    packed,
                )
            },
            Type::Array {
                elem_type_name,
                len,
            } => unsafe {
                LLVMArrayType2(
                    type_env
                        .get_type_by_name(elem_type_name)
                        .unwrap()
                        .llvm_type(type_env.clone()),
                    *len as u64,
                )
            },
            Type::Fn {
                arg_types,
                ret_type,
            } => {
                let mut llvm_arg_types: Vec<LLVMTypeRef> = Vec::new();
                for arg_type in arg_types {
                    llvm_arg_types.push(
                        type_env
                            .get_type_by_name(arg_type)
                            .unwrap()
                            .llvm_type(type_env.clone()),
                    )
                }

                unsafe {
                    LLVMFunctionType(
                        type_env
                            .clone()
                            .get_type_by_name(ret_type)
                            .unwrap()
                            .llvm_type(type_env),
                        llvm_arg_types.as_mut_slice().as_mut_ptr(),
                        llvm_arg_types.len() as u32,
                        0,
                    )
                }
            }
        }
    }

    pub fn to_ref_type(&self) -> Type {
        Type::Ref {
            referent_type_name: Rc::new(self.name().to_string()),
        }
    }

    pub fn name(&self) -> Rc<String> {
        // TODO impl missing
        match self {
            Type::None => "void".to_string().into(),
            Type::Bool => "bool".to_string().into(),
            Type::Int { width, signed } => match (width, signed) {
                (8, true) => "i8".to_string().into(),
                (8, false) => "u8".to_string().into(),
                (16, true) => "i16".to_string().into(),
                (16, false) => "u16".to_string().into(),
                (32, true) => "i32".to_string().into(),
                (32, false) => "u32".to_string().into(),
                (64, true) => "i64".to_string().into(),
                (64, false) => "u64".to_string().into(),
                _ => todo!(),
            },
            Type::Ptr { pointee_type_name } => format!("*{}", pointee_type_name).into(),
            Type::Ref { referent_type_name } => format!("&{}", referent_type_name).into(),
            Type::Struct { name, .. } => name.clone(),
            Type::Array {
                elem_type_name,
                len,
            } => format!("[{}; {}]", elem_type_name, len).into(),
            Type::Fn {
                arg_types,
                ret_type,
            } => format!("fn({}) -> {}", arg_types.join(","), ret_type).into(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Var {
    val: LLVMValueRef,
    ty: Type,
    is_const: bool,
}

#[derive(Debug)]
pub struct Func {
    ty: Type,
    env: Rc<Env>,
    arg_tys: Vec<Type>, // TODO should not be necessary because we have ty
    ret_ty: Type,       // TODO should not be necessary because we have ty
    val: LLVMValueRef,
    llvm_ty: LLVMTypeRef, // TODO not necessary because we have ty
    // TODO group these two together
    bb_entry: Option<LLVMBasicBlockRef>,
    bb_body: Option<LLVMBasicBlockRef>,
}

static mut NEXT_TYPE_ID: usize = 0;

pub struct TypeEnv {
    llvm_module_ref: LLVMModuleRef,
    parent: Option<Rc<TypeEnv>>,
    types: UnsafeCell<HashMap<usize, Type>>,
    type_ids: UnsafeCell<HashMap<String, usize>>,
    // TODO this should hold something like a GenericType instead of Type
    generic_types: UnsafeCell<HashMap<String, NodeRef>>,
    generic_impls: UnsafeCell<HashMap<String, NodeRef>>,
    generic_impl_instances: UnsafeCell<Vec<(String, Vec<Rc<str>>)>>,
    impl_envs: UnsafeCell<HashMap<String, ImplEnv>>,
}

impl TypeEnv {
    pub fn new(llvm_module_ref: LLVMModuleRef) -> Self {
        let env = TypeEnv {
            llvm_module_ref,
            parent: None,
            types: UnsafeCell::new(HashMap::new()),
            type_ids: UnsafeCell::new(HashMap::new()),
            generic_types: UnsafeCell::new(HashMap::new()),
            generic_impls: UnsafeCell::new(HashMap::new()),
            generic_impl_instances: UnsafeCell::new(Vec::new()),
            impl_envs: UnsafeCell::new(HashMap::new()),
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
        env.insert_type_by_name(
            "u64",
            Type::Int {
                width: 64,
                signed: false,
            },
        );
        env.insert_type_by_name(
            "i64",
            Type::Int {
                width: 64,
                signed: true,
            },
        );
        env.insert_type_by_name(
            "isize",
            Type::Int {
                width: unsafe {
                    LLVMPointerSize(LLVMCreateTargetData(LLVMGetDataLayoutStr(llvm_module_ref)))
                        as usize
                } * 8,
                signed: true,
            },
        );
        env.insert_type_by_name(
            "usize",
            Type::Int {
                width: unsafe {
                    LLVMPointerSize(LLVMCreateTargetData(LLVMGetDataLayoutStr(llvm_module_ref)))
                        as usize
                } * 8,
                signed: false,
            },
        );

        env.insert_type_by_name("bool", Type::Bool);

        env
    }

    pub fn make_child(parent: Rc<TypeEnv>) -> Self {
        TypeEnv {
            llvm_module_ref: parent.llvm_module_ref,
            parent: Some(parent),
            types: UnsafeCell::new(HashMap::new()),
            type_ids: UnsafeCell::new(HashMap::new()),
            generic_types: UnsafeCell::new(HashMap::new()),
            generic_impls: UnsafeCell::new(HashMap::new()),
            generic_impl_instances: UnsafeCell::new(Vec::new()),
            impl_envs: UnsafeCell::new(HashMap::new()),
        }
    }

    pub fn insert_type_by_name(&self, name: &str, ty: Type) -> usize {
        // This should not mutate parents at all. Types are resolvable only within and below the scope they are defined in
        let type_id = unsafe { NEXT_TYPE_ID };
        unsafe { NEXT_TYPE_ID += 1 };
        (unsafe { &mut *self.type_ids.get() }).insert(name.to_string(), type_id);
        (unsafe { &mut *self.types.get() }).insert(type_id, ty);
        type_id
    }

    // FIXME the entire thing is cursed
    // TODO make sure this is sound
    /// reserves id for ident if it's not registered
    fn get_type_id_by_name(&self, name: &str) -> usize {
        // TODO this will be a fucking problem because it will reserve id for type ident not available locally
        // but available in a parent, resulting in multiple different id's corresponding to the same type.
        // do lookup in parents before you reserve a local id
        // TODO also make this not reserve id and impl a get_or_reserve_type_id_by_name

        let type_id = unsafe { &*self.type_ids.get() }.get(name).copied();
        // This should not mutate parents at all. Types are resolvable only within and below the scope they are defined in
        let id = match type_id {
            Some(type_id) => type_id,
            None => {
                let name = if name.contains('<') {
                    let (ident, generics) = name.split_once('<').unwrap();
                    let mut types: Vec<String> = Vec::new();
                    for ty_arg in generics.trim_end_matches('>').split(',') {
                        if let Some(ty) = self.get_type_by_name(ty_arg) {
                            types.push(ty.name().to_string());
                        } else {
                            types.push(ty_arg.to_string());
                        }
                    }
                    format!("{}<{}>", ident, &types.join(","))
                } else {
                    name.to_string()
                };

                // FIXME FUCKING HATE THIS
                if name.starts_with('[') {
                    if let Some((elem_ty, len)) = name[1..name.len() - 1].rsplit_once(';') {
                        let type_id = unsafe { NEXT_TYPE_ID };
                        unsafe { NEXT_TYPE_ID += 1 };

                        (unsafe { &mut *self.type_ids.get() }).insert(name.clone(), type_id);

                        self.insert_type_by_name(
                            &name,
                            Type::Array {
                                elem_type_name: elem_ty.to_string().into(),
                                len: str::parse(&len[1..]).unwrap(),
                            },
                        )
                    } else {
                        todo!()
                    }
                } else if name.starts_with('&') {
                    self.insert_type_by_name(
                        &name,
                        Type::Ref {
                            referent_type_name: name.strip_prefix('&').unwrap().to_string().into(),
                        },
                    )
                } else if name.starts_with('*') {
                    self.insert_type_by_name(
                        &name,
                        Type::Ptr {
                            pointee_type_name: name.strip_prefix('*').unwrap().to_string().into(),
                        },
                    )
                } else if name.starts_with("fn(") {
                    let (arg_types_str, ret_type) = name
                        .split_once("fn(")
                        .unwrap()
                        .1
                        .rsplit_once(") -> ")
                        .unwrap();
                    let mut arg_types: Vec<String> = Vec::new();
                    if !arg_types_str.is_empty() {
                        for arg_type in arg_types_str.split(',') {
                            arg_types.push(arg_type.to_string())
                        }
                    }

                    self.insert_type_by_name(
                        &name,
                        Type::Fn {
                            arg_types,
                            ret_type: ret_type.to_string(),
                        },
                    )
                } else if let Some(p) = &self.parent {
                    p.get_type_id_by_name(&name)
                } else {
                    let type_id = unsafe { NEXT_TYPE_ID };
                    unsafe { NEXT_TYPE_ID += 1 };

                    (unsafe { &mut *self.type_ids.get() }).insert(name, type_id);
                    type_id
                }
            }
        };
        id
    }

    fn get_type_by_id(&self, type_id: usize) -> Option<&Type> {
        match (unsafe { &mut *self.types.get() }).get(&type_id) {
            Some(t) => Some(t),
            None => {
                if let Some(parent) = &self.parent {
                    parent.get_type_by_id(type_id)
                } else {
                    None
                }
            }
        }
    }

    fn get_type_by_id_mut(&self, type_id: usize) -> Option<&mut Type> {
        match (unsafe { &mut *self.types.get() }).get_mut(&type_id) {
            Some(t) => Some(t),
            None => {
                if let Some(parent) = &self.parent {
                    parent.get_type_by_id_mut(type_id)
                } else {
                    None
                }
            }
        }
    }

    pub fn get_type_by_name(&self, name: &str) -> Option<&Type> {
        self.get_type_by_id(self.get_type_id_by_name(name))
    }

    pub fn get_type_by_name_mut(&self, name: &str) -> Option<&mut Type> {
        self.get_type_by_id_mut(self.get_type_id_by_name(name))
    }

    pub fn insert_generic_type(&self, ident: String, node: NodeRef) {
        (unsafe { &mut *self.generic_types.get() }).insert(ident, node);
    }

    pub fn get_generic_type(&self, ident: &String) -> Option<&mut NodeRef> {
        match (unsafe { &mut *self.generic_types.get() }).get_mut(ident) {
            Some(t) => Some(t),
            None => {
                if let Some(parent) = &self.parent {
                    parent.get_generic_type(ident)
                } else {
                    None
                }
            }
        }
    }

    pub fn insert_generic_impl(&self, ident: Rc<str>, ty: NodeRef) {
        (unsafe { &mut *self.generic_impls.get() }).insert(ident.to_string(), ty);
    }

    pub fn get_generic_impl(&self, ident: &str) -> Option<&NodeRef> {
        match (unsafe { &mut *self.generic_impls.get() }).get(ident) {
            Some(t) => Some(t),
            None => {
                if let Some(parent) = &self.parent {
                    parent.get_generic_impl(ident)
                } else {
                    None
                }
            }
        }
    }

    pub fn insert_generic_impl_instance(&self, ident: Rc<str>, type_names: Vec<Rc<str>>) {
        (unsafe { &mut *self.generic_impl_instances.get() }).push((ident.to_string(), type_names));
    }

    pub fn get_generic_impl_instances(&self) -> &Vec<(String, Vec<Rc<str>>)> {
        unsafe { &mut *self.generic_impl_instances.get() }
    }

    // impls are top level statements for now
    pub fn insert_impl_env(&self, impl_ident: &str, env: ImplEnv) {
        (unsafe { &mut *self.impl_envs.get() }).insert(impl_ident.to_string(), env);
    }

    // impls are top level statements for now
    pub fn get_impl_env_mut(&self, impl_ident: &str) -> Option<&mut ImplEnv> {
        (unsafe { &mut *self.impl_envs.get() }).get_mut(impl_ident)
    }
}

impl std::fmt::Debug for TypeEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypeEnv")
            .field("parent", &self.parent.clone())
            .field("types", unsafe { &*self.types.get() })
            .field("type_ids", &self.type_ids)
            .finish()
    }
}

#[derive(Debug)]
pub struct ImplEnv {
    type_env: Rc<TypeEnv>,
}

#[derive(Debug)]
pub struct Env {
    parent: Option<Rc<Env>>,
    vars: UnsafeCell<HashMap<String, Var>>,
    funcs: UnsafeCell<HashMap<String, Rc<Func>>>,
}

impl Env {
    pub fn new() -> Self {
        Env {
            parent: None,
            vars: UnsafeCell::new(HashMap::new()),
            funcs: UnsafeCell::new(HashMap::new()),
        }
    }

    // heh
    pub fn make_child(parent: Rc<Env>) -> Self {
        Env {
            parent: Some(parent),
            vars: UnsafeCell::new(HashMap::new()),
            funcs: UnsafeCell::new(HashMap::new()),
        }
    }

    pub fn insert_var(&self, ident: &str, val: LLVMValueRef, ty: Type) {
        (unsafe { &mut *self.vars.get() }).insert(
            ident.to_string(),
            Var {
                val,
                ty,
                is_const: false,
            },
        );
    }

    pub fn insert_const(&self, ident: &str, val: LLVMValueRef, ty: Type) {
        (unsafe { &mut *self.vars.get() }).insert(
            ident.to_string(),
            Var {
                val,
                ty,
                is_const: true,
            },
        );
    }

    pub fn get_var(&self, ident: &str) -> Option<&Var> {
        (unsafe { &*self.vars.get() }).get(ident).or({
            if let Some(parent) = &self.parent {
                parent.get_var(ident)
            } else {
                None
            }
        })
    }

    pub fn insert_func(&self, ident: &str, func: Func) {
        (unsafe { &mut *self.funcs.get() }).insert(ident.to_string(), func.into());
    }

    pub fn get_func(&self, ident: &str) -> Option<Rc<Func>> {
        match (unsafe { &*self.funcs.get() }).get(ident) {
            v @ Some(_) => v.cloned(),
            None => {
                if let Some(parent) = &self.parent {
                    parent.get_func(ident)
                } else {
                    None
                }
            }
        }
    }
}

// TODO rename
#[derive(Clone)]
struct Val {
    ty: Type, // TODO this needs to be type name?
    llvm_val: LLVMValueRef,
}

pub struct ModuleBuilder {
    ast: Rc<Vec<NodeRef>>,
    llvm_module: LLVMModuleRef,
    builder: LLVMBuilderRef,
    type_env: Rc<TypeEnv>,
    env: Rc<Env>,
    current_func_ident: Option<Rc<str>>,
    // TODO rename
    generic_struct_mono_set: Vec<(String, Vec<String>)>,
}

impl ModuleBuilder {
    pub fn new(name: &str, ast: Vec<NodeRef>) -> Self {
        let mod_name = name.to_cstring().as_ptr();
        let llvm_module = unsafe { LLVMModuleCreateWithName(mod_name) };
        let builder = unsafe { LLVMCreateBuilder() };

        Self {
            ast: Rc::from(ast),
            llvm_module,
            builder,
            type_env: Rc::new(TypeEnv::new(llvm_module)),
            env: Rc::new(Env::new()),
            current_func_ident: None,
            generic_struct_mono_set: Vec::new(),
        }
    }

    fn build_deref_ptr(
        &mut self,
        env: Rc<Env>,
        type_env: Rc<TypeEnv>,
        node: NodeRef,
        as_lvalue: bool,
    ) -> Val {
        unsafe {
            let val = self.build_expr(env.clone(), type_env.clone(), node.clone(), false);
            let ty = match val.ty {
                Type::Ref { referent_type_name } => type_env
                    .get_type_by_name(&referent_type_name)
                    .unwrap()
                    .clone(),
                Type::Ptr { pointee_type_name } => type_env
                    .get_type_by_name(&pointee_type_name)
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
        env: Rc<Env>,
        type_env: Rc<TypeEnv>,
        node: NodeRef,
        as_lvalue: bool,
    ) -> Val {
        if let NodeKind::UnOp { op, rhs } = &node.kind {
            match op {
                Op::Ref => {
                    let val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), true);

                    Val {
                        ty: val.ty.to_ref_type(),
                        llvm_val: val.llvm_val,
                    }
                }
                Op::Deref => self.build_deref_ptr(env, type_env, rhs.clone(), as_lvalue),
                Op::Not => {
                    let val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    let llvm_val = unsafe {
                        LLVMBuildNot(self.builder, val.llvm_val, "".to_cstring().as_ptr())
                    };

                    Val {
                        ty: val.ty.to_ref_type(),
                        llvm_val,
                    }
                }
                Op::Neg => {
                    let val = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    let llvm_val = unsafe {
                        LLVMBuildNeg(self.builder, val.llvm_val, "".to_cstring().as_ptr())
                    };

                    Val {
                        ty: val.ty.to_ref_type(),
                        llvm_val,
                    }
                }
                _ => todo!(),
            }
        } else {
            todo!()
        }
    }

    fn build_binop(
        &mut self,
        env: Rc<Env>,
        type_env: Rc<TypeEnv>,
        node: NodeRef,
        as_lvalue: bool,
    ) -> Val {
        if let NodeKind::BinOp { op, lhs, rhs } = &node.kind {
            let op_span = node.span.clone();
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
                        (Type::Ptr { pointee_type_name }, Type::Int { .. }) => {
                            // TODO type check and sext
                            let pointee_ty = type_env.get_type_by_name(pointee_type_name).unwrap();
                            (
                                LLVMBuildGEP2(
                                    self.builder,
                                    pointee_ty.llvm_type(type_env.clone()),
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
                        (Type::Ptr { pointee_type_name }, Type::Int { .. }) => {
                            // TODO type check and sext
                            let pointee_ty = type_env.get_type_by_name(pointee_type_name).unwrap();
                            let offset = LLVMBuildNeg(
                                self.builder,
                                rhs_val.llvm_val,
                                "".to_cstring().as_ptr(),
                            );
                            (
                                LLVMBuildGEP2(
                                    self.builder,
                                    pointee_ty.llvm_type(type_env.clone()),
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
                        type_env.get_type_by_name("u32").unwrap().clone(),
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
                        type_env.get_type_by_name("u32").unwrap().clone(),
                    )
                },
                Op::Mod => unsafe {
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    // TODO
                    (
                        LLVMBuildURem(
                            self.builder,
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        type_env.get_type_by_name("u32").unwrap().clone(),
                    )
                },
                Op::And => unsafe {
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    // TODO
                    (
                        LLVMBuildAnd(
                            self.builder,
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        type_env.get_type_by_name("bool").unwrap().clone(),
                    )
                },
                Op::Or => unsafe {
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    // TODO
                    (
                        LLVMBuildOr(
                            self.builder,
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        type_env.get_type_by_name("bool").unwrap().clone(),
                    )
                },
                Op::BitwiseAnd => unsafe {
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    // TODO
                    (
                        LLVMBuildAnd(
                            self.builder,
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        lhs_val.ty,
                    )
                },
                Op::BitwiseOr => unsafe {
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    // TODO
                    (
                        LLVMBuildOr(
                            self.builder,
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        lhs_val.ty,
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
                        type_env.get_type_by_name("bool").unwrap().clone(),
                    )
                },
                Op::NotEq => unsafe {
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    (
                        LLVMBuildICmp(
                            self.builder,
                            llvm_sys::LLVMIntPredicate::LLVMIntNE,
                            lhs_val.llvm_val,
                            rhs_val.llvm_val,
                            "".to_cstring().as_ptr(),
                        ),
                        type_env.get_type_by_name("bool").unwrap().clone(),
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
                        type_env.get_type_by_name("bool").unwrap().clone(),
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
                        type_env.get_type_by_name("bool").unwrap().clone(),
                    )
                },
                Op::Assign(op) => unsafe {
                    macro_rules! make_binop {
                        ($op:expr, $lhs:expr, $rhs: expr, $span: expr) => {
                            self.build_binop(
                                env,
                                type_env.clone(),
                                Node {
                                    kind: NodeKind::BinOp {
                                        op: $op,
                                        lhs: $lhs,
                                        rhs: $rhs,
                                    },
                                    span: $span,
                                }
                                .into(),
                                false,
                            )
                        };
                    }
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), true);
                    let rhs_val = match op.as_deref() {
                        Some(op) => make_binop!(op.clone(), lhs.clone(), rhs.clone(), op_span),
                        None => self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false),
                    };

                    (
                        LLVMBuildStore(self.builder, rhs_val.llvm_val, lhs_val.llvm_val),
                        type_env.get_type_by_name("void").unwrap().clone(),
                    )
                },
                Op::Dot => unsafe {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), true);
                    match lhs_val.ty.clone() {
                        // TODO this is possibly retarded, then again wtf do i know
                        // TODO spans are rekt
                        Type::Ref { .. } => {
                            return self.build_binop(
                                env,
                                type_env,
                                Node {
                                    kind: NodeKind::BinOp {
                                        op: Op::Dot,
                                        lhs: Node {
                                            kind: NodeKind::UnOp {
                                                op: Op::Deref,
                                                rhs: lhs.clone(),
                                            },
                                            span: op_span.clone(),
                                        }
                                        .into(),
                                        rhs: rhs.clone(),
                                    },
                                    span: op_span.clone(),
                                }
                                .into(),
                                as_lvalue,
                            )
                        }
                        Type::Struct {
                            field_indices,
                            field_type_names,
                            name: struct_name,
                            ..
                        } => match &rhs.kind {
                            NodeKind::Ident { name } => {
                                let field_idx = match field_indices.get(&**name) {
                                    Some(idx) => idx,
                                    None => panic!("{}\nno member {}", op_span, name),
                                };
                                let field_ty = if let Some(ty) =
                                    type_env.get_type_by_name(&field_type_names[*field_idx])
                                {
                                    ty
                                } else {
                                    panic!(
                                        "unresolved type {} accessing {} in struct {}\n{}",
                                        &field_type_names[*field_idx], name, struct_name, op_span
                                    );
                                };
                                let ptr = LLVMBuildStructGEP2(
                                    self.builder,
                                    lhs_val.ty.llvm_type(type_env.clone()),
                                    lhs_val.llvm_val,
                                    *field_idx as u32,
                                    "".to_cstring().as_ptr(),
                                );

                                if as_lvalue {
                                    (ptr, field_ty.clone())
                                } else {
                                    let llvm_ty = if let Type::Fn { .. } = field_ty {
                                        LLVMPointerType(field_ty.llvm_type(type_env.clone()), 0)
                                    } else {
                                        field_ty.llvm_type(type_env.clone())
                                    };
                                    (
                                        LLVMBuildLoad2(
                                            self.builder,
                                            llvm_ty,
                                            ptr,
                                            "".to_cstring().as_ptr(),
                                        ),
                                        field_ty.clone(),
                                    )
                                }
                            }
                            NodeKind::Call { ident, args } => {
                                // TODO the following fails for struct members that depend on one another
                                // build static/member methods lists before you build impl fn bodies

                                // TODO is this even needed? maybe instead consistently mangle fn names?

                                // let func_ident =
                                //     if let Some(member) = member_methods.get(&ident.to_string()) {
                                //         member
                                //     } else {
                                //         panic!("struct {} has no method {}", struct_name, ident)
                                //     };

                                let func_ident = format!("{}::{}", struct_name, ident);
                                let func = if let Some(func) = env.get_func(func_ident.as_str()) {
                                    func
                                } else {
                                    panic!("unresolved method {}\n{}", func_ident, op_span);
                                };
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
                                        Node {
                                            kind: NodeKind::UnOp {
                                                op: Op::Ref,
                                                rhs: lhs.clone(),
                                            },
                                            span: op_span.clone(),
                                        }
                                        .into(),
                                    )
                                } else {
                                    args.insert(0, lhs.clone());
                                }

                                return self.build_call(
                                    env.clone(),
                                    type_env.clone(),
                                    func_ident.as_str(),
                                    &args,
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
                        (Type::Array { elem_type_name, .. }, Type::Int { .. }) => {
                            // TODO this and bounds check
                            // if !signed {
                            //     panic!("cannot index with signed int");
                            // }

                            let elem_ty = type_env.get_type_by_name(&elem_type_name).unwrap();

                            let ptr = unsafe {
                                LLVMBuildInBoundsGEP2(
                                    self.builder,
                                    lhs_val.ty.llvm_type(type_env.clone()),
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
                                            elem_ty.llvm_type(type_env.clone()),
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
                Op::ScopeRes => match (&lhs.kind, &rhs.kind) {
                    // TODO probably not the correct way to do this
                    (
                        NodeKind::Ident { name: type_name },
                        NodeKind::Call {
                            ident: fn_ident,
                            args: fn_args,
                        },
                    ) => {
                        if let Some(Type::Struct { static_methods, .. }) =
                            type_env.get_type_by_name(type_name)
                        {
                            let mangled_name = static_methods.get(&**fn_ident).unwrap();

                            return self.build_call(env, type_env.clone(), mangled_name, fn_args);
                        } else {
                            todo!()
                        }
                    }
                    _ => todo!(),
                },
                Op::Cast => {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), true);
                    let ty = if let NodeKind::Ident { name } = &rhs.kind {
                        type_env.get_type_by_name(name).unwrap()
                    } else {
                        todo!()
                    };

                    match (lhs_val.ty, ty) {
                        (Type::Ref { referent_type_name }, Type::Ptr { pointee_type_name }) => {
                            if referent_type_name == *pointee_type_name {
                                (lhs_val.llvm_val, ty.clone())
                            } else {
                                todo!()
                            }
                        }
                        (Type::Ptr { pointee_type_name }, Type::Ref { referent_type_name }) => {
                            if *referent_type_name == pointee_type_name {
                                (lhs_val.llvm_val, ty.clone())
                            } else {
                                todo!()
                            }
                        }
                        (
                            Type::Int { .. },
                            Type::Int {
                                signed: signed_b, ..
                            },
                        ) => (
                            // TODO compare widths and signs and not build the cast if they match
                            unsafe {
                                LLVMBuildIntCast2(
                                    self.builder,
                                    lhs_val.llvm_val,
                                    ty.llvm_type(type_env.clone()),
                                    if *signed_b { 1 } else { 0 },
                                    "".to_cstring().as_ptr(),
                                )
                            },
                            ty.clone(),
                        ),
                        _ => todo!(),
                    }
                }
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
        env: Rc<Env>,
        type_env: Rc<TypeEnv>,
        ident: &str,
        arg_exprs: &[NodeRef],
    ) -> Val {
        // TODO funcs could be vars instead?
        let (llvm_ty, llvm_val, ret_ty) = if let Some(func) = env.get_func(ident) {
            (func.llvm_ty, func.val, func.ret_ty.clone())
        } else if let Some(var) = env.get_var(ident) {
            if let ty @ Type::Fn { ret_type, .. } = &var.ty {
                let llvm_val = unsafe {
                    LLVMBuildLoad2(
                        self.builder,
                        LLVMPointerType(ty.llvm_type(type_env.clone()), 0),
                        var.val,
                        "".to_cstring().as_ptr(),
                    )
                };
                (
                    ty.llvm_type(type_env.clone()),
                    llvm_val,
                    type_env.get_type_by_name(ret_type).unwrap().clone(),
                )
            } else {
                todo!()
            }
        } else {
            panic!("unresolved function {}", ident)
        };

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
                llvm_ty,
                llvm_val,
                args.as_mut_slice().as_mut_ptr(),
                args.len() as u32,
                "".to_cstring().as_ptr(),
            )
        };

        Val {
            ty: ret_ty,
            llvm_val,
        }
    }

    fn build_array(&mut self, env: Rc<Env>, type_env: Rc<TypeEnv>, elems: &[NodeRef]) -> Val {
        let elem_vals: Vec<Val> = elems
            .iter()
            .map(|elem| self.build_expr(env.clone(), type_env.clone(), elem.clone(), false))
            .collect();
        let elem_ty = elem_vals.first().unwrap().ty.clone();
        let mut elem_vals: Vec<LLVMValueRef> = elem_vals.iter().map(|elem| elem.llvm_val).collect();
        let llvm_val = unsafe {
            LLVMConstArray2(
                elem_ty.llvm_type(type_env.clone()),
                elem_vals.as_mut_slice().as_mut_ptr(),
                elem_vals.len() as u64,
            )
        };

        Val {
            ty: Type::Array {
                elem_type_name: elem_ty.name(),
                len: elem_vals.len(),
            },
            llvm_val,
        }
    }

    fn build_string(&mut self, type_env: Rc<TypeEnv>, value: Rc<str>) -> Val {
        let ty = type_env.get_type_by_name("u8").unwrap();
        let bytes: Vec<u8> = value.bytes().collect();

        let llvm_val = unsafe {
            LLVMBuildGlobalString(
                self.builder,
                bytes.as_slice().as_ptr() as *const i8,
                "".to_cstring().as_ptr(),
            )
        };

        Val {
            ty: Type::Array {
                elem_type_name: ty.name(),
                len: bytes.len(),
            },
            llvm_val,
        }
    }

    fn build_expr(
        &mut self,
        env: Rc<Env>,
        type_env: Rc<TypeEnv>,
        node: NodeRef,
        as_lvalue: bool,
    ) -> Val {
        match &node.kind {
            NodeKind::NullPtr => {
                Val {
                    // TODO type
                    ty: type_env.get_type_by_name("*void").unwrap().clone(),
                    llvm_val: unsafe { LLVMConstPointerNull(LLVMPointerType(LLVMVoidType(), 0)) },
                }
            }
            NodeKind::Int { value } => unsafe {
                // FIXME int type
                // TODO sign extend
                let llvm_val = LLVMConstInt(LLVMInt32Type(), (*value).try_into().unwrap(), 0);

                Val {
                    ty: type_env.get_type_by_name("u32").unwrap().clone(),
                    llvm_val,
                }
            },
            NodeKind::Bool { value } => unsafe {
                let llvm_val = LLVMConstInt(LLVMInt1Type(), if *value { 1 } else { 0 }, 0);

                Val {
                    ty: type_env.get_type_by_name("bool").unwrap().clone(),
                    llvm_val,
                }
            },
            NodeKind::Char { value } => unsafe {
                let llvm_val = LLVMConstInt(LLVMInt8Type(), **value as u64, 0);

                Val {
                    ty: type_env.get_type_by_name("u8").unwrap().clone(),
                    llvm_val,
                }
            },
            NodeKind::Ident { name } => unsafe {
                if let Some(var) = env.get_var(name) {
                    let llvm_val = if as_lvalue || var.is_const {
                        var.val
                    } else {
                        let llvm_ty = if let Type::Fn { .. } = var.ty {
                            LLVMPointerType(var.ty.llvm_type(type_env.clone()), 0)
                        } else {
                            var.ty.llvm_type(type_env.clone())
                        };

                        LLVMBuildLoad2(self.builder, llvm_ty, var.val, "".to_cstring().as_ptr())
                    };

                    Val {
                        ty: var.ty.clone(),
                        llvm_val,
                    }
                } else if let Some(f) = env.get_func(name) {
                    Val {
                        ty: f.ty.clone(),
                        llvm_val: f.val,
                    }
                } else {
                    panic!("unresolved ident {}", name)
                }
            },
            NodeKind::UnOp { .. } => self.build_unop(env, type_env, node, as_lvalue),
            NodeKind::BinOp { .. } => self.build_binop(env, type_env, node, as_lvalue),
            NodeKind::Call { ident, args } => {
                if &**ident == "sizeof" {
                    assert!(args.len() == 1);
                    if let NodeKind::Ident { name: ty_name } = &args[0].kind {
                        let ty_usize = type_env.get_type_by_name("u32").unwrap().clone(); // TODO usize
                        Val {
                            ty: ty_usize.clone(),
                            llvm_val: unsafe {
                                LLVMBuildIntCast2(
                                    self.builder,
                                    LLVMSizeOf(
                                        type_env
                                            .get_type_by_name(ty_name)
                                            .unwrap()
                                            .llvm_type(type_env.clone()),
                                    ),
                                    ty_usize.llvm_type(type_env),
                                    0,
                                    "".to_cstring().as_ptr(),
                                )
                            },
                        }
                    } else {
                        todo!()
                    }
                } else {
                    self.build_call(env, type_env, ident, args)
                }
            }
            NodeKind::Array { elems } => self.build_array(env, type_env, elems),
            NodeKind::Str { value } => self.build_string(type_env, value.clone()),
            NodeKind::StructLiteral { ident, fields } => {
                // TODO this shares common behaviour with the dot operator on structs.
                // maybe have something like build_store_struct_member()
                // TODO in (for instance) let ... = T {...}, alloca and load here are redundant
                if let Some(ty @ Type::Struct { field_indices, .. }) =
                    type_env.get_type_by_name(ident)
                {
                    let func = self.env.get_func(&self.current_func_ident.clone().unwrap());

                    // TODO this is also used in 'let'. could be a helper function like build_alloca(...)
                    let reg = unsafe {
                        let bb_current = LLVMGetInsertBlock(self.builder);

                        LLVMPositionBuilderAtEnd(self.builder, func.unwrap().bb_entry.unwrap());

                        let reg = LLVMBuildAlloca(
                            self.builder,
                            ty.llvm_type(type_env.clone()),
                            "".to_cstring().as_ptr(),
                        );

                        LLVMPositionBuilderAtEnd(self.builder, bb_current);
                        reg
                    };

                    for field in fields.iter() {
                        let field_idx = if let Some(idx) = field_indices.get(&*field.ident) {
                            idx
                        } else {
                            panic!(
                                "unresolved field {} in struct literal {}",
                                field.ident,
                                ty.name()
                            );
                        };

                        let llvm_ty = if let Type::Fn { .. } = ty {
                            unsafe { LLVMPointerType(ty.llvm_type(type_env.clone()), 0) }
                        } else {
                            ty.llvm_type(type_env.clone())
                        };

                        let ptr = unsafe {
                            LLVMBuildStructGEP2(
                                self.builder,
                                llvm_ty,
                                reg,
                                *field_idx as u32,
                                "".to_cstring().as_ptr(),
                            )
                        };

                        let val = self.build_expr(
                            env.clone(),
                            type_env.clone(),
                            field.val.clone(),
                            false,
                        );
                        unsafe { LLVMBuildStore(self.builder, val.llvm_val, ptr) };
                    }

                    let llvm_val = if as_lvalue {
                        reg
                    } else {
                        unsafe {
                            LLVMBuildLoad2(
                                self.builder,
                                ty.llvm_type(type_env.clone()),
                                reg,
                                "".to_cstring().as_ptr(),
                            )
                        }
                    };

                    Val {
                        ty: ty.clone(),
                        llvm_val,
                    }
                } else {
                    panic!("unresolved type {}", ident);
                }
            }
            _ => panic!("unimplemented!\n {:?}", node),
        }
    }

    fn build_stmt(&mut self, env: Rc<Env>, type_env: Rc<TypeEnv>, node: NodeRef) -> Val {
        match &node.kind {
            NodeKind::Return { expr: stmt } => {
                let llvm_val = if let Some(rhs) = &stmt {
                    let v = self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);
                    unsafe { LLVMBuildRet(self.builder, v.llvm_val) }
                } else {
                    unsafe { LLVMBuildRetVoid(self.builder) }
                };

                Val {
                    ty: type_env.get_type_by_name("void").unwrap().clone(),
                    llvm_val,
                }
            }
            NodeKind::Let { ty, lhs, rhs } => unsafe {
                // TODO alloca the var and let assign do the rest?
                if let NodeKind::Ident { name } = &lhs.kind {
                    let var_ty = if let Some(ty) = ty {
                        match type_env.get_type_by_name(ty) {
                            t @ Some(_) => t,
                            None => panic!("unknown type {}", ty),
                        }
                    } else {
                        None
                    };

                    let func = self.env.get_func(&self.current_func_ident.clone().unwrap());
                    let bb_current = LLVMGetInsertBlock(self.builder);

                    let rhs_val = rhs.as_ref().map(|rhs| {
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false)
                    });

                    // TODO type inference stuff
                    let ty = match (var_ty, rhs_val.clone()) {
                        (Some(t1), Some(..)) => {
                            // assert_eq!(*t1, val.ty); // TODO Eq for types
                            t1.clone()
                        }
                        (Some(t), None) => t.clone(),
                        (None, Some(val)) => val.ty.clone(),
                        (None, None) => {
                            panic!("cannot infer type for let");
                        }
                    };

                    let llvm_ty = if let t @ Type::Fn { .. } = ty.clone() {
                        LLVMPointerType(t.llvm_type(type_env.clone()), 0) // TODO Type::llvm_ptr_type()
                    } else {
                        ty.llvm_type(type_env.clone())
                    };

                    LLVMPositionBuilderAtEnd(self.builder, func.unwrap().bb_entry.unwrap());
                    let reg = LLVMBuildAlloca(self.builder, llvm_ty, "".to_cstring().as_ptr());
                    LLVMPositionBuilderAtEnd(self.builder, bb_current);

                    env.insert_var(name, reg, ty);

                    if let Some(val) = rhs_val {
                        LLVMBuildStore(self.builder, val.llvm_val, reg);
                    };

                    // TODO llvm_val or val should be optional
                    Val {
                        ty: Type::None,
                        llvm_val: LLVMConstInt(LLVMInt1Type(), 0, 0),
                    }
                } else {
                    panic!()
                }
            },
            NodeKind::If {
                condition,
                then_block,
                else_block,
            } => unsafe {
                if let Some(fn_ident) = &self.current_func_ident {
                    let current_func = env.get_func(fn_ident).unwrap();

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

                    // FIXME properly determine whether the else/exit blocks should be built
                    LLVMPositionBuilderAtEnd(self.builder, bb_then);
                    if !self.build_block(env.clone(), type_env.clone(), then_block.clone()) {
                        LLVMBuildBr(self.builder, bb_exit);
                    }
                    LLVMPositionBuilderAtEnd(self.builder, bb_else);
                    if let Some(else_block) = else_block {
                        if !self.build_block(env.clone(), type_env.clone(), else_block.clone()) {
                            LLVMBuildBr(self.builder, bb_exit);
                        }
                    } else {
                        LLVMBuildBr(self.builder, bb_exit);
                    }

                    LLVMPositionBuilderAtEnd(self.builder, bb_exit);
                    Val {
                        ty: type_env.get_type_by_name("void").unwrap().clone(),
                        llvm_val: cond,
                    }
                } else {
                    panic!("if stmt outside fn")
                }
            },
            NodeKind::While { condition, body } => unsafe {
                // TODO put decls inside loop body before test bb
                if let Some(fn_ident) = &self.current_func_ident {
                    let current_func = env.get_func(fn_ident).unwrap();

                    // FIXME i hate the ordering of nested blocks in the IR. need to build depth first
                    let bb_test = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    LLVMBuildBr(self.builder, bb_test);
                    let bb_body = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());
                    let bb_exit = LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr());

                    LLVMPositionBuilderAtEnd(self.builder, bb_test);
                    LLVMBuildCondBr(
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
                        ty: type_env.get_type_by_name("void").unwrap().clone(),
                        llvm_val: null_mut(),
                    }
                } else {
                    panic!("while stmt outside fn")
                }
            },
            NodeKind::Match {
                scrutinee,
                arms,
                num_cases,
            } => {
                if let Some(fn_ident) = &self.current_func_ident {
                    let current_func = env.get_func(fn_ident).unwrap();
                    let bb_exit =
                        unsafe { LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr()) };
                    let scrutinee_val =
                        self.build_expr(env.clone(), type_env.clone(), scrutinee.clone(), false);

                    let switch = unsafe {
                        LLVMBuildSwitch(
                            self.builder,
                            scrutinee_val.llvm_val,
                            bb_exit,
                            *num_cases as u32,
                        )
                    };

                    for arm in arms.iter() {
                        let mut pattern_vals: Vec<Val> = Vec::new();

                        for case in arm.pattern.iter() {
                            let val =
                                self.build_expr(env.clone(), type_env.clone(), case.clone(), false);
                            pattern_vals.push(val);
                        }

                        let bb = unsafe {
                            LLVMAppendBasicBlock(current_func.val, "".to_cstring().as_ptr())
                        };
                        unsafe { LLVMPositionBuilderAtEnd(self.builder, bb) };
                        if let NodeKind::Block { .. } = &arm.stmt.kind {
                            self.build_block(env.clone(), type_env.clone(), arm.stmt.clone());
                        } else {
                            self.build_expr(env.clone(), type_env.clone(), arm.stmt.clone(), false);
                        }
                        unsafe { LLVMBuildBr(self.builder, bb_exit) };

                        for val in pattern_vals {
                            unsafe { LLVMAddCase(switch, val.llvm_val, bb) };
                        }
                    }

                    unsafe { LLVMPositionBuilderAtEnd(self.builder, bb_exit) };

                    Val {
                        ty: type_env.get_type_by_name("void").unwrap().clone(),
                        llvm_val: null_mut(),
                    }
                } else {
                    panic!("match stmt outside fn")
                }
            }
            _ => self.build_expr(env, type_env.clone(), node, false),
        }
    }

    fn build_block(&mut self, env: Rc<Env>, type_env: Rc<TypeEnv>, node: NodeRef) -> bool {
        let mut returns = false;
        if let NodeKind::Block { statements } = &node.kind {
            for (i, stmt) in statements.iter().enumerate() {
                // TODO this is a quick hack. build_stmt should return info, including whether the stmt returns
                if let NodeKind::Return { .. } = &stmt.kind {
                    if i == statements.len() - 1 {
                        returns = true;
                    } else {
                        panic!("return stmt in the middle of block");
                    }
                }
                self.build_stmt(env.clone(), type_env.clone(), stmt.clone());
            }
        } else {
            panic!()
        }
        returns
    }

    fn set_up_function(
        &mut self,
        env: Rc<Env>,
        type_env: Rc<TypeEnv>,
        ident: &str,
        args: Rc<[Arg]>,
        ret_ty: Rc<str>,
        is_extern: bool,
        _linkage: Option<Rc<str>>,
    ) {
        let ret_ty = match type_env.get_type_by_name(&ret_ty) {
            Some(ty) => ty,
            None => panic!("unresolved type {}", ret_ty),
        };
        let mut arg_ty_names: Vec<Rc<str>> = Vec::new();
        let mut arg_tys: Vec<Type> = Vec::new();
        let mut llvm_arg_types: Vec<LLVMTypeRef> = Vec::new();
        for arg in args.iter() {
            if let Some(ty) = type_env.get_type_by_name(&arg.ty()) {
                arg_ty_names.push(arg.ty());
                arg_tys.push(ty.clone());
                let llvm_ty = if let Type::Fn { .. } = ty {
                    unsafe { LLVMPointerType(ty.llvm_type(type_env.clone()), 0) }
                } else {
                    ty.llvm_type(type_env.clone())
                };
                llvm_arg_types.push(llvm_ty);
            } else {
                panic!("unresolved type {}", &arg.ty());
            }
        }
        let func_ty = unsafe {
            LLVMFunctionType(
                ret_ty.llvm_type(type_env.clone()),
                llvm_arg_types.as_mut_slice().as_mut_ptr(),
                llvm_arg_types.len().try_into().unwrap(),
                0,
            )
        };
        let val =
            unsafe { LLVMAddFunction(self.llvm_module, ident.to_cstring().as_ptr(), func_ty) };

        let fn_env = Env::make_child(env.clone());
        let (bb_entry, bb_body) = if is_extern {
            (None, None)
        } else {
            unsafe {
                (
                    Some(LLVMAppendBasicBlock(
                        val,
                        "".to_string().to_cstring().as_ptr(),
                    )),
                    Some(LLVMAppendBasicBlock(
                        val,
                        "".to_string().to_cstring().as_ptr(),
                    )),
                )
            }
        };

        let fn_ty_name = format!("fn({}) -> {}", arg_ty_names.join(","), ret_ty.name());
        let fn_ty = type_env.get_type_by_name(&fn_ty_name).unwrap();

        // this needs to be global
        self.env.insert_func(
            ident,
            Func {
                ty: fn_ty.clone(),
                env: Rc::new(fn_env),
                arg_tys,
                ret_ty: ret_ty.clone(),
                val,
                llvm_ty: func_ty,
                bb_entry,
                bb_body,
            },
        );
    }

    fn build_function(
        &mut self,
        env: Rc<Env>,
        type_env: Rc<TypeEnv>,
        ident: Rc<str>,
        args: Rc<[Arg]>,
        body: NodeRef,
    ) {
        let func = env.get_func(&ident).unwrap();
        if let (Some(bb_entry), Some(bb_body)) = (func.bb_entry, func.bb_body) {
            self.current_func_ident = Some(ident.clone());
            unsafe { LLVMPositionBuilderAtEnd(self.builder, bb_entry) };

            for (i, arg) in args.iter().enumerate() {
                let ty = match type_env.get_type_by_name(&arg.ty()) {
                    Some(ty) => ty,
                    None => panic!("unresolved type {}", arg.ty()),
                };

                let llvm_ty = if let Type::Fn { .. } = ty {
                    unsafe { LLVMPointerType(ty.llvm_type(type_env.clone()), 0) }
                } else {
                    ty.llvm_type(type_env.clone())
                };

                let argp =
                    unsafe { LLVMBuildAlloca(self.builder, llvm_ty, "".to_cstring().as_ptr()) };
                unsafe {
                    LLVMBuildStore(
                        self.builder,
                        LLVMGetParam(func.val, i.try_into().unwrap()),
                        argp,
                    )
                };
                func.env.insert_var(&arg.ident(), argp, ty.clone());
            }

            unsafe { LLVMPositionBuilderAtEnd(self.builder, bb_body) };

            self.build_block(func.env.clone(), type_env.clone(), body.clone());
            if func.ret_ty == Type::None {
                unsafe { LLVMBuildRetVoid(self.builder) };
            }

            unsafe {
                LLVMPositionBuilderAtEnd(self.builder, bb_entry);
                LLVMBuildBr(self.builder, bb_body);
            }

            self.current_func_ident = None;
        }
    }

    fn register_struct(&self, env: &Env, type_env: &TypeEnv, node: NodeRef, name: Option<String>) {
        if let NodeKind::Struct {
            ident,
            fields,
            generics,
            attributes,
        } = &node.kind
        {
            let mut field_indices: HashMap<String, usize> = HashMap::new();
            let mut field_type_names: Vec<Rc<String>> = Vec::new();
            for (idx, field) in fields.iter().enumerate() {
                field_type_names.push(field.ty.to_string().into());
                field_indices.insert(field.ident.to_string(), idx);
            }

            let name = name.unwrap_or(ident.to_string());
            self.type_env.insert_type_by_name(
                &name.clone(),
                Type::Struct {
                    name: name.into(),
                    field_indices,
                    field_type_names,
                    static_methods: HashMap::new(),
                    member_methods: HashMap::new(),
                    generics: generics.clone(),
                    attributes: attributes.clone(),
                },
            );
        }
    }

    fn pass1(&mut self) {
        for node in &*self.ast {
            #[allow(clippy::single_match)]
            match &node.kind {
                NodeKind::Const { ty, lhs, rhs } => {
                    if let NodeKind::Ident { name } = &lhs.kind {
                        let ty = if let Some(ty) = ty { ty } else { todo!() };

                        let ty = match self.type_env.get_type_by_name(ty) {
                            Some(t) => t,
                            None => panic!("unknown type {}", ty),
                        };

                        // TODO type checking and missing types
                        if let Some(Node {
                            kind: NodeKind::Int { value },
                            ..
                        }) = rhs.as_deref()
                        {
                            self.env.insert_const(
                                name,
                                unsafe {
                                    LLVMConstInt(
                                        ty.llvm_type(self.type_env.clone()),
                                        *value as u64,
                                        0,
                                    )
                                },
                                ty.clone(),
                            );
                        } else {
                            unimplemented!()
                        }
                    } else {
                        panic!()
                    }
                }
                _ => (),
            }
        }
    }

    fn pass2(&mut self) {
        for node in &*self.ast {
            if let NodeKind::Struct {
                ident, generics, ..
            } = &node.kind
            {
                let local_env = Rc::new(Env::make_child(self.env.clone()));
                let local_type_env = Rc::new(TypeEnv::make_child(self.type_env.clone()));

                // TODO build a dependency tree and gen structs depth first
                if generics.len() == 0 {
                    self.register_struct(&local_env, &local_type_env, node.clone(), None);
                } else {
                    self.type_env
                        .insert_generic_type(ident.to_string(), node.clone())
                }
            }
        }

        for (name, type_args) in self.generic_struct_mono_set.iter() {
            let local_env = Rc::new(Env::make_child(self.env.clone()));
            let local_type_env = Rc::new(TypeEnv::make_child(self.type_env.clone()));

            if let Some(
                node @ Node {
                    kind: NodeKind::Struct { generics, .. },
                    ..
                },
            ) = self.type_env.get_generic_type(name).map(|node| &**node)
            {
                for (generic_type_name, concrete_type_name) in generics.iter().zip(type_args.iter())
                {
                    if let Some(concrete_type) = local_type_env.get_type_by_name(concrete_type_name)
                    {
                        local_type_env
                            .insert_type_by_name(generic_type_name, concrete_type.clone());
                    } else {
                        continue;
                        // panic!("unresolved type {} while monomorphizing struct {} with generics {:?}", concrete_type_name, ident, generics);
                    }
                }

                let mangled_name = format!("{}<{}>", name, type_args.join(","));
                self.register_struct(
                    &local_env,
                    &local_type_env,
                    node.clone().into(),
                    Some(mangled_name.clone()),
                );
                self.type_env.insert_impl_env(
                    &mangled_name,
                    ImplEnv {
                        type_env: local_type_env,
                    },
                )
            }
        }
    }

    fn pass3(&mut self) {
        for node in &*self.ast.clone() {
            match &node.kind {
                NodeKind::Fn {
                    ident,
                    args,
                    ret_ty,
                    is_extern,
                    linkage,
                    ..
                } => self.set_up_function(
                    self.env.clone(),
                    self.type_env.clone(),
                    ident,
                    args.clone(),
                    ret_ty.clone(),
                    *is_extern,
                    linkage.clone(),
                ),
                NodeKind::ExternBlock { linkage, block } => {
                    if let NodeKind::Block { statements } = &block.kind {
                        for stmt in statements.iter() {
                            if let NodeKind::Fn {
                                ident,
                                args,
                                ret_ty,
                                ..
                            } = &stmt.kind
                            {
                                self.set_up_function(
                                    self.env.clone(),
                                    self.type_env.clone(),
                                    ident,
                                    args.clone(),
                                    ret_ty.clone(),
                                    true,
                                    linkage.clone(),
                                )
                            } else {
                                todo!()
                            }
                        }
                    }
                }
                _ => (),
            }
        }
    }

    fn pass4(&mut self) {
        for node in &*self.ast.clone() {
            #[allow(clippy::single_match)]
            match &node.kind {
                NodeKind::Impl {
                    ident: impl_ty,
                    methods,
                    type_generics,
                    ..
                } => {
                    if type_generics.len() > 0 {
                        self.type_env
                            .insert_generic_impl(impl_ty.clone(), node.clone());
                    } else {
                        let env = Rc::new(Env::make_child(self.env.clone()));
                        let type_env = Rc::new(TypeEnv::make_child(self.type_env.clone()));

                        type_env.insert_type_by_name(
                            "Self",
                            self.type_env.get_type_by_name(impl_ty).unwrap().clone(),
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
                            if let NodeKind::Fn {
                                ident: method_name,
                                args,
                                ret_ty,
                                ..
                            } = &method.kind
                            {
                                let is_static = if let Some(arg) = args.first() {
                                    !(&*arg.ty() == "Self" || &*arg.ty() == "&Self")
                                } else {
                                    true
                                };

                                let mangled_name = format!("{}::{}", impl_ty, method_name);

                                if is_static {
                                    static_methods
                                        .insert(method_name.to_string(), mangled_name.clone());
                                } else {
                                    member_methods
                                        .insert(method_name.to_string(), mangled_name.clone());
                                }

                                self.set_up_function(
                                    env.clone(),
                                    type_env.clone(),
                                    &mangled_name,
                                    args.clone(),
                                    ret_ty.clone(),
                                    false,
                                    None,
                                );
                            } else {
                                todo!()
                            }
                        }
                    }
                }
                _ => (),
            }
        }
    }

    fn pass5(&mut self) {
        for node in &*self.ast.clone() {
            if let NodeKind::Impl {
                ident: impl_ty,
                methods,
                type_generics,
                ..
            } = &node.kind
            {
                // TODO duplicated stuff here
                if type_generics.is_empty() {
                    let env = Rc::new(Env::make_child(self.env.clone()));
                    let type_env = Rc::new(TypeEnv::make_child(self.type_env.clone()));
                    type_env.insert_type_by_name(
                        "Self",
                        self.type_env.get_type_by_name(impl_ty).unwrap().clone(),
                    );

                    for method in methods.iter() {
                        if let NodeKind::Fn {
                            ident, args, body, ..
                        } = &method.kind
                        {
                            let mangled_name = format!("{}::{}", impl_ty, ident);
                            self.build_function(
                                env.clone(),
                                type_env.clone(),
                                mangled_name.into(),
                                args.clone(),
                                body.clone().unwrap(),
                            )
                        } else {
                            todo!()
                        }
                    }
                } else {
                    let monos: Vec<Vec<String>> = self
                        .generic_struct_mono_set
                        .iter()
                        .filter(|(name, _)| name == &**impl_ty)
                        .map(|(_, concrete_types)| concrete_types.clone())
                        .collect();

                    for concrete_types in monos {
                        let impl_ty = format!("{}<{}>", impl_ty, concrete_types.join(","));
                        let env = Rc::new(Env::make_child(self.env.clone()));
                        let type_env = Rc::new(TypeEnv::make_child(self.type_env.clone()));
                        type_env.insert_type_by_name(
                            "Self",
                            self.type_env.get_type_by_name(&impl_ty).unwrap().clone(),
                        );

                        for (generic, ty) in type_generics.iter().zip(concrete_types.iter()) {
                            if let Some(ty) = type_env.get_type_by_name(ty) {
                                type_env.insert_type_by_name(generic, ty.clone());
                            } else {
                                return; // FIXME we get here if we have non-monomorphized types in the set, which shouldn't happen
                            }
                        }

                        for method in methods.iter() {
                            if let NodeKind::Fn {
                                ident,
                                args,
                                body,
                                ret_ty,
                                ..
                            } = &method.kind
                            {
                                let mangled_name = format!("{}::{}", impl_ty, ident);
                                self.set_up_function(
                                    env.clone(),
                                    type_env.clone(),
                                    &mangled_name,
                                    args.clone(),
                                    ret_ty.clone(),
                                    false,
                                    None,
                                );

                                // TODO defer this to a later stage or member fns might not be able to resolve each other
                                self.build_function(
                                    env.clone(),
                                    type_env.clone(),
                                    mangled_name.into(),
                                    args.clone(),
                                    body.clone().unwrap(),
                                )
                            } else {
                                todo!()
                            }
                        }
                    }
                }
            }
        }
    }

    fn pass6(&mut self) {
        for node in &*self.ast.clone() {
            match &node.kind {
                NodeKind::Fn {
                    ident,
                    body,
                    args,
                    is_extern,
                    ..
                } => {
                    if !is_extern {
                        self.build_function(
                            self.env.clone(),
                            self.type_env.clone(),
                            ident.clone(),
                            args.clone(),
                            body.clone().unwrap(),
                        )
                    }
                }
                _ => (),
            }
        }
    }

    pub fn build(&mut self) {
        TypeCollector::new(self.ast.clone())
            .collect()
            .for_each(|ty| {
                if ty.contains('<') {
                    let (mut type_name, generics) = ty.split_once('<').unwrap();
                    let types: Vec<String> = generics
                        .strip_suffix('>')
                        .unwrap()
                        .split_terminator(',')
                        .map(|t| t.to_string())
                        .collect();

                    type_name = type_name.trim_start_matches('&').trim_start_matches('*');

                    self.generic_struct_mono_set
                        .push((type_name.to_owned(), types));
                } else {
                    // TODO this is to bring the type into scope but might/should not be necessary
                    self.type_env.get_type_by_name(ty);
                }
            });

        self.pass1();
        self.pass2();
        self.pass3();
        self.pass4();
        self.pass5();
        self.pass6();
    }

    pub unsafe fn get_llvm_module_ref(&mut self) -> LLVMModuleRef {
        self.llvm_module
    }
}

impl Drop for ModuleBuilder {
    fn drop(&mut self) {
        unsafe { LLVMDisposeBuilder(self.builder) };
    }
}
