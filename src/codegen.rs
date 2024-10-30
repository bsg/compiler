// TODO LLVMVerifyFunction & check return values of llvm-sys function calls
// FIXME function pointer related stuff resulted in a lot of duplicate code
// FIXME attributes are fucked
// FIXME assigning a struct to another seems to 'move' it instead of copying it
// FIXME top level consts dependent will not resolve compound types on account of type not being available when the const is being generated
// TODO llvm type aliases for compound types
// TODO Scope!
// FIXME pointer arithmetic and deref are fucked
// TODO generic param bindings should be aliases, not newtypes

use llvm_sys::core::*;
use llvm_sys::prelude::*;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::collections::LinkedList;
use std::ffi::CString;
use std::ptr::null_mut;
use std::rc::Rc;

use crate::ast::*;
use crate::type_env::Type;
use crate::type_env::TypeEnv;

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

fn llvm_type(ty: &Type, type_env: Rc<TypeEnv>) -> LLVMTypeRef {
    match ty {
        Type::Void => unsafe { LLVMVoidType() },
        Type::Bool => unsafe { LLVMInt1Type() },
        Type::Int { width, .. } => match width {
            8 => unsafe { LLVMInt8Type() },
            16 => unsafe { LLVMInt16Type() },
            32 => unsafe { LLVMInt32Type() },
            64 => unsafe { LLVMInt64Type() },
            128 => unsafe { LLVMInt128Type() },
            _ => todo!(),
        },
        Type::Ref { referent_type } => unsafe {
            if let Some(ty) = type_env.get(referent_type) {
                LLVMPointerType(llvm_type(ty, type_env.clone()), 0)
            } else {
                // TODO this and similar needs to be propagated up. maybe llvm_type should return Option<...>
                panic!("unresolved type {}", referent_type);
            }
        },
        Type::Ptr { pointee_type } => unsafe {
            if let Some(ty) = type_env.get(pointee_type) {
                LLVMPointerType(llvm_type(ty, type_env.clone()), 0)
            } else {
                panic!("unresolved type {}", pointee_type);
            }
        },
        Type::Struct {
            field_types,
            attributes,
            ..
        } => unsafe {
            let mut llvm_types: Vec<LLVMTypeRef> = field_types
                .iter()
                .map(|f| {
                    if let Some(ty) = type_env.get(f) {
                        if let Type::Fn { .. } = ty {
                            LLVMPointerType(llvm_type(ty, type_env.clone()), 0)
                        } else {
                            llvm_type(ty, type_env.clone())
                        }
                    } else {
                        panic!("unresolved type {}", *f)
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

            LLVMStructType(llvm_types.as_mut_ptr(), field_types.len() as u32, packed)
        },
        Type::Array { elem_type, len } => unsafe {
            LLVMArrayType2(
                llvm_type(type_env.get(elem_type).unwrap(), type_env.clone()),
                *len as u64,
            )
        },
        Type::Fn { params, ret_type } => {
            let mut llvm_param_types: Vec<LLVMTypeRef> = Vec::new();
            for param_type in params {
                llvm_param_types.push(llvm_type(
                    type_env.get(param_type).unwrap(),
                    type_env.clone(),
                ))
            }

            unsafe {
                LLVMFunctionType(
                    llvm_type(type_env.clone().get(ret_type).unwrap(), type_env),
                    llvm_param_types.as_mut_slice().as_mut_ptr(),
                    llvm_param_types.len() as u32,
                    0,
                )
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Var {
    val: LLVMValueRef,
    ty: Rc<TypeAnnotation>,
    is_const: bool,
}

pub struct Func {
    ty: Rc<TypeAnnotation>,
    env: Rc<Env>,
    type_env: Rc<TypeEnv>,
    ret_type: Rc<TypeAnnotation>, // TODO should not be necessary because we have ty
    val: LLVMValueRef,
    llvm_type: LLVMTypeRef, // TODO not necessary because we have ty
    // TODO group these two together -- (wtf did I mean here?)
    bb_entry: Option<LLVMBasicBlockRef>,
    bb_body: Option<LLVMBasicBlockRef>,
    node: Option<NodeRef>,
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

    pub fn insert_var(&self, ident: &str, val: LLVMValueRef, ty: Rc<TypeAnnotation>) {
        (unsafe { &mut *self.vars.get() }).insert(
            ident.to_string(),
            Var {
                val,
                ty,
                is_const: false,
            },
        );
    }

    pub fn insert_const(&self, ident: &str, val: LLVMValueRef, ty: Rc<TypeAnnotation>) {
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
    ty: Rc<TypeAnnotation>,
    llvm_val: LLVMValueRef,
}

pub struct ModuleBuilder {
    ast: Rc<Vec<NodeRef>>,
    llvm_module: LLVMModuleRef,
    builder: LLVMBuilderRef,
    type_env: Rc<TypeEnv>,
    env: Rc<Env>,
    current_func_ident: Option<Rc<str>>,
    continue_block: Option<LLVMBasicBlockRef>,
    break_block: Option<LLVMBasicBlockRef>,
    fn_decls: UnsafeCell<HashMap<String, (PathSegment, NodeRef)>>,
    fn_specializations: UnsafeCell<LinkedList<(PathSegment, NodeRef)>>,
    fns_to_build: Vec<String>,
}

impl ModuleBuilder {
    pub fn new(name: &str, ast: Vec<NodeRef>) -> Self {
        let mod_name = name.to_cstring().as_ptr();
        let llvm_module = unsafe { LLVMModuleCreateWithName(mod_name) };
        let builder = unsafe { LLVMCreateBuilder() };

        let type_env = Rc::new(TypeEnv::new());
        type_env.insert(
            TypeAnnotation::Simple {
                ident: "void".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Void,
        );
        type_env.insert(
            TypeAnnotation::Simple {
                ident: "bool".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Bool,
        );
        type_env.insert(
            TypeAnnotation::Simple {
                ident: "u8".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Int {
                width: 8,
                signed: false,
            },
        );
        type_env.insert(
            TypeAnnotation::Simple {
                ident: "u16".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Int {
                width: 16,
                signed: false,
            },
        );
        type_env.insert(
            TypeAnnotation::Simple {
                ident: "u32".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Int {
                width: 32,
                signed: false,
            },
        );
        type_env.insert(
            TypeAnnotation::Simple {
                ident: "i8".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Int {
                width: 8,
                signed: true,
            },
        );
        type_env.insert(
            TypeAnnotation::Simple {
                ident: "i16".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Int {
                width: 16,
                signed: true,
            },
        );
        type_env.insert(
            TypeAnnotation::Simple {
                ident: "i32".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Int {
                width: 32,
                signed: true,
            },
        );

        Self {
            ast: Rc::from(ast),
            llvm_module,
            builder,
            type_env,
            env: Rc::new(Env::new()),
            current_func_ident: None,
            continue_block: None,
            break_block: None,
            fn_decls: UnsafeCell::new(HashMap::new()),
            fn_specializations: UnsafeCell::new(LinkedList::new()),
            fns_to_build: Vec::new(),
        }
    }

    fn push_fn_decl(&self, ident: String, path_segment: PathSegment, node: NodeRef) {
        unsafe { &mut *self.fn_decls.get() }.insert(ident, (path_segment, node));
    }

    // TODO why the fuck does this not take ident by ref? similar shit elsewhere
    fn get_fn_decl(&self, ident: String) -> Option<&(PathSegment, NodeRef)> {
        unsafe { &mut *self.fn_decls.get() }.get(&ident)
    }

    fn push_fn_specialization(&self, path_segment: PathSegment, node: NodeRef) {
        { unsafe { &mut *self.fn_specializations.get() } }.push_back((path_segment, node));
    }

    fn get_fn_specializations(&mut self) -> &mut LinkedList<(PathSegment, NodeRef)> {
        unsafe { &mut *self.fn_specializations.get() }
    }

    fn build_deref(
        &mut self,
        env: Rc<Env>,
        type_env: Rc<TypeEnv>,
        node: NodeRef,
        as_lvalue: bool,
    ) -> Val {
        unsafe {
            let val = self.build_expr(env.clone(), type_env.clone(), node.clone(), false);
            let ty = match &*val.ty {
                TypeAnnotation::Ref { referent_type } => referent_type.clone(),
                TypeAnnotation::Ptr { pointee_type } => pointee_type.clone(),
                TypeAnnotation::SelfByRef => TypeAnnotation::simple_from_name("Self"),
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
                Op::Deref => self.build_deref(env, type_env, rhs.clone(), as_lvalue),
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

                    let lhs_ty = type_env.get(&lhs_val.ty).unwrap();
                    let rhs_ty = type_env.get(&rhs_val.ty).unwrap();

                    match (lhs_ty, rhs_ty) {
                        (Type::Int { .. }, Type::Int { .. }) => (
                            LLVMBuildAdd(
                                self.builder,
                                lhs_val.llvm_val,
                                rhs_val.llvm_val,
                                "".to_cstring().as_ptr(),
                            ),
                            lhs_val.ty,
                        ),
                        (Type::Ptr { pointee_type }, Type::Int { .. }) => {
                            // TODO type check and sext
                            let pointee_ty = type_env.get(pointee_type).unwrap();
                            (
                                LLVMBuildGEP2(
                                    self.builder,
                                    llvm_type(pointee_ty, type_env.clone()),
                                    lhs_val.llvm_val,
                                    [rhs_val.llvm_val].as_mut_ptr(),
                                    1,
                                    "".to_cstring().as_ptr(),
                                ),
                                lhs_val.ty,
                            )
                        }
                        _ => panic!("cannot add {} to {}", rhs_ty.name(), lhs_ty.name()),
                    }
                },
                Op::Sub => unsafe {
                    let lhs_val =
                        self.build_expr(env.clone(), type_env.clone(), lhs.clone(), false);
                    let rhs_val =
                        self.build_expr(env.clone(), type_env.clone(), rhs.clone(), false);

                    let lhs_ty = type_env.get(&lhs_val.ty).unwrap();
                    let rhs_ty = type_env.get(&rhs_val.ty).unwrap();

                    match (lhs_ty, rhs_ty) {
                        (Type::Int { .. }, Type::Int { .. }) => (
                            LLVMBuildSub(
                                self.builder,
                                lhs_val.llvm_val,
                                rhs_val.llvm_val,
                                "".to_cstring().as_ptr(),
                            ),
                            lhs_val.ty,
                        ),
                        (Type::Ptr { pointee_type }, Type::Int { .. }) => {
                            // TODO type check and sext
                            let pointee_ty = type_env.get(pointee_type).unwrap();
                            let offset = LLVMBuildNeg(
                                self.builder,
                                rhs_val.llvm_val,
                                "".to_cstring().as_ptr(),
                            );
                            (
                                LLVMBuildGEP2(
                                    self.builder,
                                    llvm_type(pointee_ty, type_env.clone()),
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
                        TypeAnnotation::Simple {
                            ident: "u32".into(),
                            type_args: [].into(),
                        }
                        .into(),
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
                        TypeAnnotation::Simple {
                            ident: "u32".into(),
                            type_args: [].into(),
                        }
                        .into(),
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
                        TypeAnnotation::Simple {
                            ident: "u32".into(),
                            type_args: [].into(),
                        }
                        .into(),
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
                        TypeAnnotation::Simple {
                            ident: "bool".into(),
                            type_args: [].into(),
                        }
                        .into(),
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
                        TypeAnnotation::Simple {
                            ident: "bool".into(),
                            type_args: [].into(),
                        }
                        .into(),
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
                        TypeAnnotation::Simple {
                            ident: "bool".into(),
                            type_args: [].into(),
                        }
                        .into(),
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
                        TypeAnnotation::Simple {
                            ident: "bool".into(),
                            type_args: [].into(),
                        }
                        .into(),
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
                        TypeAnnotation::Simple {
                            ident: "bool".into(),
                            type_args: [].into(),
                        }
                        .into(),
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
                        TypeAnnotation::Simple {
                            ident: "bool".into(),
                            type_args: [].into(),
                        }
                        .into(),
                    )
                },
                Op::Assign(op) => unsafe {
                    macro_rules! make_binop {
                        ($op:expr, $lhs:expr, $rhs: expr, $span: expr) => {
                            self.build_binop(
                                env.clone(),
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

                    let lhs_ty = type_env.get(&lhs_val.ty).unwrap();
                    let rhs_ty = type_env.get(&rhs_val.ty).unwrap();

                    if let (rhs_ty @ Type::Struct { .. }, _lhs_ty @ Type::Struct { .. }) =
                        (lhs_ty, rhs_ty)
                    {
                        // TODO this is to check whether rhs is a struct literal or not, find a better way
                        // for instance, this will not work if rhs is a struct member
                        // TODO use platform alignment
                        if let NodeKind::Ident { .. } = rhs.kind {
                            // FIXME redundant
                            let rhs_val =
                                self.build_expr(env.clone(), type_env.clone(), rhs.clone(), true);
                            let lhs_ptr = LLVMBuildBitCast(
                                self.builder,
                                lhs_val.llvm_val,
                                LLVMPointerType(LLVMInt8Type(), 0),
                                "".to_cstring().as_ptr(),
                            );
                            let rhs_ptr = LLVMBuildBitCast(
                                self.builder,
                                rhs_val.llvm_val,
                                LLVMPointerType(LLVMInt8Type(), 0),
                                "".to_cstring().as_ptr(),
                            );
                            LLVMBuildMemCpy(
                                self.builder,
                                lhs_ptr,
                                4,
                                rhs_ptr,
                                4,
                                // TODO this should be lhs_ty but it breaks if the structs are of different type/size, which we'll disallow anyways in which case lhs_ty == rhs_ty
                                LLVMSizeOf(llvm_type(rhs_ty, type_env.clone())),
                            )
                        } else {
                            LLVMBuildStore(self.builder, rhs_val.llvm_val, lhs_val.llvm_val)
                        }
                    } else {
                        LLVMBuildStore(self.builder, rhs_val.llvm_val, lhs_val.llvm_val)
                    };

                    (null_mut(), TypeAnnotation::simple_from_name("void"))
                },
                Op::Dot => unsafe {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), true);
                    let lhs_ty = type_env.get(&lhs_val.ty).unwrap();

                    match &lhs_ty.clone() {
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
                            field_types,
                            name: struct_name,
                            ..
                        } => match &rhs.kind {
                            NodeKind::Ident { name } => {
                                let field_idx = match field_indices.get(&**name) {
                                    Some(idx) => idx,
                                    None => panic!("{}\nno member {}", op_span, name),
                                };
                                let field_ty =
                                    if let Some(ty) = type_env.get(&field_types[*field_idx]) {
                                        ty
                                    } else {
                                        panic!(
                                            "unresolved type {} accessing {} in struct {}\n{}",
                                            &field_types[*field_idx], name, struct_name, op_span
                                        );
                                    };
                                let ptr = LLVMBuildStructGEP2(
                                    self.builder,
                                    llvm_type(lhs_ty, type_env.clone()),
                                    lhs_val.llvm_val,
                                    *field_idx as u32,
                                    "".to_cstring().as_ptr(),
                                );

                                if as_lvalue {
                                    (ptr, field_types[*field_idx].clone())
                                } else {
                                    let llvm_ty = if let Type::Fn { .. } = field_ty {
                                        LLVMPointerType(llvm_type(field_ty, type_env.clone()), 0)
                                    } else {
                                        llvm_type(field_ty, type_env.clone())
                                    };
                                    (
                                        LLVMBuildLoad2(
                                            self.builder,
                                            llvm_ty,
                                            ptr,
                                            "".to_cstring().as_ptr(),
                                        ),
                                        field_types[*field_idx].clone(),
                                    )
                                }
                            }
                            NodeKind::Call {
                                path: PathSegment { ident, generics },
                                args,
                            } => {
                                let func_ident =
                                    format!("{}::{}", struct_name.strip_generics(), ident);
                                let fn_decl = match self.get_fn_decl(func_ident.clone()) {
                                    Some(decl) => decl,
                                    None => todo!(),
                                };

                                let self_by_ref = match &fn_decl.1.kind {
                                    NodeKind::Fn { params, .. } => {
                                        matches!(*params[0].ty(), TypeAnnotation::SelfByRef)
                                    }
                                    _ => todo!(),
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

                                let local_type_env = TypeEnv::make_child(type_env.clone());

                                let self_ty = TypeAnnotation::simple_from_name("Self");

                                local_type_env.insert_local(self_ty.clone(), lhs_ty.clone());

                                local_type_env.insert_local(
                                    TypeAnnotation::SelfByRef.into(),
                                    Type::Ref {
                                        referent_type: self_ty,
                                    },
                                );

                                // Infer impl type args from lhs
                                let mut type_args: Vec<Rc<TypeAnnotation>> =
                                    struct_name.type_args().to_vec();
                                type_args.append(&mut generics.to_vec());

                                return self.build_call(
                                    env.clone(),
                                    local_type_env.into(),
                                    PathSegment {
                                        ident: func_ident.into(),
                                        generics: type_args.into(),
                                    },
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

                    let lhs_ty = type_env.get(&lhs_val.ty).unwrap();
                    let rhs_ty = type_env.get(&rhs_val.ty).unwrap();

                    match (&lhs_ty, &rhs_ty) {
                        (Type::Array { elem_type, .. }, Type::Int { .. }) => {
                            // TODO this and bounds check
                            // if !signed {
                            //     panic!("cannot index with signed int");
                            // }

                            let elem_ty = type_env.get(elem_type).unwrap();

                            let ptr = unsafe {
                                LLVMBuildInBoundsGEP2(
                                    self.builder,
                                    llvm_type(lhs_ty, type_env.clone()),
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
                                            llvm_type(elem_ty, type_env.clone()),
                                            ptr,
                                            "".to_cstring().as_ptr(),
                                        )
                                    }
                                },
                                elem_type.clone(),
                            )
                        }
                        _ => todo!(),
                    }
                }
                Op::ScopeRes => match (&lhs.kind, &rhs.kind) {
                    // TODO probably not the correct way to do this
                    (
                        NodeKind::Ident { name },
                        NodeKind::Call {
                            path,
                            args: fn_args,
                        },
                    ) => {
                        let mangled_name = format!("{}::{}", name, path.ident);
                        return self.build_call(
                            env,
                            type_env.clone(),
                            PathSegment {
                                ident: mangled_name.as_str().into(),
                                generics: path.generics.clone(),
                            },
                            fn_args,
                        );
                    }
                    _ => todo!(),
                },
                Op::Cast => {
                    let lhs_val = self.build_expr(env.clone(), type_env.clone(), lhs.clone(), true);
                    let lhs_ty = type_env.get(&lhs_val.ty).unwrap();
                    let rhs_ty_annotation = if let NodeKind::Type { ty } = &rhs.kind {
                        ty
                    } else {
                        todo!()
                    };

                    let rhs_ty = type_env.get(rhs_ty_annotation).unwrap();

                    match (lhs_ty, rhs_ty) {
                        (Type::Ptr { .. }, Type::Ptr { .. }) => {
                            (lhs_val.llvm_val, rhs_ty_annotation.clone())
                        }
                        (Type::Ref { referent_type }, Type::Ptr { pointee_type }) => {
                            if *referent_type == *pointee_type {
                                (lhs_val.llvm_val, pointee_type.clone())
                            } else {
                                todo!()
                            }
                        }
                        (Type::Ptr { pointee_type }, Type::Ref { referent_type }) => {
                            if *referent_type == *pointee_type {
                                (lhs_val.llvm_val, referent_type.clone())
                            } else {
                                todo!()
                            }
                        }
                        (Type::Struct { .. }, Type::Struct { name, .. }) => {
                            (lhs_val.llvm_val, name.clone())
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
                                    llvm_type(rhs_ty, type_env.clone()),
                                    if *signed_b { 1 } else { 0 },
                                    "".to_cstring().as_ptr(),
                                )
                            },
                            rhs_ty_annotation.clone(),
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
        path: PathSegment,
        arg_exprs: &[NodeRef],
    ) -> Val {
        // TODO funcs could be vars instead? or everything that can be resolved by a path could be an Item?
        let (llvm_ty, llvm_val, ret_ty) = if let Some(func) = env.get_func(&path.to_string()) {
            (func.llvm_type, func.val, func.ret_type.clone())
        } else if let Some(var) = env.get_var(&path.to_string()) {
            if let ty @ Type::Fn { ret_type, .. } = type_env.get(&var.ty).unwrap() {
                let llvm_val = unsafe {
                    LLVMBuildLoad2(
                        self.builder,
                        LLVMPointerType(llvm_type(ty, type_env.clone()), 0),
                        var.val,
                        "".to_cstring().as_ptr(),
                    )
                };
                (llvm_type(ty, type_env.clone()), llvm_val, ret_type.clone())
            } else {
                todo!()
            }
        } else if let Some(fn_decl) = self.get_fn_decl(path.ident.to_string()) {
            if let NodeKind::Fn { params, ret_ty, .. } = &fn_decl.1.kind {
                let substitutions: Vec<(Rc<TypeAnnotation>, Rc<TypeAnnotation>)> = fn_decl
                    .0
                    .generics
                    .iter()
                    .zip(path.generics.iter())
                    .map(|(ty, concrete_ty)| (ty.clone(), concrete_ty.clone()))
                    .collect();

                let concrete_ret_ty = if path.generics.len() > 0 {
                    ret_ty.substitute(&substitutions)
                } else {
                    ret_ty.clone()
                };
                let mut concrete_param_tys: Vec<Rc<TypeAnnotation>> = vec![];
                let concrete_params: Vec<FnParam> = params
                    .iter()
                    .map(|param| {
                        if let FnParam::Pair { ident, ty } = param {
                            let new_ty = if path.generics.len() > 0 {
                                ty.substitute(&substitutions)
                            } else {
                                ty.clone()
                            };
                            concrete_param_tys.push(new_ty.clone());
                            FnParam::Pair {
                                ident: ident.clone(),
                                ty: new_ty,
                            }
                        } else {
                            param.clone()
                        }
                    })
                    .collect();

                let local_type_env = TypeEnv::make_child(type_env.clone());
                for i in 0..path.generics.len() {
                    let ty = type_env.get(&path.generics[i]).unwrap();
                    local_type_env.insert_local(fn_decl.0.generics[i].clone(), ty.clone());
                }

                self.set_up_function(
                    env.clone(),
                    local_type_env.into(),
                    &path.to_string(),
                    concrete_params.into(),
                    concrete_ret_ty,
                    false,
                    None,
                    Some(fn_decl.1.clone()),
                );

                return self.build_call(env, type_env, path, arg_exprs);
            } else {
                todo!()
            }
        } else {
            panic!("unresolved fn {}", path);
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
                llvm_type(type_env.get(&elem_ty).unwrap(), type_env.clone()),
                elem_vals.as_mut_slice().as_mut_ptr(),
                elem_vals.len() as u64,
            )
        };

        Val {
            ty: TypeAnnotation::Array {
                element_type: elem_ty.clone(),
            }
            .into(),
            llvm_val,
        }
    }

    fn build_string(&mut self, value: Rc<str>) -> Val {
        let bytes: Vec<u8> = value.bytes().collect();

        let llvm_val = unsafe {
            LLVMBuildGlobalString(
                self.builder,
                bytes.as_slice().as_ptr() as *const i8,
                "".to_cstring().as_ptr(),
            )
        };

        Val {
            ty: TypeAnnotation::Array {
                element_type: TypeAnnotation::simple_from_name("u8"),
            }
            .into(),
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
                    ty: TypeAnnotation::Ref {
                        referent_type: TypeAnnotation::simple_from_name("void"),
                    }
                    .into(),
                    llvm_val: unsafe { LLVMConstPointerNull(LLVMPointerType(LLVMVoidType(), 0)) },
                }
            }
            NodeKind::Int { value } => unsafe {
                // FIXME int type
                // TODO sign extend
                let llvm_val = LLVMConstInt(LLVMInt32Type(), *value, 0);

                Val {
                    ty: TypeAnnotation::simple_from_name("u32"),
                    llvm_val,
                }
            },
            NodeKind::Bool { value } => unsafe {
                let llvm_val = LLVMConstInt(LLVMInt1Type(), if *value { 1 } else { 0 }, 0);

                Val {
                    ty: TypeAnnotation::simple_from_name("bool"),
                    llvm_val,
                }
            },
            NodeKind::Char { value } => unsafe {
                let llvm_val = LLVMConstInt(LLVMInt8Type(), **value as u64, 0);

                Val {
                    ty: TypeAnnotation::simple_from_name("u8"),
                    llvm_val,
                }
            },
            NodeKind::Ident { name } => unsafe {
                if let Some(var) = env.get_var(name) {
                    let llvm_val = if as_lvalue || var.is_const {
                        var.val
                    } else {
                        let var_ty = type_env.get(&var.ty).unwrap();
                        let llvm_ty = if let Type::Fn { .. } = var_ty {
                            LLVMPointerType(llvm_type(var_ty, type_env.clone()), 0)
                        } else {
                            llvm_type(var_ty, type_env.clone())
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
                } else if let Some(decl) = self.get_fn_decl(name.to_string()) {
                    todo!("got here because fn pointers...");
                } else {
                    panic!("unresolved ident {}", name)
                }
            },
            NodeKind::UnOp { .. } => self.build_unop(env, type_env, node, as_lvalue),
            NodeKind::BinOp { .. } => self.build_binop(env, type_env, node, as_lvalue),
            NodeKind::Call {
                path: path @ PathSegment { ident, generics },
                args,
            } => {
                if &**ident == "size_of" {
                    assert!(generics.len() == 1);
                    let ty_usize = TypeAnnotation::simple_from_name("u32"); // TODO usize
                    Val {
                        ty: ty_usize.clone(),
                        llvm_val: unsafe {
                            LLVMBuildIntCast2(
                                self.builder,
                                LLVMSizeOf(llvm_type(
                                    type_env.get(&generics[0]).unwrap(),
                                    type_env.clone(),
                                )),
                                llvm_type(type_env.clone().get(&ty_usize).unwrap(), type_env),
                                0,
                                "".to_cstring().as_ptr(),
                            )
                        },
                    }
                } else {
                    self.build_call(env, type_env, path.clone(), args)
                }
            }
            NodeKind::Array { elems } => self.build_array(env, type_env, elems),
            NodeKind::Str { value } => self.build_string(value.clone()),
            NodeKind::StructLiteral {
                path: path @ PathSegment { .. },
                fields,
            } => {
                // TODO this shares common behaviour with the dot operator on structs.
                // maybe have something like build_store_struct_member()
                // TODO in (for instance) let ... = T {...}, alloca and load here are redundant

                if let Some(ty @ Type::Struct { field_indices, .. }) =
                    type_env.get(&TypeAnnotation::Simple {
                        ident: path.ident.clone(),
                        type_args: path.generics.clone(),
                    })
                {
                    let func = self.env.get_func(&self.current_func_ident.clone().unwrap());

                    // TODO this is also used in 'let'. could be a helper function like build_alloca(...)
                    let reg = unsafe {
                        let bb_current = LLVMGetInsertBlock(self.builder);

                        LLVMPositionBuilderAtEnd(self.builder, func.unwrap().bb_entry.unwrap());

                        let reg = LLVMBuildAlloca(
                            self.builder,
                            llvm_type(ty, type_env.clone()),
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
                            unsafe { LLVMPointerType(llvm_type(ty, type_env.clone()), 0) }
                        } else {
                            llvm_type(ty, type_env.clone())
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
                                llvm_type(ty, type_env.clone()),
                                reg,
                                "".to_cstring().as_ptr(),
                            )
                        }
                    };

                    Val {
                        ty: TypeAnnotation::simple_from_name(&path.to_string()),
                        llvm_val,
                    }
                } else {
                    panic!("{}\nunresolved type {}", node.span, path);
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
                    ty: TypeAnnotation::simple_from_name("void"),
                    llvm_val,
                }
            }
            NodeKind::Let {
                ty: type_annotation,
                lhs,
                rhs,
            } => unsafe {
                // TODO alloca the var and let assign do the rest?
                if let NodeKind::Ident { name } = &lhs.kind {
                    let var_ty = match type_env.get(type_annotation) {
                        t @ Some(_) => t,
                        None => panic!("unknown type {}", type_annotation),
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
                        (None, Some(val)) => type_env.get(&val.ty).unwrap().clone(),
                        (None, None) => {
                            panic!("cannot infer type for let");
                        }
                    };

                    let llvm_ty = if let t @ Type::Fn { .. } = ty.clone() {
                        LLVMPointerType(llvm_type(&t, type_env.clone()), 0) // TODO Type::llvm_ptr_type()
                    } else {
                        llvm_type(&ty, type_env.clone())
                    };

                    LLVMPositionBuilderAtEnd(self.builder, func.unwrap().bb_entry.unwrap());
                    let reg = LLVMBuildAlloca(self.builder, llvm_ty, "".to_cstring().as_ptr());
                    LLVMPositionBuilderAtEnd(self.builder, bb_current);

                    env.insert_var(name, reg, type_annotation.clone());

                    if let Some(val) = rhs_val {
                        LLVMBuildStore(self.builder, val.llvm_val, reg);
                    };

                    // TODO llvm_val or val should be optional
                    Val {
                        ty: TypeAnnotation::simple_from_name(""),
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
                        ty: TypeAnnotation::simple_from_name("void"),
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

                    self.break_block = Some(bb_exit);
                    self.continue_block = Some(bb_test);

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

                    self.break_block = None;
                    self.continue_block = None;

                    Val {
                        ty: TypeAnnotation::simple_from_name("void"),
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
                        ty: TypeAnnotation::simple_from_name("void"),
                        llvm_val: null_mut(),
                    }
                } else {
                    panic!("match stmt outside fn")
                }
            }
            NodeKind::Continue => {
                if let Some(bb) = self.continue_block {
                    unsafe { LLVMBuildBr(self.builder, bb) };
                } else {
                    panic!("{}\ncontinue outside loop body", node.span);
                }

                Val {
                    ty: TypeAnnotation::simple_from_name("void"),
                    llvm_val: null_mut(),
                }
            }
            NodeKind::Break => {
                if let Some(bb) = self.break_block {
                    unsafe { LLVMBuildBr(self.builder, bb) };
                } else {
                    panic!("{}\nbreak outside loop body", node.span);
                }

                Val {
                    ty: TypeAnnotation::simple_from_name("void"),
                    llvm_val: null_mut(),
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
                match &stmt.kind {
                    NodeKind::Return { .. } | &NodeKind::Break | &NodeKind::Continue => {
                        if i == statements.len() - 1 {
                            returns = true;
                        } else {
                            panic!("{}\nunreachable code following statement", stmt.span);
                        }
                    }
                    _ => (),
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
        params: Rc<[FnParam]>,
        ret_ty: Rc<TypeAnnotation>,
        is_extern: bool,
        _linkage: Option<Rc<str>>,
        node: Option<NodeRef>,
    ) {
        println!("setting up fn {}", ident);
        let ret_type = match type_env.get(&ret_ty) {
            Some(ty) => ty.clone(),
            None => panic!("unresolved type {} setting up fn {}", ret_ty, ident),
        };

        let mut param_types: Vec<Rc<TypeAnnotation>> = Vec::new();
        let mut llvm_param_types: Vec<LLVMTypeRef> = Vec::new();
        for param in params.iter() {
            if let Some(ty) = type_env.get(&param.ty()) {
                param_types.push(param.ty());
                let llvm_type = if let Type::Fn { .. } = ty {
                    unsafe { LLVMPointerType(llvm_type(ty, type_env.clone()), 0) }
                } else {
                    llvm_type(ty, type_env.clone())
                };
                llvm_param_types.push(llvm_type);
            } else {
                panic!("unresolved type {}", &param.ty());
            }
        }
        let func_type = unsafe {
            LLVMFunctionType(
                llvm_type(&ret_type, type_env.clone()),
                llvm_param_types.as_mut_slice().as_mut_ptr(),
                llvm_param_types.len().try_into().unwrap(),
                0,
            )
        };
        let val =
            unsafe { LLVMAddFunction(self.llvm_module, ident.to_cstring().as_ptr(), func_type) };

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

        // this needs to be global
        self.env.insert_func(
            ident,
            Func {
                ty: TypeAnnotation::Fn {
                    params: param_types.clone().into(),
                    return_type: ret_ty.clone(),
                }
                .into(),
                env: Rc::new(fn_env),
                type_env: type_env.clone(),
                ret_type: ret_ty,
                val,
                llvm_type: func_type,
                bb_entry,
                bb_body,
                node,
            },
        );
        self.fns_to_build.push(ident.to_owned());
    }

    fn build_function(
        &mut self,
        env: Rc<Env>,
        type_env: Rc<TypeEnv>,
        ident: Rc<str>,
        params: Rc<[FnParam]>,
        body: NodeRef,
    ) {
        println!("building {}", ident);
        let func = env.get_func(&ident).unwrap();
        if let (Some(bb_entry), Some(bb_body)) = (func.bb_entry, func.bb_body) {
            self.current_func_ident = Some(ident.clone());
            unsafe { LLVMPositionBuilderAtEnd(self.builder, bb_entry) };

            for (i, param) in params.iter().enumerate() {
                let ty = match type_env.get(&param.ty()) {
                    Some(ty) => ty,
                    None => panic!("unresolved type {}", param.ty()),
                };

                let llvm_ty = if let Type::Fn { .. } = ty {
                    unsafe { LLVMPointerType(llvm_type(ty, type_env.clone()), 0) }
                } else {
                    llvm_type(ty, type_env.clone())
                };

                let param_ptr =
                    unsafe { LLVMBuildAlloca(self.builder, llvm_ty, "".to_cstring().as_ptr()) };
                unsafe {
                    LLVMBuildStore(
                        self.builder,
                        LLVMGetParam(func.val, i.try_into().unwrap()),
                        param_ptr,
                    )
                };
                func.env.insert_var(&param.ident(), param_ptr, param.ty());
            }

            unsafe { LLVMPositionBuilderAtEnd(self.builder, bb_body) };

            self.build_block(func.env.clone(), func.type_env.clone(), body.clone());
            if *type_env.get(&func.ret_type).unwrap() == Type::Void {
                unsafe { LLVMBuildRetVoid(self.builder) };
            }

            unsafe {
                LLVMPositionBuilderAtEnd(self.builder, bb_entry);
                LLVMBuildBr(self.builder, bb_body);
            }

            self.current_func_ident = None;
        }
    }

    fn pass1(&mut self) {
        for node in &*self.ast {
            match &node.kind {
                NodeKind::Const {
                    ty: type_annotation,
                    lhs,
                    rhs,
                } => {
                    if let NodeKind::Ident { name } = &lhs.kind {
                        let ty = match self.type_env.get(type_annotation) {
                            Some(t) => t,
                            None => panic!("unknown type {}", type_annotation),
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
                                    LLVMConstInt(llvm_type(ty, self.type_env.clone()), *value, 0)
                                },
                                type_annotation.clone(),
                            );
                        } else {
                            unimplemented!()
                        }
                    } else {
                        panic!()
                    }
                }
                NodeKind::Struct {
                    ident,
                    generics,
                    attributes,
                    fields,
                    ..
                } => {
                    let mut field_indices: HashMap<String, usize> = HashMap::new();
                    let mut field_types: Vec<Rc<TypeAnnotation>> = Vec::new();
                    for (idx, field) in fields.iter().enumerate() {
                        field_types.push(field.ty.clone());
                        field_indices.insert(field.ident.to_string(), idx);
                    }

                    let name = Rc::from(TypeAnnotation::Simple {
                        ident: ident.clone(),
                        type_args: [].into(),
                    });

                    self.type_env.insert(
                        name.clone(),
                        Type::Struct {
                            name,
                            field_indices,
                            field_types,
                            type_params: generics.clone(),
                            attributes: attributes.clone(),
                        },
                    );
                }
                NodeKind::Fn {
                    ident, generics, ..
                } => {
                    println!("registering fn decl {}", ident);
                    self.push_fn_decl(
                        ident.to_string(),
                        PathSegment {
                            ident: ident.clone(),
                            generics: generics.clone(),
                        },
                        node.clone(),
                    );

                    if &**ident == "main" {
                        self.push_fn_specialization(
                            PathSegment {
                                ident: "main".into(),
                                generics: [].as_slice().into(),
                            },
                            node.clone(),
                        );
                    }
                }
                NodeKind::Impl {
                    ty,
                    methods,
                    generics: impl_generics,
                } => {
                    for node in methods.iter() {
                        if let NodeKind::Fn {
                            ident,
                            generics: fn_generics,
                            ..
                        } = &node.kind
                        {
                            let fn_ident = ty.strip_generics().to_string() + "::" + ident.as_ref();
                            let mut generics: Vec<Rc<TypeAnnotation>> = impl_generics.to_vec();
                            generics.append(&mut fn_generics.to_vec());

                            println!("registering fn decl {}", fn_ident);
                            self.push_fn_decl(
                                fn_ident,
                                PathSegment {
                                    ident: ident.clone(),
                                    generics: generics.into(),
                                },
                                node.clone(),
                            );
                        }
                    }
                }
                _ => (),
            }
        }
    }

    fn set_up_fns(&mut self) {
        while let Some((spec, node)) = self.get_fn_specializations().pop_front() {
            if let NodeKind::Fn { params, ret_ty, .. } = &node.kind {
                println!("setting up fn {}\nspecs:", spec.ident);
                assert_eq!(spec.generics.len(), spec.generics.len());
                println!("{}", spec);
                let type_env = TypeEnv::make_child(self.type_env.clone());
                for (ty_param, ty_arg) in spec.generics.iter().zip(spec.generics.iter()) {
                    type_env.insert_local(
                        Rc::unwrap_or_clone(ty_param.clone().into()),
                        type_env.get(ty_arg).unwrap().clone(),
                    );
                }
                self.set_up_function(
                    self.env.clone(),
                    type_env.into(),
                    &spec.to_string(),
                    params.clone(),
                    ret_ty.clone(),
                    false,
                    None,
                    Some(node.clone()),
                )
            }
        }
        println!();

        // TODO collect this in pass1, don't walk the ast again
        for node in &*self.ast.clone() {
            if let NodeKind::ExternBlock { linkage, block } = &node.kind {
                if let NodeKind::Block { statements } = &block.kind {
                    for stmt in statements.iter() {
                        if let NodeKind::Fn {
                            ident,
                            params,
                            ret_ty,
                            ..
                        } = &stmt.kind
                        {
                            self.set_up_function(
                                self.env.clone(),
                                self.type_env.clone(),
                                ident,
                                params.clone(),
                                ret_ty.clone(),
                                true,
                                linkage.clone(),
                                Some(node.clone()),
                            )
                        } else {
                            todo!()
                        }
                    }
                }
            }
        }
    }

    fn build_fns(&mut self) {
        while let Some(func_ident) = self.fns_to_build.pop() {
            let func = unsafe { &*self.env.funcs.get() }.get(&func_ident).unwrap();
            if let Some(Node {
                kind:
                    NodeKind::Fn {
                        params,
                        body: Some(body),
                        ..
                    },
                ..
            }) = func.node.as_deref()
            {
                self.build_function(
                    self.env.clone(),
                    func.type_env.clone(),
                    func_ident.into(),
                    params.clone(),
                    body.clone(),
                )
            }
        }
    }

    pub fn build(&mut self) {
        self.pass1();
        self.set_up_fns();
        self.build_fns();
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
