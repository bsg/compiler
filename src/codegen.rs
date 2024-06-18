use llvm_sys::core::*;
use llvm_sys::prelude::*;
use std::collections::HashMap;
use std::ffi::CString;

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
}

pub struct Func {
    val: LLVMValueRef,
    ty: LLVMTypeRef,
}

pub struct Env {
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

        Env {
            vars: HashMap::new(),
            types,
            funcs: HashMap::new(),
        }
    }

    pub fn insert_type(&mut self, ident: &str, ty: LLVMTypeRef) {
        self.types.insert(ident.to_string(), ty);
    }

    pub fn get_type(&mut self, ident: &str) -> Option<&LLVMTypeRef> {
        self.types.get(ident)
    }

    pub fn insert_var(&mut self, ident: &str, val: LLVMValueRef, ty: LLVMTypeRef) {
        self.vars.insert(ident.to_string(), Var { val, ty });
    }

    pub fn get_var(&mut self, ident: &str) -> Option<&Var> {
        self.vars.get(ident)
    }

    pub fn insert_func(&mut self, ident: &str, val: LLVMValueRef, ty: LLVMTypeRef) {
        println!("insert_func {}", ident);
        self.funcs.insert(ident.to_string(), Func { val, ty });
    }

    pub fn get_func(&mut self, ident: &str) -> Option<&Func> {
        self.funcs.get(ident)
    }
}

pub struct ModuleBuilder {
    name: String,
    module: LLVMModuleRef,
    builder: LLVMBuilderRef,
    env: Env,
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
            env: Env::new(),
        }
    }

    fn build_value(&mut self, node: NodeRef) -> LLVMValueRef {
        match &*node {
            Node::Int(i) => {
                // FIXME int type
                // TODO sign extend
                unsafe { LLVMConstInt(LLVMInt32Type(), i.value.try_into().unwrap(), 0) }
            }
            _ => unimplemented!(),
        }
    }

    fn build_binop(&mut self, node: BinOpNode) -> LLVMValueRef {
        match node.op {
            Op::Add => unsafe {
                LLVMBuildAdd(
                    self.builder,
                    self.build_expr(node.lhs),
                    self.build_expr(node.rhs),
                    "".to_cstring().as_ptr(),
                )
            },
            Op::Sub => unsafe {
                LLVMBuildSub(
                    self.builder,
                    self.build_expr(node.lhs),
                    self.build_expr(node.rhs),
                    "".to_cstring().as_ptr(),
                )
            },
            Op::Mul => unsafe {
                LLVMBuildMul(
                    self.builder,
                    self.build_expr(node.lhs),
                    self.build_expr(node.rhs),
                    "".to_cstring().as_ptr(),
                )
            },
            Op::Div => unsafe {
                // TODO
                LLVMBuildUDiv(
                    self.builder,
                    self.build_expr(node.lhs),
                    self.build_expr(node.rhs),
                    "".to_cstring().as_ptr(),
                )
            },
            _ => unimplemented!(),
        }
    }

    fn build_expr(&mut self, node: NodeRef) -> LLVMValueRef {
        match &*node {
            Node::Int(_) => self.build_value(node),
            Node::Ident(ident) => unsafe {
                let var = self.env.get_var(&ident.name).unwrap();
                LLVMBuildLoad2(self.builder, var.ty, var.val, "".to_cstring().as_ptr())
            },
            Node::BinOp(op) => self.build_binop(op.clone()),
            Node::Call(call) => {
                // TODO return type etc is hardcoded rn. traverse ast and build symtable for use here
                // will also need to build fns without bodies first to act as prototypes
                // TODO LLVMGetNamedFunction for extern fns
                let func = self.env.get_func(&call.ident.name).unwrap();
                unsafe {
                    LLVMBuildCall2(
                        self.builder,
                        func.ty,
                        func.val,
                        core::ptr::null_mut(),
                        0,
                        "".to_cstring().as_ptr(),
                    )
                }
            }
            _ => unimplemented!(),
        }
    }

    fn build_stmt(&mut self, node: NodeRef) -> LLVMValueRef {
        match &*node {
            Node::Return(r) => {
                if let Some(rhs) = &r.stmt {
                    let v = self.build_expr(rhs.clone());
                    unsafe { LLVMBuildRet(self.builder, v) }
                } else {
                    unsafe { LLVMBuildRetVoid(self.builder) }
                }
            }
            Node::Let(l) => unsafe {
                if let Node::Ident(ident) = &*l.lhs {
                    let reg = LLVMBuildAlloca(
                        self.builder,
                        *self.env.get_type(&l.ty).unwrap(),
                        "".to_cstring().as_ptr(),
                    );
                    let rhs = self.build_expr(l.rhs.clone());
                    let ty = *self.env.get_type(&l.ty).unwrap();
                    self.env.insert_var(&ident.name, reg, ty);
                    LLVMBuildStore(self.builder, rhs, reg)
                } else {
                    panic!()
                }
            },
            _ => unimplemented!(),
        }
    }

    fn build_block(&mut self, node: NodeRef) {
        if let Node::Block(block) = &*node {
            for stmt in block.statements.iter() {
                self.build_stmt(stmt.clone());
            }
        } else {
            panic!()
        }
    }

    pub fn build_func(&mut self, node: NodeRef) {
        if let Node::Fn(func) = &*node {
            let fn_type = self.env.get_type(&func.ret_ty).unwrap();
            let function_type = unsafe { LLVMFunctionType(*fn_type, [].as_mut_ptr(), 0, 0) };
            let function = unsafe {
                LLVMAddFunction(self.module, func.ident.to_cstring().as_ptr(), function_type)
            };
            self.env.insert_func(&func.ident, function, function_type);
            let entry_block =
                unsafe { LLVMAppendBasicBlock(function, "".to_string().to_cstring().as_ptr()) };
            unsafe { LLVMPositionBuilderAtEnd(self.builder, entry_block) };
            self.build_block(func.body.clone());
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
