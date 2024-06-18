use core::ffi::CStr;
use llvm_sys::core::*;
use llvm_sys::prelude::*;
use llvm_sys::LLVMValue;
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

pub struct Module {
    name: String,
    module: LLVMModuleRef,
    builder: LLVMBuilderRef,
    types: HashMap<String, LLVMTypeRef>,
}

impl Module {
    pub fn new(name: &str) -> Self {
        let mod_name = CStr::from_bytes_with_nul(format!("{}\0", name).as_bytes())
            .unwrap()
            .as_ptr();
        let module = unsafe { LLVMModuleCreateWithName(mod_name) };
        let builder = unsafe { LLVMCreateBuilder() };

        let mut types = HashMap::new();
        types.insert("void".to_owned(), unsafe { LLVMVoidType() });
        types.insert("u32".to_owned(), unsafe { LLVMInt32Type() });
        types.insert("i32".to_owned(), unsafe { LLVMInt32Type() });

        Self {
            name: name.to_owned(),
            module,
            builder,
            types,
        }
    }

    fn build_value(&mut self, node: NodeRef) -> LLVMValueRef {
        match &*node {
            Node::Int(i) => {
                // FIXME int type
                unsafe { LLVMConstInt(LLVMInt32Type(), i.value.try_into().unwrap(), 0) }
            },
            _ => unimplemented!()
        }
    }

    fn build_block(&mut self, node: NodeRef) {
        if let Node::Block(block) = &*node {
            for stmt in block.statements.iter() {
                match &**stmt {
                    Node::Return(r) => {
                        let v = self.build_value(r.stmt.clone().unwrap());
                        unsafe { LLVMBuildRet(self.builder, v) };
                    },
                    _ => unimplemented!()
                };
            }
        } else {
            panic!()
        }
    }

    pub fn build_func(&mut self, node: NodeRef) {
        if let Node::Fn(func) = &*node {
            let fn_type = self.types.get("void").unwrap();
            let function_type = unsafe { LLVMFunctionType(*fn_type, [].as_mut_ptr(), 0, 0) };
            let function = unsafe {
                LLVMAddFunction(self.module, func.ident.to_cstring().as_ptr(), function_type)
            };
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

impl Drop for Module {
    fn drop(&mut self) {
        unsafe { LLVMDisposeBuilder(self.builder) };
    }
}
