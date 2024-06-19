use std::{collections::HashMap, fs};

use ast::{BinOpNode, IfNode, Node, NodeRef, Op};
use clap::Parser;
use llvm_sys::target_machine::{
    LLVMGetDefaultTargetTriple, LLVMGetFirstTarget, LLVMGetHostCPUName,
};

mod ast;
mod lexer;
mod parser;
mod codegen;

use llvm_sys::core::*;
use llvm_sys::target_machine::*;

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

    unsafe {
        if llvm_sys::target::LLVM_InitializeNativeTarget() != 0 {
            panic!();
        }

        if llvm_sys::target::LLVM_InitializeNativeAsmPrinter() != 0 {
            panic!()
        }
    };

    let code = fs::read_to_string(args.path.unwrap()).unwrap();
    let ast = crate::parser::Parser::new(&code).parse();

    let mut module = codegen::ModuleBuilder::new("hello");
    module.build_symtable(ast.as_slice());
    for node in ast {
        module.build_func(node);
    }

    unsafe {
        LLVMPrintModuleToFile(
            module.get_llvm_module_ref(),
            core::ffi::CStr::from_bytes_with_nul(b"out.ll\0")
                .unwrap()
                .as_ptr(),
            core::ptr::null_mut(),
        )
    };

    let triple = unsafe { LLVMGetDefaultTargetTriple() };
    let cpu = unsafe { LLVMGetHostCPUName() };
    let machine = unsafe {
        LLVMCreateTargetMachine(
            LLVMGetFirstTarget(),
            triple,
            cpu,
            LLVMGetHostCPUFeatures(),
            LLVMCodeGenOptLevel::LLVMCodeGenLevelNone,
            LLVMRelocMode::LLVMRelocDefault,
            LLVMCodeModel::LLVMCodeModelDefault,
        )
    };

    unsafe {
        let mut err = core::ptr::null_mut();
        let res = LLVMTargetMachineEmitToFile(
            machine,
            module.get_llvm_module_ref(),
            core::ffi::CStr::from_bytes_with_nul(b"hello.o\0")
                .unwrap()
                .as_ptr() as *mut i8,
            LLVMCodeGenFileType::LLVMObjectFile,
            &mut err,
        );

        if res == 1 {
            panic!("{:?}", core::ffi::CStr::from_ptr(err));
        }
    };

    unsafe { LLVMDisposeMessage(triple) };
    unsafe { LLVMDisposeMessage(cpu) };
}
