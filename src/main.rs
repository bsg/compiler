use std::fs;
use std::ptr::null_mut;

use clap::Parser;
use llvm_sys::analysis::LLVMVerifyModule;
use llvm_sys::target_machine::{
    LLVMGetDefaultTargetTriple, LLVMGetFirstTarget, LLVMGetHostCPUName,
};

mod ast;
mod codegen;
mod lexer;
mod parser;
mod type_env;

use llvm_sys::core::*;
use llvm_sys::target_machine::*;
use llvm_sys::transforms::pass_builder::{LLVMCreatePassBuilderOptions, LLVMRunPasses};

#[derive(Parser)]
#[command()]
struct Args {
    path: Option<String>,
    #[clap(long, action)]
    ast: bool,
    #[clap(long, action)]
    asm: bool,
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

    if args.ast {
        let mut s = String::new();
        for node in ast.iter() {
            s += format!("{:?}\n", node).as_str();
        }
        fs::write("ast.txt", s).unwrap();
    }

    let mut module = codegen::ModuleBuilder::new("main", ast);
    module.build();

    unsafe {
        LLVMVerifyModule(
            module.get_llvm_module_ref(),
            llvm_sys::analysis::LLVMVerifierFailureAction::LLVMPrintMessageAction,
            null_mut(),
        )
    };

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
            LLVMCodeGenOptLevel::LLVMCodeGenLevelDefault,
            LLVMRelocMode::LLVMRelocDefault,
            LLVMCodeModel::LLVMCodeModelDefault,
        )
    };

    unsafe {
        LLVMRunPasses(
            module.get_llvm_module_ref(),
            core::ffi::CStr::from_bytes_with_nul(b"default<O3>\0")
                .unwrap()
                .as_ptr() as *mut i8,
            machine,
            LLVMCreatePassBuilderOptions(),
        )
    };

    unsafe {
        let mut err = core::ptr::null_mut();
        let res = LLVMTargetMachineEmitToFile(
            machine,
            module.get_llvm_module_ref(),
            core::ffi::CStr::from_bytes_with_nul(if args.asm { b"main.s\0" } else { b"main.o\0" })
                .unwrap()
                .as_ptr() as *mut i8,
            if args.asm {
                LLVMCodeGenFileType::LLVMAssemblyFile
            } else {
                LLVMCodeGenFileType::LLVMObjectFile
            },
            &mut err,
        );

        if res == 1 {
            panic!("{:?}", core::ffi::CStr::from_ptr(err));
        }

        LLVMPrintModuleToFile(
            module.get_llvm_module_ref(),
            core::ffi::CStr::from_bytes_with_nul(b"out.opt.ll\0")
                .unwrap()
                .as_ptr(),
            core::ptr::null_mut(),
        )
    };

    unsafe { LLVMDisposeMessage(triple) };
    unsafe { LLVMDisposeMessage(cpu) };
}
