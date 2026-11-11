//! Symbol visibility of WebAssembly side modules.
//!
//! The Emscripten dynamic linker resolves the symbols that side modules export
//! globally, by name: when a module refers to a symbol it exports itself (in
//! position independent code through a GOT entry), it gets the definition of
//! the module that was loaded first. Every OSDI library defines symbols of the
//! same names (`eval_0`, `osdi_log`, `OSDI_LIM_TABLE`, ...), so all libraries
//! but the first would call the functions of the first library (the function
//! pointers in their descriptors) and use its data.
//!
//! Therefore a library refers only to hidden symbols, which the linker resolves
//! within the library: everything but the OSDI interface is hidden, and the
//! data of the OSDI interface is defined under a hidden name and exported
//! through an alias.

use std::ffi::CString;
use std::ptr::NonNull;

use llvm_sys::core::{
    LLVMAddAlias2, LLVMGetFirstFunction, LLVMGetFirstGlobal, LLVMGetLinkage, LLVMGetNextFunction,
    LLVMGetNextGlobal, LLVMGetValueName2, LLVMGlobalGetValueType, LLVMIsDeclaration,
    LLVMSetLinkage, LLVMSetValueName2, LLVMSetVisibility,
};
use llvm_sys::prelude::LLVMValueRef;
use llvm_sys::{LLVMLinkage, LLVMVisibility};
use mir_llvm::ModuleLlvm;
use target::spec::Target;

/// Whether the target needs [`localize_symbols`].
pub fn needs_local_symbols(target: &Target) -> bool {
    target.arch == "wasm32"
}

/// Symbols a simulator looks up in an OSDI library (dlsym).
fn is_osdi_interface(name: &str) -> bool {
    name.starts_with("OSDI_") || name == "osdi_log"
}

/// Suffix of the hidden definition behind an exported OSDI interface symbol.
const INTERNAL_SUFFIX: &str = ".internal";

unsafe fn name(val: LLVMValueRef) -> String {
    let mut len = 0;
    let ptr = LLVMGetValueName2(val, &mut len);
    String::from_utf8_lossy(std::slice::from_raw_parts(ptr as *const u8, len)).into_owned()
}

unsafe fn rename(val: LLVMValueRef, name: &str) {
    LLVMSetValueName2(val, name.as_ptr() as *const _, name.len());
}

/// Whether the symbol is visible outside of its object file.
unsafe fn is_global_symbol(val: LLVMValueRef) -> bool {
    !matches!(
        LLVMGetLinkage(val),
        LLVMLinkage::LLVMInternalLinkage | LLVMLinkage::LLVMPrivateLinkage
    )
}

/// Makes the module refer only to symbols that are resolved within the
/// library, see the module documentation. Run on each object of a library
/// before it is optimized and emitted.
pub fn localize_symbols(llmod: &ModuleLlvm) {
    unsafe {
        let llmod = NonNull::from(llmod.llmod()).as_ptr();

        // Functions: the library only exports data. Declarations are kept as
        // they are, they are defined in other objects of the library (then
        // hidden there, which the linker uses) or imported from the C library.
        let mut fun = LLVMGetFirstFunction(llmod);
        while !fun.is_null() {
            if LLVMIsDeclaration(fun) == 0 && is_global_symbol(fun) {
                LLVMSetVisibility(fun, LLVMVisibility::LLVMHiddenVisibility);
            }
            fun = LLVMGetNextFunction(fun);
        }

        // Collect the globals first, aliases are added while processing them
        let mut globals = Vec::new();
        let mut global = LLVMGetFirstGlobal(llmod);
        while !global.is_null() {
            globals.push(global);
            global = LLVMGetNextGlobal(global);
        }

        for global in globals {
            if !is_global_symbol(global) {
                continue;
            }
            let global_name = name(global);
            let defined = LLVMIsDeclaration(global) == 0;
            if is_osdi_interface(&global_name) {
                // References (here and in the other objects) go to the hidden
                // definition, the simulator finds the exported alias.
                let internal = format!("{global_name}{INTERNAL_SUFFIX}");
                rename(global, &internal);
                LLVMSetVisibility(global, LLVMVisibility::LLVMHiddenVisibility);
                if defined {
                    let alias_name = CString::new(global_name).unwrap();
                    let alias = LLVMAddAlias2(
                        llmod,
                        LLVMGlobalGetValueType(global),
                        0,
                        global,
                        alias_name.as_ptr(),
                    );
                    LLVMSetLinkage(alias, LLVMLinkage::LLVMExternalLinkage);
                }
            } else if defined {
                LLVMSetVisibility(global, LLVMVisibility::LLVMHiddenVisibility);
            }
        }
    }
}
