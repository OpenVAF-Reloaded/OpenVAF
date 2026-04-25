use std::cell::{Cell, RefCell};
use std::ffi::CString;
use std::ptr::NonNull;

use ahash::AHashMap;
use lasso::{Rodeo, Spur};
use libc::c_char;
#[cfg(feature = "llvm18")]
use libc::c_uint;
use llvm_sys::bit_reader::LLVMParseBitcodeInContext2;
//use llvm_sys::LLVMBool; // For False, if applicable
use llvm_sys::core::{LLVMCreateMemoryBufferWithMemoryRange, LLVMGetNamedFunction};
use llvm_sys::linker::LLVMLinkModules2;
use llvm_sys::{LLVMType as Type, LLVMValue as Value};
use target::spec::Target;

use crate::types::Types;
use crate::LLVMString;

pub struct CodegenCx<'a, 'll> {
    pub llmod: &'ll llvm_sys::LLVMModule,
    pub llcx: &'ll llvm_sys::LLVMContext,

    pub target: &'a Target,
    // pub target_cpu: &'a str,
    pub literals: &'a Rodeo,
    str_lit_cache: RefCell<AHashMap<Spur, &'ll Value>>,
    pub(crate) intrinsics: RefCell<AHashMap<&'static str, (&'ll Type, &'ll Value)>>,
    pub(crate) local_gen_sym_counter: Cell<u32>,
    pub(crate) tys: Types<'ll>,
}

impl<'a, 'll> CodegenCx<'a, 'll> {
    pub(crate) fn new(
        literals: &'a Rodeo,
        llvm_module: &'ll crate::ModuleLlvm,
        target: &'a Target,
        // target_cpu: &'a str,
    ) -> CodegenCx<'a, 'll> {
        // let ty_isize =
        //     unsafe { llvm_sys::core::LLVMIntTypeInContext(llvm_module.llcx, target.pointer_width) };
        CodegenCx {
            llmod: llvm_module.llmod(),
            llcx: unsafe { &*llvm_module.llcx },
            str_lit_cache: RefCell::new(AHashMap::with_capacity(literals.len())),
            literals,
            intrinsics: RefCell::new(AHashMap::new()),
            local_gen_sym_counter: Cell::new(0),
            // target_cpu,
            target,
            tys: Types::new(unsafe { &*llvm_module.llcx }, target.pointer_width),
        }
    }

    pub fn get_func_by_name(&self, name: &str) -> Option<&'ll Value> {
        let name = CString::new(name).unwrap();
        unsafe {
            let ptr = LLVMGetNamedFunction(NonNull::from(self.llmod).as_ptr(), name.as_ptr());
            if ptr.is_null() {
                None
            } else {
                Some(&*(ptr as *const Value))
            }
        }
    }

    pub fn include_bitcode(&self, bitcode: &[u8]) {
        let sym = self.generate_local_symbol_name("bitcode_buffer");
        let sym = CString::new(sym).unwrap();
        unsafe {
            let buff = LLVMCreateMemoryBufferWithMemoryRange(
                bitcode.as_ptr() as *const c_char,
                bitcode.len(),
                sym.as_ptr(),
                0,
            );
            let mut module: *mut llvm_sys::LLVMModule = std::ptr::null_mut();
            assert!(
                LLVMParseBitcodeInContext2(NonNull::from(self.llcx).as_ptr(), buff, &mut module)
                    == 0,
                "failed to parse bitcode"
            );
            assert!(!module.is_null(), "parsed module is null");
            assert!(
                LLVMLinkModules2(NonNull::from(self.llmod).as_ptr(), module) == 0,
                "failed to link parsed bitcode"
            );
        }
    }
    pub fn to_str(&self) -> LLVMString {
        unsafe {
            LLVMString::new(llvm_sys::core::LLVMPrintModuleToString(
                NonNull::from(self.llmod).as_ptr(),
            ))
        }
    }

    pub fn const_str_uninterned(&self, lit: &str) -> &'ll Value {
        let lit = self.literals.get(lit).unwrap();
        self.const_str(lit)
    }

    pub fn const_str(&self, lit: Spur) -> &'ll Value {
        if let Some(val) = self.str_lit_cache.borrow().get(&lit) {
            return val;
        }

        let val = self.literals.resolve(&lit).as_bytes().to_owned();

        // assert!(!val.contains(&b'\0'));
        // val.push(b'\0');
        // LLVM 18 uses LLVMConstStringInContext, LLVM 19+ uses LLVMConstStringInContext2
        #[cfg(feature = "llvm18")]
        let val = unsafe {
            llvm_sys::core::LLVMConstStringInContext(
                NonNull::from(self.llcx).as_ptr(),
                val.as_ptr() as *const c_char,
                val.len() as c_uint,
                0,
            )
        };
        #[cfg(any(feature = "llvm19", feature = "llvm20", feature = "llvm21", feature = "llvm22"))]
        let val = unsafe {
            llvm_sys::core::LLVMConstStringInContext2(
                NonNull::from(self.llcx).as_ptr(),
                val.as_ptr() as *const c_char,
                val.len(),
                0,
            )
        };
        let sym = self.generate_local_symbol_name("str");
        let ty = self.val_ty(unsafe { &*val });
        let global = self
            .define_global(&sym, ty)
            .unwrap_or_else(|| unreachable!("symbol {} already defined", sym));

        unsafe {
            llvm_sys::core::LLVMSetInitializer(NonNull::from(global).as_ptr(), val);
            llvm_sys::core::LLVMSetGlobalConstant(NonNull::from(global).as_ptr(), 1);
            llvm_sys::core::LLVMSetLinkage(
                NonNull::from(global).as_ptr(),
                llvm_sys::LLVMLinkage::LLVMInternalLinkage,
            );
        }
        self.str_lit_cache.borrow_mut().insert(lit, global);
        global
    }
}

impl CodegenCx<'_, '_> {
    /// Generates a new symbol name with the given prefix. This symbol name must
    /// only be used for definitions with `internal` or `private` linkage.
    pub fn generate_local_symbol_name(&self, prefix: &str) -> String {
        let idx = self.local_gen_sym_counter.get();
        self.local_gen_sym_counter.set(idx + 1);
        // Include a '.' character, so there can be no accidental conflicts with
        // user defined names
        let mut name = String::with_capacity(prefix.len() + 6);
        name.push_str(prefix);
        name.push('.');
        base_n::push_str(idx as u128, base_n::ALPHANUMERIC_ONLY, &mut name);
        name
    }
}
