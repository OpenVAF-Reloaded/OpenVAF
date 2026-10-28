// Re-export the correct llvm-sys version based on feature flags
#[cfg(feature = "llvm18")]
extern crate llvm_sys_181 as llvm_sys;
#[cfg(feature = "llvm19")]
extern crate llvm_sys_191 as llvm_sys;
#[cfg(feature = "llvm20")]
extern crate llvm_sys_201 as llvm_sys;
#[cfg(feature = "llvm21")]
extern crate llvm_sys_211 as llvm_sys;
#[cfg(feature = "llvm22")]
extern crate llvm_sys_221 as llvm_sys;

use std::error::Error;
use std::ffi::{CStr, CString};
use std::fmt::{self, Debug, Display, Formatter};
use std::mem::MaybeUninit;
use std::ops::Deref;
use std::os::raw::{c_char, c_uint, c_ulonglong};
use std::path::Path;
use std::ptr;
use std::ptr::NonNull;

use lasso::Rodeo;
use libc::c_void;
use llvm_sys::core;
use llvm_sys::core::{LLVMCreateMessage, LLVMDisposeMessage};
use llvm_sys::error::LLVMGetErrorMessage;
use llvm_sys::transforms::pass_builder::*;

pub const UNNAMED: *const c_char = b"\0".as_ptr() as *const c_char;
#[derive(Eq)]
#[repr(transparent)]
pub struct LLVMString {
    ptr: *const c_char,
}

impl LLVMString {
    pub unsafe fn new(ptr: *const c_char) -> Self {
        LLVMString { ptr }
    }

    pub(crate) fn create_from_str(string: &str) -> LLVMString {
        let msg = CString::new(string).unwrap();
        unsafe { LLVMString::new(LLVMCreateMessage(msg.as_ptr())) }
    }

    pub fn create_from_c_str(string: &CStr) -> LLVMString {
        unsafe { LLVMString::new(LLVMCreateMessage(string.as_ptr())) }
    }
}

impl Deref for LLVMString {
    type Target = CStr;

    fn deref(&self) -> &Self::Target {
        unsafe { CStr::from_ptr(self.ptr) }
    }
}

impl Debug for LLVMString {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self.deref())
    }
}

impl Display for LLVMString {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.deref().to_string_lossy())
    }
}

impl PartialEq for LLVMString {
    fn eq(&self, other: &LLVMString) -> bool {
        **self == **other
    }
}

impl Error for LLVMString {
    fn description(&self) -> &str {
        self.to_str().expect("Could not convert LLVMString to str (likely invalid unicode)")
    }

    fn cause(&self) -> Option<&dyn Error> {
        None
    }
}

impl Drop for LLVMString {
    fn drop(&mut self) {
        unsafe {
            LLVMDisposeMessage(self.ptr as *mut _);
        }
    }
}

use llvm_sys::core::{LLVMGetDiagInfoDescription, LLVMGetDiagInfoSeverity};
pub use llvm_sys::target_machine::LLVMCodeGenOptLevel;
use llvm_sys::target_machine::{LLVMGetHostCPUFeatures, LLVMGetHostCPUName};
use target::spec::Target;

mod builder;
mod context;
mod declarations;
mod intrinsics;
mod types;

mod callbacks;
#[cfg(test)]
mod tests;

pub use builder::{Builder, BuilderVal, MemLoc};
pub use callbacks::{BuiltCallbackFun, CallbackFun, InlineCallbackBuilder};
pub use context::CodegenCx;

pub struct LLVMBackend<'t> {
    target: &'t Target,
    target_cpu: String,
    features: String,
}

impl<'t> LLVMBackend<'t> {
    pub fn new(
        _cg_opts: &[String],
        target: &'t Target,
        mut target_cpu: String,
        target_features: &[String],
    ) -> LLVMBackend<'t> {
        if target_cpu == "generic" {
            target_cpu = target.options.cpu.clone();
        }

        let mut features = vec![];
        if target_cpu == "native" {
            let features_string = unsafe {
                let ptr = LLVMGetHostCPUFeatures();
                let features_string = if !ptr.is_null() {
                    CStr::from_ptr(ptr)
                        .to_str()
                        .unwrap_or_else(|e| {
                            unreachable!("LLVM returned a non-utf8 features string: {}", e);
                        })
                        .to_owned()
                } else {
                    unreachable!(
                        "could not allocate host CPU features, LLVM returned a `null` string"
                    );
                };

                LLVMDisposeMessage(ptr as *mut c_char);

                features_string
            };
            features.extend(features_string.split(',').map(String::from));

            target_cpu = unsafe {
                let ptr = LLVMGetHostCPUName();
                let cpu = if !ptr.is_null() {
                    CStr::from_ptr(ptr)
                        .to_str()
                        .unwrap_or_else(|e| {
                            unreachable!("LLVM returned a non-utf8 features string: {}", e);
                        })
                        .to_owned()
                } else {
                    unreachable!(
                        "could not allocate host CPU features, LLVM returned a `null` string"
                    );
                };

                LLVMDisposeMessage(ptr as *mut c_char);

                cpu
            };
        }

        features
            .extend(target.options.features.split(',').filter(|v| !v.is_empty()).map(String::from));
        features.extend(target_features.iter().cloned());

        // TODO add target options here if we ever have any
        // https://reviews.llvm.org/D145043
        //llvm_sys::initialization::init(cg_opts, &[]);
        //https://github.com/llvm/llvm-project/commit/62ef97e0631ff41ad53436477cecc7d3eb244d1b
        LLVMBackend { target, target_cpu, features: features.join(",") }
    }

    /// # Safety
    ///
    /// This function calls the LLVM-C Api which may not be entirely safe.
    /// Exercise caution!
    pub unsafe fn new_module(
        &self,
        name: &str,
        opt_lvl: LLVMCodeGenOptLevel,
    ) -> Result<ModuleLlvm, LLVMString> {
        ModuleLlvm::new(name, self.target, &self.target_cpu, &self.features, opt_lvl)
    }

    /// # Safety
    ///
    /// This function calls the LLVM-C Api which may not be entirely safe.
    /// Exercise caution!
    pub unsafe fn new_ctx<'a, 'll>(
        &'a self,
        literals: &'a Rodeo,
        module: &'ll ModuleLlvm,
    ) -> CodegenCx<'a, 'll> {
        CodegenCx::new(literals, module, self.target)
    }

    pub fn target(&self) -> &'t Target {
        self.target
    }
}

impl Drop for LLVMBackend<'_> {
    fn drop(&mut self) {}
}

extern "C" fn diagnostic_handler(info: *mut llvm_sys::LLVMDiagnosticInfo, _: *mut c_void) {
    unsafe {
        let severity = LLVMGetDiagInfoSeverity(info);
        let msg = LLVMString::new(LLVMGetDiagInfoDescription(info));
        match severity {
            llvm_sys::LLVMDiagnosticSeverity::LLVMDSError => log::error!("{msg}"),
            llvm_sys::LLVMDiagnosticSeverity::LLVMDSWarning => log::warn!("{msg}"),
            llvm_sys::LLVMDiagnosticSeverity::LLVMDSRemark => log::debug!("{msg}"),
            llvm_sys::LLVMDiagnosticSeverity::LLVMDSNote => log::trace!("{msg}"),
        }
    }
}

// Helper function to convert Rust string to C string
fn to_c_string(s: &str) -> CString {
    CString::new(s).unwrap()
}

// Helper function to convert C string to Rust string
unsafe fn from_c_string(s: *const c_char) -> String {
    CStr::from_ptr(s).to_string_lossy().into_owned()
}

/// # Safety
///
/// This function calls the LLVM C interface and may emit unsafety for invalid inputs.
/// Specifically this function is not thread save!
pub unsafe fn create_target(
    triple: &str,
    cpu: &str,
    features: &str,
    level: llvm_sys::target_machine::LLVMCodeGenOptLevel,
    reloc_mode: llvm_sys::target_machine::LLVMRelocMode,
    code_model: llvm_sys::target_machine::LLVMCodeModel,
) -> Result<llvm_sys::target_machine::LLVMTargetMachineRef, LLVMString> {
    let triple_ = LLVMString::create_from_c_str(&CString::new(triple).unwrap());
    let triple_ =
        LLVMString::new(llvm_sys::target_machine::LLVMNormalizeTargetTriple(triple_.as_ptr()));
    let mut target: llvm_sys::target_machine::LLVMTargetRef = std::ptr::null_mut();
    let mut err_string = MaybeUninit::uninit();

    let code = llvm_sys::target_machine::LLVMGetTargetFromTriple(
        triple_.as_ptr(),
        &mut target,
        err_string.as_mut_ptr(),
    );

    if code == 1 {
        return Err(LLVMString::new(err_string.assume_init()));
    }

    let cpu = LLVMString::create_from_str(cpu);
    let features = CString::new(features).unwrap();

    let target_machine = llvm_sys::target_machine::LLVMCreateTargetMachine(
        target,
        triple_.as_ptr(),
        cpu.as_ptr(),
        features.as_ptr(),
        level,
        reloc_mode,
        code_model,
    );

    if target_machine.is_null() {
        return Err(LLVMString::create_from_c_str(
            CStr::from_bytes_with_nul(
                format!("error: code gen not available for target \"{}\"\0", triple).as_bytes(),
            )
            .unwrap(),
        ));
    }

    Ok(target_machine)
}

pub unsafe fn set_normalized_target(module: llvm_sys::prelude::LLVMModuleRef, triple: &str) {
    let triple_c = to_c_string(triple);
    let normalized_triple = llvm_sys::target_machine::LLVMNormalizeTargetTriple(triple_c.as_ptr());
    llvm_sys::core::LLVMSetTarget(module, normalized_triple);
    llvm_sys::core::LLVMDisposeMessage(normalized_triple);
}

pub unsafe fn get_host_cpu_name() -> String {
    from_c_string(llvm_sys::target_machine::LLVMGetHostCPUName())
}

pub unsafe fn get_host_cpu_features() -> String {
    from_c_string(llvm_sys::target_machine::LLVMGetHostCPUFeatures())
}

pub unsafe fn offset_of_element(
    td: llvm_sys::target::LLVMTargetDataRef,
    struct_ty: llvm_sys::prelude::LLVMTypeRef,
    elem: c_uint,
) -> c_ulonglong {
    llvm_sys::target::LLVMOffsetOfElement(td, struct_ty, elem)
}

pub unsafe fn create_target_data(string_rep: &str) -> llvm_sys::target::LLVMTargetDataRef {
    let string_rep_c = to_c_string(string_rep);
    llvm_sys::target::LLVMCreateTargetData(string_rep_c.as_ptr())
}

pub unsafe fn dispose_target_data(target_data: llvm_sys::target::LLVMTargetDataRef) {
    llvm_sys::target::LLVMDisposeTargetData(target_data);
}

pub unsafe fn abi_size_of_type(
    data: llvm_sys::target::LLVMTargetDataRef,
    ty: llvm_sys::prelude::LLVMTypeRef,
) -> c_ulonglong {
    llvm_sys::target::LLVMABISizeOfType(data, ty)
}

pub unsafe fn abi_alignment_of_type(
    data: llvm_sys::target::LLVMTargetDataRef,
    ty: llvm_sys::prelude::LLVMTypeRef,
) -> c_uint {
    llvm_sys::target::LLVMABIAlignmentOfType(data, ty)
}

pub unsafe fn target_machine_emit_to_file(
    target: llvm_sys::target_machine::LLVMTargetMachineRef,
    module: llvm_sys::prelude::LLVMModuleRef,
    filename: &str,
    codegen: llvm_sys::target_machine::LLVMCodeGenFileType,
) -> Result<(), String> {
    let filename_c = to_c_string(filename);
    let mut error_msg: *mut c_char = ptr::null_mut();

    if llvm_sys::target_machine::LLVMTargetMachineEmitToFile(
        target,
        module,
        filename_c.as_ptr(),
        codegen,
        &mut error_msg,
    ) != 0
    {
        let error = from_c_string(error_msg);
        llvm_sys::core::LLVMDisposeMessage(error_msg);
        Err(error)
    } else {
        Ok(())
    }
}

pub struct ModuleLlvm {
    llcx: llvm_sys::prelude::LLVMContextRef,
    llmod_raw: llvm_sys::prelude::LLVMModuleRef,
    tm: llvm_sys::target_machine::LLVMTargetMachineRef,
    opt_lvl: llvm_sys::target_machine::LLVMCodeGenOptLevel,
}

impl ModuleLlvm {
    pub unsafe fn new(
        name: &str,
        target: &Target,
        target_cpu: &str,
        features: &str,
        opt_lvl: llvm_sys::target_machine::LLVMCodeGenOptLevel,
    ) -> Result<ModuleLlvm, LLVMString> {
        let llcx = llvm_sys::core::LLVMContextCreate();
        let target_data_layout = target.data_layout.clone();

        llvm_sys::core::LLVMContextSetDiagnosticHandler(
            llcx,
            Some(diagnostic_handler),
            ptr::null_mut(),
        );

        let name = CString::new(name).unwrap();
        let llmod = llvm_sys::core::LLVMModuleCreateWithNameInContext(name.as_ptr(), llcx);

        let data_layout = CString::new(&*target_data_layout).unwrap();
        llvm_sys::core::LLVMSetDataLayout(llmod, data_layout.as_ptr());

        set_normalized_target(llmod, &target.llvm_target);

        let tm = create_target(
            &target.llvm_target,
            target_cpu,
            features,
            opt_lvl,
            llvm_sys::target_machine::LLVMRelocMode::LLVMRelocPIC,
            llvm_sys::target_machine::LLVMCodeModel::LLVMCodeModelDefault,
        )?;

        Ok(ModuleLlvm { llcx, llmod_raw: llmod, tm, opt_lvl })
    }

    pub fn to_str(&self) -> LLVMString {
        unsafe {
            LLVMString::new(llvm_sys::core::LLVMPrintModuleToString(
                NonNull::from(self.llmod()).as_ptr(),
            ))
        }
    }

    pub fn llmod(&self) -> &llvm_sys::LLVMModule {
        unsafe { &*self.llmod_raw }
    }
    pub fn optimize(&self) {
        let llmod = self.llmod();

        unsafe {
            // Create PassBuilderOptions
            let options = LLVMCreatePassBuilderOptions(); //this is opaque LLVMPassBuilderOptionsRef

            // Set optimization level
            let opt_level = match self.opt_lvl {
                llvm_sys::target_machine::LLVMCodeGenOptLevel::LLVMCodeGenLevelNone => {
                    "default<O0>"
                }
                llvm_sys::target_machine::LLVMCodeGenOptLevel::LLVMCodeGenLevelLess => {
                    "default<O1>"
                }
                llvm_sys::target_machine::LLVMCodeGenOptLevel::LLVMCodeGenLevelDefault => {
                    "default<O2>"
                }
                llvm_sys::target_machine::LLVMCodeGenOptLevel::LLVMCodeGenLevelAggressive => {
                    "default<O3>"
                }
            };

            let error = {
                // Create variables in inner scope
                let opt_level_cstring = CString::new(opt_level).unwrap();
                let opt_level_ptr = opt_level_cstring.as_ptr();

                let llmod_ptr = NonNull::from(llmod).as_ptr();

                // Run passes while values are guaranteed to be alive
                LLVMRunPasses(llmod_ptr, opt_level_ptr, self.tm, options)
            };
            // Check for errors
            if !error.is_null() {
                // Handle error
                let error_string = LLVMGetErrorMessage(error);
                let rust_str =
                    std::ffi::CStr::from_ptr(error_string).to_string_lossy().into_owned();
                eprintln!("Error occurred during optimization: {}", rust_str);
                core::LLVMDisposeMessage(error_string);
            }

            // Clean up
            LLVMDisposePassBuilderOptions(options);
        }
    }

    /// Verifies this module and prints out  any errors
    ///
    /// # Returns
    /// Whether this module is valid (true if valid)
    pub fn verify_and_print(&self) -> bool {
        unsafe {
            llvm_sys::analysis::LLVMVerifyModule(
                self.llmod_raw, // Use the raw pointer directly
                llvm_sys::analysis::LLVMVerifierFailureAction::LLVMPrintMessageAction,
                std::ptr::null_mut(), // Use null pointer instead of None
            ) == 0
        }
    }

    /// Verifies this module and prints out an error for any errors
    ///
    /// # Returns
    /// An error messages in case the module invalid
    pub fn verify(&self) -> Option<LLVMString> {
        unsafe {
            let mut out_message: *mut c_char = std::ptr::null_mut();
            if llvm_sys::analysis::LLVMVerifyModule(
                self.llmod_raw,
                llvm_sys::analysis::LLVMVerifierFailureAction::LLVMReturnStatusAction,
                &mut out_message,
            ) == 1
            {
                if !out_message.is_null() {
                    let message = LLVMString::new(out_message);
                    llvm_sys::core::LLVMDisposeMessage(out_message);
                    Some(message)
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    pub fn emit_object(&self, dst: &Path) -> Result<(), LLVMString> {
        let path = CString::new(dst.to_str().unwrap()).unwrap();

        let mut err_string = MaybeUninit::uninit();
        let return_code = unsafe {
            // REVIEW: Why does LLVM need a mutable ptr to path...?

            llvm_sys::target_machine::LLVMTargetMachineEmitToFile(
                self.tm,
                NonNull::from(self.llmod()).as_ptr(),
                path.as_ptr(),
                llvm_sys::target_machine::LLVMCodeGenFileType::LLVMObjectFile,
                err_string.as_mut_ptr(),
            )
        };

        if return_code == 1 {
            unsafe {
                return Err(LLVMString::new(err_string.assume_init()));
            }
        }

        Ok(())
    }
}

impl Drop for ModuleLlvm {
    fn drop(&mut self) {
        unsafe {
            llvm_sys::target_machine::LLVMDisposeTargetMachine(&mut *(self.tm as *mut _));
            llvm_sys::core::LLVMContextDispose(&mut *(self.llcx as *mut _));
        }
    }
}
