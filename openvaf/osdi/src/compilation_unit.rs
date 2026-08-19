use std::iter;
use std::ptr::NonNull;

use hir::CompilationDB;
use hir_lower::fmt::{DisplayKind, FmtArg, FmtArgKind};
use hir_lower::{CallBackKind, HirInterner, RetFlag};
use lasso::Rodeo;
use llvm_sys::core::{
    LLVMAddIncoming, LLVMAppendBasicBlockInContext, LLVMBuildAdd, LLVMBuildArrayMalloc,
    LLVMBuildBr, LLVMBuildCall2, LLVMBuildCondBr, LLVMBuildFMul, LLVMBuildFree, LLVMBuildICmp,
    LLVMBuildInBoundsGEP2, LLVMBuildLoad2, LLVMBuildPhi, LLVMBuildZExt, LLVMGetFirstFunction,
    LLVMGetNextFunction, LLVMGetParam, LLVMIsDeclaration, LLVMPositionBuilderAtEnd, LLVMSetLinkage,
    LLVMSetUnnamedAddress,
};
use llvm_sys::{LLVMIntPredicate, LLVMLinkage, LLVMUnnamedAddr, LLVMValue};
use mir::{FuncRef, Function};
use mir_llvm::{BuiltCallbackFun, CallbackFun, CodegenCx, LLVMBackend, ModuleLlvm, UNNAMED};
use sim_back::dae::DaeSystem;
use sim_back::init::Initialization;
use sim_back::node_collapse::NodeCollapse;
use sim_back::{CompiledModule, ModuleInfo};
use typed_index_collections::TiVec;
use typed_indexmap::TiSet;

use crate::inst_data::OsdiInstanceData;
use crate::metadata::osdi_0_5::{
    stdlib_bitcode, OsdiTys, LOG_FMT_ERR, LOG_LVL_DEBUG, LOG_LVL_DISPLAY, LOG_LVL_ERR,
    LOG_LVL_FATAL, LOG_LVL_INFO, LOG_LVL_WARN,
};
use crate::metadata::OsdiLimFunction;
use crate::model_data::OsdiModelData;
use crate::{lltype, OsdiLimId};

fn function_iter(
    module: &llvm_sys::LLVMModule,
) -> impl Iterator<Item = *mut llvm_sys::LLVMValue> + '_ {
    let fun = unsafe { LLVMGetFirstFunction(NonNull::from(module).as_ptr()) };
    iter::successors(Some(fun), |&fun| {
        let next_fun = unsafe { LLVMGetNextFunction(fun) };
        if next_fun.is_null() {
            None
        } else {
            Some(next_fun)
        }
    })
}

pub fn new_codegen<'a, 'll>(
    back: &'a LLVMBackend,
    llmod: &'ll ModuleLlvm,
    literals: &'a Rodeo,
) -> CodegenCx<'a, 'll> {
    let cx = unsafe { back.new_ctx(literals, llmod) };
    cx.include_bitcode(stdlib_bitcode(back.target()));

    for fun in function_iter(llmod.llmod()) {
        unsafe {
            // LLVMPurgeAttrs(fun);
            if LLVMIsDeclaration(fun) != 0 as i32 {
                continue;
            }

            LLVMSetLinkage(fun, LLVMLinkage::LLVMInternalLinkage);
            LLVMSetUnnamedAddress(fun, LLVMUnnamedAddr::LLVMGlobalUnnamedAddr);
        }
    }

    let exp_table = cx.get_declared_value("EXP").expect("constant EXP missing from stdlib");
    let char_table =
        cx.get_declared_value("FMT_CHARS").expect("constant FMT_CHARS missing from stdlib");

    unsafe {
        LLVMSetLinkage(NonNull::from(exp_table).as_ptr(), LLVMLinkage::LLVMInternalLinkage);
        LLVMSetLinkage(NonNull::from(char_table).as_ptr(), LLVMLinkage::LLVMInternalLinkage);
    }

    cx
}

pub struct OsdiCompilationUnit<'a, 'b, 'll> {
    pub db: &'a CompilationDB,
    pub inst_data: OsdiInstanceData<'ll>,
    pub model_data: OsdiModelData<'ll>,
    pub tys: &'a OsdiTys<'ll>,
    pub cx: &'a CodegenCx<'b, 'll>,
    pub module: &'a OsdiModule<'b>,
    pub lim_dispatch_table: Option<&'ll llvm_sys::LLVMValue>,
}

impl<'a, 'b, 'll> OsdiCompilationUnit<'a, 'b, 'll> {
    pub fn new(
        db: &'a CompilationDB,
        module: &'a OsdiModule<'b>,
        cx: &'a CodegenCx<'b, 'll>,
        tys: &'a OsdiTys<'ll>,
        eval: bool,
    ) -> OsdiCompilationUnit<'a, 'b, 'll> {
        let inst_data = OsdiInstanceData::new(db, module, cx);
        let model_data = OsdiModelData::new(db, module, cx, &inst_data);
        let lim_dispatch_table =
            if eval && !module.lim_table.is_empty() && !module.intern.lim_state.is_empty() {
                let ty = cx.ty_array(tys.osdi_lim_function, module.lim_table.len() as u32);
                let ptr = cx
                    .define_global("OSDI_LIM_TABLE", ty)
                    .unwrap_or_else(|| unreachable!("symbol OSDI_LIM_TABLE already defined"));
                unsafe {
                    llvm_sys::core::LLVMSetLinkage(
                        NonNull::from(ptr).as_ptr(),
                        llvm_sys::LLVMLinkage::LLVMExternalLinkage,
                    );
                    llvm_sys::core::LLVMSetUnnamedAddress(
                        NonNull::from(ptr).as_ptr(),
                        llvm_sys::LLVMUnnamedAddr::LLVMNoUnnamedAddr,
                    );
                    llvm_sys::core::LLVMSetDLLStorageClass(
                        NonNull::from(ptr).as_ptr(),
                        llvm_sys::LLVMDLLStorageClass::LLVMDLLExportStorageClass,
                    );
                }
                Some(ptr)
            } else {
                None
            };
        OsdiCompilationUnit { db, inst_data, model_data, tys, cx, module, lim_dispatch_table }
    }

    pub fn lim_dispatch_table(&self) -> &'ll llvm_sys::LLVMValue {
        self.lim_dispatch_table.unwrap()
    }
}

pub struct OsdiModule<'a> {
    pub info: &'a ModuleInfo,
    pub dae_system: &'a DaeSystem,
    pub eval: &'a Function,
    pub intern: &'a HirInterner,
    pub init: &'a Initialization,
    pub model_param_setup: &'a Function,
    pub model_param_intern: &'a HirInterner,
    pub lim_table: &'a TiSet<OsdiLimId, OsdiLimFunction>,
    pub node_collapse: &'a NodeCollapse,
    pub sym: String,
}

impl<'a> OsdiModule<'a> {
    pub fn new(
        db: &'a CompilationDB,
        module: &'a CompiledModule,
        lim_table: &'a TiSet<OsdiLimId, OsdiLimFunction>,
    ) -> Self {
        let sym = base_n::encode(module.info.module.uuid(db) as u128, base_n::CASE_INSENSITIVE);
        let CompiledModule {
            info,
            dae_system,
            eval,
            intern,
            init,
            model_param_setup,
            model_param_intern,
            node_collapse,
        } = module;
        OsdiModule {
            sym,
            lim_table,
            info,
            dae_system,
            eval,
            intern,
            init,
            model_param_setup,
            model_param_intern,
            node_collapse,
        }
    }
}

pub fn general_callbacks<'ll>(
    intern: &HirInterner,
    builder: &mut mir_llvm::Builder<'_, '_, 'll>,
    ret_flags: &'ll llvm_sys::LLVMValue,
    handle: &'ll llvm_sys::LLVMValue,
    simparam: &'ll llvm_sys::LLVMValue,
) -> TiVec<FuncRef, Option<CallbackFun<'ll>>> {
    let ptr_ty = builder.cx.ty_ptr();
    intern
        .callbacks
        .raw
        .iter()
        .map(|call| {
            let cb = match call {
                CallBackKind::SimParam => {
                    let fun = builder
                        .cx
                        .get_func_by_name("simparam")
                        .expect("stdlib function simparam is missing");
                    let fun_ty = builder.cx.ty_func(
                        &[ptr_ty, ptr_ty, ptr_ty, builder.cx.ty_ptr()],
                        builder.cx.ty_double(),
                    );
                    CallbackFun::Prebuilt(BuiltCallbackFun {
                        fun_ty,
                        fun,
                        state: vec![simparam, handle, ret_flags].into_boxed_slice(),
                        num_state: 0,
                    })
                }
                CallBackKind::SimParamOpt => {
                    let fun = builder
                        .cx
                        .get_func_by_name("simparam_opt")
                        .expect("stdlib function simparam_opt is missing");
                    let fun_ty = builder.cx.ty_func(
                        &[ptr_ty, builder.cx.ty_ptr(), builder.cx.ty_double()],
                        builder.cx.ty_double(),
                    );
                    CallbackFun::Prebuilt(BuiltCallbackFun {
                        fun_ty,
                        fun,
                        state: vec![simparam].into_boxed_slice(),
                        num_state: 0,
                    })
                }
                CallBackKind::SimParamStr => {
                    let fun = builder
                        .cx
                        .get_func_by_name("simparam_str")
                        .expect("stdlib function simparam_str is missing");
                    let fun_ty = builder.cx.ty_func(
                        &[ptr_ty, ptr_ty, ptr_ty, builder.cx.ty_ptr()],
                        builder.cx.ty_ptr(),
                    );
                    CallbackFun::Prebuilt(BuiltCallbackFun {
                        fun_ty,
                        fun,
                        state: vec![simparam, handle, ret_flags].into_boxed_slice(),
                        num_state: 0,
                    })
                }
                // If these derivative were non zero they would have been removed
                CallBackKind::Derivative(_) | CallBackKind::NodeDerivative(_) => {
                    let zero = builder.cx.const_real(0.0);
                    CallbackFun::Prebuilt(
                        builder.cx.const_callback(&[builder.cx.ty_double()], zero),
                    )
                }
                CallBackKind::ParamInfo(_, _)
                | CallBackKind::CollapseHint(_, _)
                | CallBackKind::BuiltinLimit { .. }
                | CallBackKind::StoreLimit(_)
                | CallBackKind::LimDiscontinuity
                | CallBackKind::Analysis
                | CallBackKind::NoiseTable(_)
                | CallBackKind::WhiteNoise { .. }
                | CallBackKind::FlickerNoise { .. }
                | CallBackKind::TimeDerivative => return None,

                CallBackKind::Print { kind, arg_tys } => {
                    let (fun, fun_ty) = print_callback(builder.cx, *kind, arg_tys);
                    CallbackFun::Prebuilt(BuiltCallbackFun {
                        fun_ty,
                        fun,
                        state: Box::new([handle]),
                        num_state: 0,
                    })
                }
                CallBackKind::SetRetFlag(flag) => {
                    let fun = if *flag == RetFlag::Abort {
                        // Fatal
                        builder
                            .cx
                            .get_func_by_name("set_ret_flag_fatal")
                            .expect("stdlib function set_ret_flag_fatal is missing")
                    } else if *flag == RetFlag::Finish {
                        // Finish
                        builder
                            .cx
                            .get_func_by_name("set_ret_flag_finish")
                            .expect("stdlib function set_ret_flag_finish is missing")
                    } else if *flag == RetFlag::Stop {
                        // Stop
                        builder
                            .cx
                            .get_func_by_name("set_ret_flag_stop")
                            .expect("stdlib function set_ret_flag_stop is missing")
                    } else {
                        panic!("Unsupported RetFlag encountered.");
                    };
                    let fun_ty = builder.cx.ty_func(&[ptr_ty], builder.cx.ty_void());
                    CallbackFun::Prebuilt(BuiltCallbackFun {
                        fun_ty,
                        fun,
                        state: Box::new([ret_flags]),
                        num_state: 0,
                    })
                }
            };
            Some(cb)
        })
        .collect()
}
/* This was very useful for debugging
fn print_module_ir(cx: &CodegenCx, message: &str) {
    unsafe {
        let ir_ptr = llvm_sys::core::LLVMPrintModuleToString(NonNull::from(cx.llmod).as_ptr());
        if !ir_ptr.is_null() {
            let ir = std::ffi::CStr::from_ptr(ir_ptr).to_string_lossy().into_owned();
            let lines: Vec<&str> = ir.lines().collect();
            let mut found = false;
            let mut count = 0;
            let mut output_lines = Vec::new();

            for line in lines {
                if found {
                    output_lines.push(line);
                    count += 1;
                    if count >= 35 {
                        break;
                    }
                } else if line.contains("internal fastcc void @cb.2(ptr %0, ptr %1) unnamed_addr") {
                    found = true;
                    output_lines.push(line);
                    count += 1;
                }
            }

            let output_str = output_lines.join("\n");
            println!("{}:\n{}", message, output_str);
            llvm_sys::core::LLVMDisposeMessage(ir_ptr);
        }
    }
}*/

fn print_callback<'ll>(
    cx: &CodegenCx<'_, 'll>,
    kind: hir_lower::fmt::DisplayKind,
    arg_tys: &[FmtArg],
) -> (&'ll llvm_sys::LLVMValue, &'ll llvm_sys::LLVMType) {
    let mut args = vec![cx.ty_ptr(), cx.ty_ptr()];
    args.extend(arg_tys.iter().map(|arg| lltype(&arg.ty, cx)));
    let fun_ty = cx.ty_func(&args, cx.ty_void());
    let name = cx.local_callback_name();
    let fun = cx.declare_int_fn(&name, fun_ty);

    // Print IR before starting the function
    //print_module_ir(cx, "Before starting the function");

    unsafe {
        let entry_bb = LLVMAppendBasicBlockInContext(
            NonNull::from(cx.llcx).as_ptr(),
            NonNull::from(fun).as_ptr(),
            UNNAMED,
        );
        let alloc_bb = LLVMAppendBasicBlockInContext(
            NonNull::from(cx.llcx).as_ptr(),
            NonNull::from(fun).as_ptr(),
            UNNAMED,
        );
        let write_bb = LLVMAppendBasicBlockInContext(
            NonNull::from(cx.llcx).as_ptr(),
            NonNull::from(fun).as_ptr(),
            UNNAMED,
        );
        let err_bb = LLVMAppendBasicBlockInContext(
            NonNull::from(cx.llcx).as_ptr(),
            NonNull::from(fun).as_ptr(),
            UNNAMED,
        );
        let exit_bb = LLVMAppendBasicBlockInContext(
            NonNull::from(cx.llcx).as_ptr(),
            NonNull::from(fun).as_ptr(),
            UNNAMED,
        );
        let llbuilder = llvm_sys::core::LLVMCreateBuilderInContext(NonNull::from(cx.llcx).as_ptr());

        LLVMPositionBuilderAtEnd(llbuilder, entry_bb);
        let handle = LLVMGetParam(NonNull::from(fun).as_ptr(), 0);
        let fmt_lit = LLVMGetParam(NonNull::from(fun).as_ptr(), 1);
        let mut args = vec![
            cx.const_null_ptr(),
            cx.const_usize(0),
            &*LLVMGetParam(NonNull::from(fun).as_ptr(), 1),
        ];

        let exp_table = cx.get_declared_value("EXP").expect("constant EXP missing from stdlib");
        let exp_table_ty = cx.ty_array(cx.ty_double(), 11);
        let char_table =
            cx.get_declared_value("FMT_CHARS").expect("constant FMT_CHARS missing from stdlib");
        let char_table_ty = cx.ty_array(cx.ty_char(), 11);
        let fmt_char_idx =
            cx.get_func_by_name("fmt_char_idx").expect("fmt_char_idx missing from stdlib");
        let fmt_char_idx_ty = cx.ty_func(&[cx.ty_double()], cx.ty_int());
        let fmt_binary = cx.get_func_by_name("fmt_binary").expect("fmt_binary missing from stdlib");
        let fmt_binary_ty = cx.ty_func(&[cx.ty_int()], cx.ty_ptr());
        let mut free = Vec::new();

        for (i, arg) in arg_tys.iter().enumerate() {
            let val = LLVMGetParam(NonNull::from(fun).as_ptr(), i as u32 + 2);
            match arg.kind {
                FmtArgKind::Binary => {
                    let mut val_array = [val];
                    let formatted_str = LLVMBuildCall2(
                        llbuilder,
                        NonNull::from(fmt_binary_ty).as_ptr(),
                        NonNull::from(fmt_binary).as_ptr(),
                        val_array.as_mut_ptr(),
                        1,
                        UNNAMED,
                    );
                    free.push(formatted_str);
                }
                FmtArgKind::EngineerReal => {
                    let mut val_array = [val];
                    let idx = LLVMBuildCall2(
                        llbuilder,
                        NonNull::from(fmt_char_idx_ty).as_ptr(),
                        NonNull::from(fmt_char_idx).as_ptr(),
                        val_array.as_mut_ptr(),
                        1,
                        UNNAMED,
                    );
                    let mut idx_array = vec![cx.const_int(0), &*idx];
                    let exp = LLVMBuildInBoundsGEP2(
                        llbuilder,
                        NonNull::from(exp_table_ty).as_ptr(),
                        NonNull::from(exp_table).as_ptr(),
                        idx_array.as_mut_ptr() as *mut *mut _,
                        2,
                        UNNAMED,
                    );
                    let exp = LLVMBuildLoad2(
                        llbuilder,
                        NonNull::from(cx.ty_double()).as_ptr(),
                        exp,
                        UNNAMED,
                    );
                    let num = LLVMBuildFMul(llbuilder, val, exp, UNNAMED);
                    args.push(&*num);
                    let mut idx_array = vec![cx.const_int(0), &*idx];
                    let scale_char = LLVMBuildInBoundsGEP2(
                        llbuilder,
                        NonNull::from(char_table_ty).as_ptr(),
                        NonNull::from(char_table).as_ptr(),
                        idx_array.as_mut_ptr() as *mut *mut _,
                        2,
                        UNNAMED,
                    );
                    args.push(&*scale_char);
                }
                FmtArgKind::Other => args.push(&*val),
            }
        }
        let (fun_ty, fun) = cx.intrinsic("snprintf").unwrap();
        // Convert Vec<&LLVMValue> to Vec<*mut LLVMValue>
        let mut raw_args: Vec<*mut LLVMValue> =
            args.iter().map(|&arg| NonNull::from(arg).as_ptr()).collect();

        let len = LLVMBuildCall2(
            llbuilder,
            NonNull::from(fun_ty).as_ptr(),
            NonNull::from(fun).as_ptr(),
            raw_args.as_mut_ptr(),
            raw_args.len() as u32,
            UNNAMED,
        );

        let is_err = LLVMBuildICmp(
            llbuilder,
            LLVMIntPredicate::LLVMIntSLT,
            len,
            NonNull::from(cx.const_int(0)).as_ptr(),
            UNNAMED,
        );
        LLVMBuildCondBr(llbuilder, is_err, err_bb, alloc_bb);

        // Print IR after building the conditional branch
        //print_module_ir(cx, "After building the conditional branch");

        LLVMPositionBuilderAtEnd(llbuilder, alloc_bb);
        let data_len =
            LLVMBuildAdd(llbuilder, len, NonNull::from(cx.const_int(1)).as_ptr(), UNNAMED);
        let ptr = LLVMBuildArrayMalloc(
            llbuilder,
            NonNull::from(cx.ty_char()).as_ptr(),
            data_len,
            UNNAMED,
        );
        let null_ptr = cx.const_null_ptr();
        let is_err = LLVMBuildICmp(
            llbuilder,
            llvm_sys::LLVMIntPredicate::LLVMIntEQ,
            NonNull::from(null_ptr).as_ptr(),
            ptr,
            UNNAMED,
        );
        LLVMBuildCondBr(llbuilder, is_err, err_bb, write_bb);

        // Print IR after building the malloc and conditional branch
        //print_module_ir(cx, "After building the malloc and conditional branch");

        LLVMPositionBuilderAtEnd(llbuilder, write_bb);
        let data_len =
            LLVMBuildAdd(llbuilder, len, NonNull::from(cx.const_int(1)).as_ptr(), UNNAMED);
        // LLVM value data_len is i32, we need size_t because snprintf needs it. Zero extend to get size_t
        let data_len =
            LLVMBuildZExt(llbuilder, data_len, NonNull::from(cx.ty_size()).as_ptr(), UNNAMED);
        raw_args[0] = ptr;
        raw_args[1] = data_len;
        let len = LLVMBuildCall2(
            llbuilder,
            NonNull::from(fun_ty).as_ptr(),
            NonNull::from(fun).as_ptr(),
            raw_args.as_mut_ptr(),
            raw_args.len() as u32,
            UNNAMED,
        );
        let is_err = LLVMBuildICmp(
            llbuilder,
            LLVMIntPredicate::LLVMIntSLT,
            len,
            NonNull::from(cx.const_int(0)).as_ptr(),
            UNNAMED,
        );
        for alloc in free.iter() {
            LLVMBuildFree(llbuilder, *alloc);
        }
        LLVMBuildCondBr(llbuilder, is_err, err_bb, exit_bb);

        // Print IR after building the write block
        //print_module_ir(cx, "After building the write block");

        LLVMPositionBuilderAtEnd(llbuilder, err_bb);
        LLVMBuildBr(llbuilder, exit_bb);

        // Print IR after building the error block
        //print_module_ir(cx, "After building the error block");

        LLVMPositionBuilderAtEnd(llbuilder, exit_bb);
        let flags = LLVMBuildPhi(llbuilder, NonNull::from(cx.ty_int()).as_ptr(), UNNAMED);
        let lvl = match kind {
            DisplayKind::Debug => LOG_LVL_DEBUG,
            DisplayKind::Display | DisplayKind::Monitor => LOG_LVL_DISPLAY,
            DisplayKind::Info => LOG_LVL_INFO,
            DisplayKind::Warn => LOG_LVL_WARN,
            DisplayKind::Error => LOG_LVL_ERR,
            DisplayKind::Fatal => LOG_LVL_FATAL,
        };
        let lvl_and_err = lvl | LOG_FMT_ERR;
        let lvl = cx.const_unsigned_int(lvl);
        let lvl_and_err = cx.const_unsigned_int(lvl_and_err);

        let lvl_val = lvl as *const llvm_sys::LLVMValue as *mut _;
        let lvl_and_err_val = lvl_and_err as *const llvm_sys::LLVMValue as *mut _;
        let mut incoming_values: [*mut llvm_sys::LLVMValue; 2] = [lvl_val, lvl_and_err_val];
        let incoming_values_ptr = &mut incoming_values as *mut [*mut llvm_sys::LLVMValue]
            as *mut *mut llvm_sys::LLVMValue;

        let mut incoming_blocks = [write_bb, err_bb];
        LLVMAddIncoming(flags, incoming_values_ptr, incoming_blocks.as_mut_ptr(), 2);

        let msg = LLVMBuildPhi(llbuilder, NonNull::from(cx.ty_ptr()).as_ptr(), UNNAMED);
        //  print_module_ir(cx, "After building the PHI block");

        // Fix for second LLVMAddIncoming call
        let mut incoming_values = [ptr, fmt_lit];
        let mut incoming_blocks = [write_bb, err_bb];
        LLVMAddIncoming(msg, incoming_values.as_mut_ptr(), incoming_blocks.as_mut_ptr(), 2);

        let fun_ptr = cx.get_declared_value("osdi_log").expect("symbol osdi_log is missing");
        let fun_ty = cx.ty_func(&[cx.ty_ptr(), cx.ty_ptr(), cx.ty_int()], cx.ty_void());
        let fun = LLVMBuildLoad2(
            llbuilder,
            NonNull::from(cx.ty_ptr()).as_ptr(),
            NonNull::from(fun_ptr).as_ptr(),
            UNNAMED,
        );

        // Fix for LLVMBuildCall2
        let mut args = [handle, msg, flags];
        LLVMBuildCall2(
            llbuilder,
            NonNull::from(fun_ty).as_ptr(),
            fun,
            args.as_mut_ptr(),
            3,
            UNNAMED,
        );
        llvm_sys::core::LLVMBuildRetVoid(llbuilder);
        llvm_sys::core::LLVMDisposeBuilder(llbuilder);
    }

    // Print IR at the end of the function
    //print_module_ir(cx, "Final IR after building the function");

    (fun, fun_ty)
}
