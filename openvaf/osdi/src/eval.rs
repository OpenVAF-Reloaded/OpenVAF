use core::ptr::NonNull;

use hir_lower::{CallBackKind, CurrentKind, LimitState, ParamKind};
use llvm_sys::core::{
    LLVMAppendBasicBlockInContext, LLVMBuildAlloca, LLVMBuildAnd, LLVMBuildBr, LLVMBuildCall2,
    LLVMBuildCondBr, LLVMBuildICmp, LLVMBuildInBoundsGEP2, LLVMBuildIntCast2, LLVMBuildLoad2,
    LLVMBuildOr, LLVMBuildRet, LLVMBuildStore, LLVMCreateBuilderInContext, LLVMDisposeBuilder,
    LLVMGetParam, LLVMPositionBuilderAtEnd,
};
use llvm_sys::LLVMIntPredicate::{LLVMIntNE, LLVMIntULT};
use log::info;
use mir_llvm::{
    Builder, BuilderVal, BuiltCallbackFun, CallbackFun, InlineCallbackBuilder, MemLoc, UNNAMED,
};
use sim_back::SimUnknownKind;
use typed_index_collections::TiVec;

use crate::bitfield::{is_flag_set, is_flag_set_mem, is_flag_unset};
use crate::compilation_unit::{general_callbacks, OsdiCompilationUnit};
use crate::inst_data::OsdiInstanceParam;
use crate::metadata::osdi_0_4::{
    ANALYSIS_IC, CALC_NOISE, CALC_OP, CALC_REACT_JACOBIAN, CALC_REACT_LIM_RHS, CALC_REACT_RESIDUAL,
    CALC_RESIST_JACOBIAN, CALC_RESIST_LIM_RHS, CALC_RESIST_RESIDUAL, ENABLE_LIM, EVAL_RET_FLAG_LIM,
    INIT_LIM,
};
use crate::metadata::OsdiLimFunction;
use crate::OsdiLimId;

/*
// Inline callback example
struct AbortCallback;

impl<'ll> InlineCallbackBuilder<'ll> for AbortCallback {
    fn build_inline(
        &self,
        builder: &mut Builder<'_, '_, 'll>, // The builder is modified, so it should be mutable
        state: &Box<[&'ll llvm_sys::LLVMValue]>,
    ) -> &'ll llvm_sys::LLVMValue {
        let cx = builder.cx;
        unsafe {
            // state[1] is the parent function value, needed to append blocks
            let parent_func = state[1];

            // Create a block to hold the `ret` instruction and a block to continue in.
            let ret_block = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(parent_func).as_ptr(),
                UNNAMED,
            );
            let cont_block = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(parent_func).as_ptr(),
                UNNAMED,
            );

            let llbuilder = builder.llbuilder as *mut _;

            // This is an "Abort" callback, so it unconditionally branches to the return block.
            LLVMBuildBr(llbuilder, ret_block);

            // Add the `ret` instruction to the return block using the high-level helper
            // from the feature branch.
            LLVMPositionBuilderAtEnd(llbuilder, ret_block);
            builder.ret();

            // Position the builder at the start of the continue block for any subsequent
            // instructions. This ensures the builder is in a valid state.
            LLVMPositionBuilderAtEnd(llbuilder, cont_block);
        }

        // The original call instruction doesn't produce a value since it leads to a
        // terminator. We return a dummy value to satisfy the function signature.
        cx.const_int(0)
    }

    fn return_type(
        &self,
        builder: &Builder<'_, '_, 'll>,
        _state: &Box<[&'ll llvm_sys::LLVMValue]>,
    ) -> &'ll llvm_sys::LLVMType {
        builder.cx.ty_int()
    }
}
*/

impl<'ll> OsdiCompilationUnit<'_, '_, 'll> {
    pub fn eval_prototype(&self) -> &'ll llvm_sys::LLVMValue {
        let name = &format!("eval_{}", &self.module.sym);
        let cx = &self.cx;

        let ty_ptr = cx.ty_ptr();

        let fun_ty = cx.ty_func(&[ty_ptr, ty_ptr, ty_ptr, ty_ptr], cx.ty_int());
        cx.declare_ext_fn(name, fun_ty)
    }

    pub fn eval(&self) -> &'ll llvm_sys::LLVMValue {
        let llfunc = self.eval_prototype();
        let OsdiCompilationUnit { inst_data, model_data, cx, module, .. } = self;

        let func = module.eval;
        let intern = module.intern;

        let mut builder = Builder::new(cx, func, llfunc, Some(cx.ty_int()), false);

        let handle = unsafe { &*llvm_sys::core::LLVMGetParam(NonNull::from(llfunc).as_ptr(), 0) };
        let instance = unsafe { &*llvm_sys::core::LLVMGetParam(NonNull::from(llfunc).as_ptr(), 1) };
        let model = unsafe { &*llvm_sys::core::LLVMGetParam(NonNull::from(llfunc).as_ptr(), 2) };
        let sim_info = unsafe { &*llvm_sys::core::LLVMGetParam(NonNull::from(llfunc).as_ptr(), 3) };
        let sim_info_ty = self.tys.osdi_sim_info;

        // let simparam_ty = self.tys.osdi_sim_paras;
        let simparam = unsafe { builder.struct_gep(sim_info_ty, sim_info, 0) };

        const ABSTIME_OFFSET: u32 = 1;

        let prev_result = unsafe {
            let ptr = builder.struct_gep(sim_info_ty, sim_info, 2);
            builder.load(cx.ty_ptr(), ptr)
        };

        let prev_state = unsafe {
            let ptr = builder.struct_gep(sim_info_ty, sim_info, 3);
            builder.load(cx.ty_ptr(), ptr)
        };

        let next_state = unsafe {
            let ptr = builder.struct_gep(sim_info_ty, sim_info, 4);
            builder.load(cx.ty_ptr(), ptr)
        };

        let flags = MemLoc::struct_gep(sim_info, sim_info_ty, cx.ty_int(), 5, cx);

        let ret_flags = builder.ret_allocated.unwrap();
        unsafe { builder.store(ret_flags, cx.const_int(0)) };

        let connected_ports = unsafe { inst_data.load_connected_ports(&mut builder, instance) };
        let prev_solve: TiVec<_, _> = module
            .dae_system
            .unknowns
            .indices()
            .map(|node| unsafe {
                inst_data.read_node_voltage(cx, node, instance, prev_result, builder.llbuilder)
            })
            .collect();

        let get_prev_solve = |node| {
            if let Some(node) = module.dae_system.unknowns.index(&node) {
                prev_solve[node]
            } else {
                info!("node {node:?} is always zero");
                cx.const_real(0.0)
            }
        };

        let state_idx: TiVec<LimitState, _> = (0..intern.lim_state.len())
            .map(|i| unsafe { inst_data.read_state_idx(cx, i.into(), instance, builder.llbuilder) })
            .collect();

        let true_ = cx.const_bool(true);
        let mut params: TiVec<_, _> = intern
            .params
            .raw
            .iter()
            .map(|(kind, val)| {
                if func.dfg.value_dead(*val) && !inst_data.eval_outputs.contains_key(val) {
                    return BuilderVal::Undef;
                }

                let val = unsafe {
                    match *kind {
                        ParamKind::Param(param) => {
                            return inst_data
                                .param_loc(cx, OsdiInstanceParam::User(param), instance)
                                .unwrap_or_else(|| model_data.param_loc(cx, param, model).unwrap())
                                .into()
                        }
                        ParamKind::Voltage { hi, lo } => {
                            let hi = get_prev_solve(SimUnknownKind::KirchoffLaw(hi));
                            if let Some(lo) = lo {
                                let lo = get_prev_solve(SimUnknownKind::KirchoffLaw(lo));
                                &*llvm_sys::core::LLVMBuildFSub(
                                    builder.llbuilder,
                                    NonNull::from(hi).as_ptr(),
                                    NonNull::from(lo).as_ptr(),
                                    UNNAMED,
                                )
                            } else {
                                hi
                            }
                        }
                        ParamKind::Current(CurrentKind::Port(_)) => cx.const_real(0.0),
                        ParamKind::Abstime => {
                            let loc = MemLoc::struct_gep(
                                sim_info,
                                sim_info_ty,
                                cx.ty_double(),
                                ABSTIME_OFFSET,
                                cx,
                            );
                            return loc.into();
                        }

                        ParamKind::Current(kind) => get_prev_solve(SimUnknownKind::Current(kind)),
                        ParamKind::ImplicitUnknown(equation) => {
                            get_prev_solve(SimUnknownKind::Implicit(equation))
                        }
                        ParamKind::Temperature => {
                            return inst_data.temperature_loc(cx, instance).into()
                        }
                        ParamKind::ParamGiven { param } => {
                            let inst_given = inst_data.is_param_given(
                                cx,
                                OsdiInstanceParam::User(param),
                                instance,
                                builder.llbuilder,
                            );
                            match inst_given {
                                Some(inst_given) => {
                                    let model_given = model_data.is_inst_param_given(
                                        inst_data,
                                        cx,
                                        OsdiInstanceParam::User(param),
                                        model,
                                        builder.llbuilder,
                                    );

                                    builder.select(inst_given, true_, model_given)
                                }
                                None => model_data
                                    .is_param_given(cx, param, model, builder.llbuilder)
                                    .unwrap(),
                            }
                        }
                        ParamKind::PortConnected { port } => {
                            let id = module
                                .dae_system
                                .unknowns
                                .unwrap_index(&SimUnknownKind::KirchoffLaw(port));
                            let id = cx.const_unsigned_int(id.into());
                            builder.int_cmp(id, connected_ports, LLVMIntULT)
                        }
                        ParamKind::ParamSysFun(param) => inst_data
                            .read_param(
                                OsdiInstanceParam::Builtin(param),
                                instance,
                                builder.llbuilder,
                            )
                            .unwrap(),
                        ParamKind::HiddenState(_) => unreachable!(), // TODO  hidden state
                        ParamKind::EnableIntegration => {
                            let flags = flags.read(builder.llbuilder);
                            let is_not_dc =
                                is_flag_set(cx, CALC_REACT_JACOBIAN, flags, builder.llbuilder);
                            let is_not_ic =
                                is_flag_unset(cx, ANALYSIS_IC, flags, builder.llbuilder);
                            &*LLVMBuildAnd(
                                builder.llbuilder,
                                NonNull::from(is_not_dc).as_ptr(),
                                NonNull::from(is_not_ic).as_ptr(),
                                UNNAMED,
                            )
                        }
                        ParamKind::PrevState(state) => {
                            let idx =
                                inst_data.read_state_idx(cx, state, instance, builder.llbuilder);
                            return MemLoc {
                                ptr: prev_state,
                                ptr_ty: cx.ty_double(),
                                ty: cx.ty_double(),
                                indices: vec![idx].into_boxed_slice(),
                            }
                            .into();
                        }
                        ParamKind::NewState(state) => {
                            let idx =
                                inst_data.read_state_idx(cx, state, instance, builder.llbuilder);

                            return MemLoc {
                                ptr: next_state,
                                ptr_ty: cx.ty_double(),
                                ty: cx.ty_double(),
                                indices: vec![idx].into_boxed_slice(),
                            }
                            .into();
                        }
                        ParamKind::EnableLim => {
                            is_flag_set_mem(cx, ENABLE_LIM, &flags, builder.llbuilder)
                        }
                    }
                };
                BuilderVal::Eager(val)
            })
            .collect();

        let cache_vals = (0..module.init.cache_slots.len()).map(|i| unsafe {
            let slot = i.into();
            let val = inst_data.load_cache_slot(module, builder.llbuilder, slot, instance);
            BuilderVal::Eager(val)
        });

        params.extend(cache_vals);
        builder.params = params;

        builder.callbacks = general_callbacks(intern, &mut builder, ret_flags, handle, simparam);

        for (func, kind) in intern.callbacks.iter_enumerated() {
            let cb = match *kind {
                CallBackKind::BuiltinLimit { name, num_args } => {
                    let id = module
                        .lim_table
                        .unwrap_index(&OsdiLimFunction { name, num_args: num_args - 2 });
                    CallbackFun::Prebuilt(self.lim_func(id, num_args - 2, &flags, ret_flags))
                }
                CallBackKind::StoreLimit(state) => {
                    let fun = builder
                        .cx
                        .get_func_by_name("store_lim")
                        .expect("stdlib function store_lim is missing");
                    let fun_ty =
                        cx.ty_func(&[cx.ty_ptr(), cx.ty_int(), cx.ty_double()], cx.ty_double());
                    CallbackFun::Prebuilt(BuiltCallbackFun {
                        fun_ty,
                        fun,
                        state: Box::new([sim_info, state_idx[state]]),
                        num_state: 0,
                    })
                }
                CallBackKind::LimDiscontinuity => {
                    let fun = builder
                        .cx
                        .get_func_by_name("lim_discontinuity")
                        .expect("stdlib function lim_discontinuity is missing");
                    let fun_ty = cx.ty_func(&[cx.ty_ptr()], cx.ty_void());
                    CallbackFun::Prebuilt(BuiltCallbackFun {
                        fun_ty,
                        fun,
                        state: Box::new([ret_flags]),
                        num_state: 0,
                    })
                }
                CallBackKind::Analysis => {
                    let fun = builder
                        .cx
                        .get_func_by_name("analysis")
                        .expect("stdlib function analysis is missing");
                    let fun_ty = cx.ty_func(&[cx.ty_ptr(), cx.ty_ptr()], cx.ty_int());
                    CallbackFun::Prebuilt(BuiltCallbackFun {
                        fun_ty,
                        fun,
                        state: Box::new([sim_info]),
                        num_state: 0,
                    })
                }
                _ => continue,
            };
            builder.callbacks[func] = Some(cb);
        }

        unsafe {
            builder.build_consts();
            builder.build_func();
        }
        let exit_bb = func.layout.last_block().unwrap();

        // store parameters
        builder.select_bb(exit_bb);

        unsafe {
            for reactive in [false, true] {
                let (jacobian_flag, residual_flag, lim_rhs_flag) = if reactive {
                    (CALC_REACT_JACOBIAN, CALC_REACT_RESIDUAL, CALC_REACT_LIM_RHS)
                } else {
                    (CALC_RESIST_JACOBIAN, CALC_RESIST_RESIDUAL, CALC_RESIST_LIM_RHS)
                };

                let store_matrix = |builder: &mut Builder<'_, '_, 'll>| {
                    for entry in module.dae_system.jacobian.keys() {
                        inst_data.store_jacobian(entry, instance, builder, reactive)
                    }
                };
                Self::build_store_results(
                    &mut builder,
                    llfunc,
                    &flags,
                    jacobian_flag,
                    &store_matrix,
                );

                let store_residual = |builder: &mut Builder<'_, '_, 'll>| {
                    for unknown in module.dae_system.unknowns.indices() {
                        inst_data.store_residual(unknown, instance, builder, reactive);
                    }
                };
                Self::build_store_results(
                    &mut builder,
                    llfunc,
                    &flags,
                    residual_flag,
                    &store_residual,
                );

                let store_lim_rhs = |builder: &mut Builder<'_, '_, 'll>| {
                    for unknown in module.dae_system.unknowns.indices() {
                        inst_data.store_lim_rhs(unknown, instance, builder, reactive);
                    }
                };
                Self::build_store_results(
                    &mut builder,
                    llfunc,
                    &flags,
                    lim_rhs_flag,
                    &store_lim_rhs,
                );
            }

            let store_opvars = |builder: &mut Builder<'_, '_, 'll>| {
                for (_, &eval_output) in &inst_data.opvars {
                    inst_data.store_eval_output(eval_output, instance, builder)
                }
            };
            Self::build_store_results(&mut builder, llfunc, &flags, CALC_OP, &store_opvars);
            let store_noise = |builder: &mut Builder<'_, '_, 'll>| {
                for source in &inst_data.noise {
                    for eval_output in source.eval_outputs() {
                        inst_data.store_eval_output(eval_output, instance, builder)
                    }
                }
            };
            Self::build_store_results(&mut builder, llfunc, &flags, CALC_NOISE, &store_noise);

            inst_data.store_bound_step(instance, &builder);
            inst_data.store_delay_times(instance, &builder);

            builder.ret();
        }

        llfunc
    }

    unsafe fn build_store_results(
        builder: &mut Builder<'_, '_, 'll>,
        llfunc: &'ll llvm_sys::LLVMValue,
        flags: &MemLoc<'ll>,
        flag: u32,
        store_val: &dyn Fn(&mut Builder<'_, '_, 'll>),
    ) {
        let cx = builder.cx;
        let bb = LLVMAppendBasicBlockInContext(
            NonNull::from(cx.llcx).as_ptr(),
            NonNull::from(llfunc).as_ptr(),
            UNNAMED,
        );
        let next_bb = LLVMAppendBasicBlockInContext(
            NonNull::from(cx.llcx).as_ptr(),
            NonNull::from(llfunc).as_ptr(),
            UNNAMED,
        );

        let is_set = is_flag_set_mem(cx, flag, flags, builder.llbuilder);
        LLVMBuildCondBr(builder.llbuilder, NonNull::from(is_set).as_ptr(), bb, next_bb);

        LLVMPositionBuilderAtEnd(builder.llbuilder, bb);
        store_val(builder);
        LLVMBuildBr(builder.llbuilder, next_bb);

        LLVMPositionBuilderAtEnd(builder.llbuilder, next_bb);
    }

    fn lim_func(
        &self,
        id: OsdiLimId,
        num_args: u32,
        flags_loc: &MemLoc<'ll>,
        ret_flags_ptr: &'ll llvm_sys::LLVMValue,
    ) -> BuiltCallbackFun<'ll> {
        let OsdiCompilationUnit { cx, tys, .. } = self;
        let table = self.lim_dispatch_table();

        let double = cx.ty_double();
        let c_bool = cx.ty_c_bool();
        let int = cx.ty_int();

        let mut args = vec![cx.ty_ptr(), cx.ty_ptr(), double, double];
        args.resize(num_args as usize + 4, double);
        let fun_ty = cx.ty_func(&args, double);
        let name = &format!("lim_{}_{id}", &self.module.sym);
        let llfunc = cx.declare_int_fn(name, fun_ty);

        unsafe {
            let entry = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let exit = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let val_changed_bb = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let llbuilder = &*LLVMCreateBuilderInContext(NonNull::from(cx.llcx).as_ptr());
            LLVMPositionBuilderAtEnd(NonNull::from(llbuilder).as_ptr(), entry);

            let mut flags = &*LLVMGetParam(NonNull::from(llfunc).as_ptr(), 0);
            flags = &*flags_loc
                .read_with_ptr(NonNull::from(llbuilder).as_ptr(), NonNull::from(flags).as_ptr());
            let mut init = is_flag_set(cx, INIT_LIM, flags, llbuilder);
            init = &*LLVMBuildIntCast2(
                NonNull::from(llbuilder).as_ptr(),
                NonNull::from(init).as_ptr(),
                NonNull::from(c_bool).as_ptr(),
                0,
                UNNAMED,
            );

            let mut val_changed = LLVMBuildAlloca(
                NonNull::from(llbuilder).as_ptr(),
                NonNull::from(c_bool).as_ptr(),
                UNNAMED,
            );
            LLVMBuildStore(
                NonNull::from(llbuilder).as_ptr(),
                NonNull::from(cx.const_c_bool(false)).as_ptr(),
                val_changed,
            );
            let id_val = cx.const_unsigned_int(id.into()) as *const llvm_sys::LLVMValue as *mut _;
            let two_val = cx.const_int(2) as *const llvm_sys::LLVMValue as *mut _;
            let mut gep_indices: [llvm_sys::prelude::LLVMValueRef; 2] = [id_val, two_val];
            let gep_ptr = gep_indices.as_mut_ptr();

            let func_ptr_ptr = LLVMBuildInBoundsGEP2(
                NonNull::from(llbuilder).as_ptr(),
                NonNull::from(tys.osdi_lim_function).as_ptr(),
                NonNull::from(table).as_ptr(),
                gep_ptr,
                2,
                UNNAMED,
            );

            let func_ptr = LLVMBuildLoad2(
                NonNull::from(llbuilder).as_ptr(),
                NonNull::from(cx.ty_ptr()).as_ptr(),
                func_ptr_ptr,
                UNNAMED,
            );
            let mut lim_fn_args = vec![c_bool, cx.ty_ptr(), double, double];
            lim_fn_args.extend((0..num_args).map(|_| double));
            let lim_fn_ty = cx.ty_func(&lim_fn_args, double);
            let mut args = vec![init, &*val_changed];
            args.extend(
                (2..4 + num_args).map(|i| &*LLVMGetParam(NonNull::from(llfunc).as_ptr(), i)),
            );
            let mut raw_args: Vec<*mut llvm_sys::LLVMValue> =
                args.iter().map(|&arg| arg as *const _ as *mut _).collect();
            let res = LLVMBuildCall2(
                NonNull::from(llbuilder).as_ptr(),
                NonNull::from(lim_fn_ty).as_ptr(),
                func_ptr,
                raw_args.as_mut_ptr(),
                args.len() as u32,
                UNNAMED,
            );

            val_changed = LLVMBuildLoad2(
                NonNull::from(llbuilder).as_ptr(),
                NonNull::from(c_bool).as_ptr(),
                val_changed,
                UNNAMED,
            );
            val_changed = LLVMBuildICmp(
                NonNull::from(llbuilder).as_ptr(),
                LLVMIntNE,
                val_changed,
                NonNull::from(cx.const_c_bool(false)).as_ptr(),
                UNNAMED,
            );
            LLVMBuildCondBr(NonNull::from(llbuilder).as_ptr(), val_changed, val_changed_bb, exit);

            LLVMPositionBuilderAtEnd(NonNull::from(llbuilder).as_ptr(), val_changed_bb);
            let ret_flags_ptr = LLVMGetParam(NonNull::from(llfunc).as_ptr(), 1);
            let mut ret_flags = LLVMBuildLoad2(
                NonNull::from(llbuilder).as_ptr(),
                NonNull::from(int).as_ptr(),
                ret_flags_ptr,
                UNNAMED,
            );
            ret_flags = LLVMBuildOr(
                NonNull::from(llbuilder).as_ptr(),
                ret_flags,
                NonNull::from(cx.const_unsigned_int(EVAL_RET_FLAG_LIM)).as_ptr(),
                UNNAMED,
            );
            LLVMBuildStore(NonNull::from(llbuilder).as_ptr(), ret_flags, ret_flags_ptr);
            LLVMBuildBr(NonNull::from(llbuilder).as_ptr(), exit);

            LLVMPositionBuilderAtEnd(NonNull::from(llbuilder).as_ptr(), exit);
            LLVMBuildRet(NonNull::from(llbuilder).as_ptr(), res);

            LLVMDisposeBuilder(NonNull::from(llbuilder).as_ptr());
        }

        BuiltCallbackFun {
            fun_ty,
            fun: llfunc,
            state: Box::new([flags_loc.ptr, ret_flags_ptr]),
            num_state: 0,
        }
    }
}
