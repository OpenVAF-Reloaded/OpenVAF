use core::ptr::NonNull;

use llvm_sys::core::{
    LLVMAddCase, LLVMAppendBasicBlockInContext, LLVMBuildAnd, LLVMBuildBr, LLVMBuildCondBr,
    LLVMBuildICmp, LLVMBuildRet, LLVMBuildSelect, LLVMBuildSwitch, LLVMCreateBuilderInContext,
    LLVMDisposeBuilder, LLVMGetParam, LLVMPositionBuilderAtEnd,
};
use llvm_sys::LLVMIntPredicate::LLVMIntNE;
use mir_llvm::UNNAMED;

use crate::compilation_unit::OsdiCompilationUnit;
use crate::metadata::osdi_0_5::{ACCESS_FLAG_INSTANCE, ACCESS_FLAG_SET};

impl<'ll> OsdiCompilationUnit<'_, '_, 'll> {
    pub fn access_function_prototype(&self) -> &'ll llvm_sys::LLVMValue {
        let cx = &self.cx;
        let void_ptr = cx.ty_ptr();
        let uint32_t = cx.ty_int();
        let fun_ty = cx.ty_func(&[void_ptr, void_ptr, uint32_t, uint32_t], void_ptr);
        let name = &format!("access_{}", &self.module.sym);
        cx.declare_ext_fn(name, fun_ty)
    }

    pub fn access_function(&self) -> &'ll llvm_sys::LLVMValue {
        let llfunc = self.access_function_prototype();
        let OsdiCompilationUnit { inst_data, model_data, cx, .. } = &self;

        unsafe {
            let entry = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let err_exit = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let model_bb = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let inst_bb = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let opvar_bb = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let llbuilder = LLVMCreateBuilderInContext(NonNull::from(cx.llcx).as_ptr());

            LLVMPositionBuilderAtEnd(llbuilder, entry);

            // get params
            let inst = LLVMGetParam(NonNull::from(llfunc).as_ptr(), 0);
            let model = LLVMGetParam(NonNull::from(llfunc).as_ptr(), 1);
            let param_id = LLVMGetParam(NonNull::from(llfunc).as_ptr(), 2);
            let flags = LLVMGetParam(NonNull::from(llfunc).as_ptr(), 3);

            // constants
            let access_flag_instance =
                NonNull::from(cx.const_unsigned_int(ACCESS_FLAG_INSTANCE)).as_ptr();
            let access_flag_set = NonNull::from(cx.const_unsigned_int(ACCESS_FLAG_SET)).as_ptr();
            let zero = NonNull::from(cx.const_unsigned_int(0)).as_ptr();

            //
            // start building function body
            // check various flags
            // compute boolean indicating if instance flag is set
            let flags_and_instance = LLVMBuildAnd(llbuilder, flags, access_flag_instance, UNNAMED);
            let instance_flag_set =
                LLVMBuildICmp(llbuilder, LLVMIntNE, flags_and_instance, zero, UNNAMED);

            // compute boolean indicating if write flag is set
            let flags_and_set = LLVMBuildAnd(llbuilder, flags, access_flag_set, UNNAMED);
            let write_flag_set = LLVMBuildICmp(llbuilder, LLVMIntNE, flags_and_set, zero, UNNAMED);

            // build if block, true block is for instance flag set, false block is for instance flag not set
            LLVMBuildCondBr(llbuilder, instance_flag_set, inst_bb, model_bb);

            //
            // start building instance params access block
            // this block scans all instance parameters and tries to find the one with param_id
            // instance parameter indices match osdi ids
            // it returns a pointer into the parameter storage in instance structure
            LLVMPositionBuilderAtEnd(llbuilder, inst_bb);

            // create switch statement, based on param_id, default block is opvar_bb
            // number of cases obtained from inst_data
            let switch_inst =
                LLVMBuildSwitch(llbuilder, param_id, opvar_bb, inst_data.params.len() as u32);

            // build cases, one for each instance parameter
            // assumes osdi ids of instance parameters are 0..inst_data.params.len()
            for param_idx in 0..inst_data.params.len() {
                // create building block bb
                let bb = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                LLVMPositionBuilderAtEnd(llbuilder, bb);
                // construct case constant, add case with building block bb
                let case = NonNull::from(cx.const_unsigned_int(param_idx as u32)).as_ptr();
                LLVMAddCase(switch_inst, case, bb);

                // build code for retrieving pointer to parameter storage of
                // param_idx-th instance parameter in instance structure
                let (ptr, _) = inst_data.nth_param_ptr(param_idx as u32, &*inst, &*llbuilder);

                // set the param_given flag if write flag is given
                // create new block for writing
                let write = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                // create new block for return
                let ret = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                // build if, true block is for setting write flag (write block), false block is return (ret block)
                LLVMBuildCondBr(llbuilder, write_flag_set, write, ret);

                // build true block
                LLVMPositionBuilderAtEnd(llbuilder, write);

                // build code for setting the param_given flag
                inst_data.set_nth_param_given(cx, param_idx as u32, &*inst, &*llbuilder);
                // build branch (jump) to false block
                LLVMBuildBr(llbuilder, ret);

                // build false block
                // return the pointer
                LLVMPositionBuilderAtEnd(llbuilder, ret);
                LLVMBuildRet(llbuilder, NonNull::from(ptr).as_ptr());
            }

            //
            // start building model params access block
            LLVMPositionBuilderAtEnd(llbuilder, model_bb);

            // create switch statement, based on param_id, default block is opvar_bb
            // number of cases: is the number of cases ok?
            // should it be inst_data.params.len()+model_data.params.len()
            let switch_model = LLVMBuildSwitch(
                llbuilder,
                param_id,
                opvar_bb,
                inst_data.params.len() as u32 + model_data.params.len() as u32,
            );

            // build cases, one for each instance parameter
            // assumes osdi ids of instance parameters are 0..inst_data.params.len()
            for param_idx in 0..inst_data.params.len() {
                // create building block bb
                let bb = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                LLVMPositionBuilderAtEnd(llbuilder, bb);
                // construct case constant, add case with building block bb
                // instance parameter IDs are 0..num_instance_params-1
                let case = cx.const_unsigned_int(param_idx as u32);

                LLVMAddCase(switch_model, NonNull::from(case).as_ptr(), bb);

                // build code for getting the pointer to
                // param_idx-th instance parameter in model structure
                let (ptr, _) = model_data.nth_inst_param_ptr(
                    inst_data,
                    param_idx as u32,
                    &*model,
                    &*llbuilder,
                );

                // set the param_given flag if write flag is given
                let write = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                let ret = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                LLVMBuildCondBr(llbuilder, write_flag_set, write, ret);
                LLVMPositionBuilderAtEnd(llbuilder, write);
                // build code for setting the param_given flag of an instance parameter in model structure
                model_data.set_nth_inst_param_given(cx, param_idx as u32, &*model, &*llbuilder);
                LLVMBuildBr(llbuilder, ret);

                // return the pointer
                LLVMPositionBuilderAtEnd(llbuilder, ret);
                LLVMBuildRet(llbuilder, NonNull::from(ptr).as_ptr());
            }

            // build cases, one for each model parameter
            // assumes osdi ids of model parameters start with inst_data.params.len()
            for param_idx in 0..model_data.params.len() {
                // create building block bb
                let bb = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                LLVMPositionBuilderAtEnd(llbuilder, bb);
                // construct case constant, add case with building block bb
                // model parameter IDs are num_instance_params..num_instance_params+num_model_params-1
                // num_model_params == model_data.params.len() counts only model parameters
                let case = cx.const_unsigned_int((inst_data.params.len() + param_idx) as u32);
                LLVMAddCase(switch_model, NonNull::from(case).as_ptr(), bb);

                // build code for getting the pointer to
                // param_idx-th model parameter in model structure
                let (ptr, _) = model_data.nth_param_ptr(param_idx as u32, &*model, &*llbuilder);

                // set the param_given flag if write flag is given
                let write = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                let ret = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                LLVMBuildCondBr(llbuilder, write_flag_set, write, ret);
                LLVMPositionBuilderAtEnd(llbuilder, write);
                // build code for setting the param_given flag of a model parameter in model structure
                model_data.set_nth_param_given(cx, param_idx as u32, &*model, &*llbuilder);
                LLVMBuildBr(llbuilder, ret);

                // return the pointer
                LLVMPositionBuilderAtEnd(llbuilder, ret);
                LLVMBuildRet(llbuilder, NonNull::from(ptr).as_ptr());
            }

            // null pointer constant
            let null_ptr = cx.const_null_ptr();

            //
            // default case block if instance/model parameter with given osdi id not found
            LLVMPositionBuilderAtEnd(llbuilder, opvar_bb);
            // create switch based on param_id, default block is err_exit
            let switch_opvar =
                LLVMBuildSwitch(llbuilder, param_id, err_exit, inst_data.opvars.len() as u32);

            // build cases, one for each opvar
            // assumes osdi ids of opvars start with model_data.params.len() + inst_data.params.len()
            for opvar_idx in 0..inst_data.opvars.len() {
                // get inst_data, model_data, and cx
                let OsdiCompilationUnit { inst_data, model_data, cx, .. } = &self;
                // create building block bb
                let bb = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                LLVMPositionBuilderAtEnd(llbuilder, bb);
                // construct case constant, add case with building block bb
                let case = cx.const_unsigned_int(
                    (model_data.params.len() + inst_data.params.len() + opvar_idx) as u32,
                );

                LLVMAddCase(switch_opvar, NonNull::from(case).as_ptr(), bb);

                // build code for getting the pointer to
                // param_idx-th opvar in instance structure
                let (ptr, _) = self.nth_opvar_ptr(opvar_idx as u32, &*inst, &*model, &*llbuilder);
                // return the pointer
                LLVMBuildRet(llbuilder, NonNull::from(ptr).as_ptr());
            }

            // return NULL on unknown id
            LLVMPositionBuilderAtEnd(llbuilder, err_exit);
            LLVMBuildRet(llbuilder, NonNull::from(null_ptr).as_ptr());

            LLVMDisposeBuilder(llbuilder);
        }

        llfunc
    }

    pub fn given_flag_instance(&self) -> &'ll llvm_sys::LLVMValue {
        let cx = &self.cx;
        let void_ptr = cx.ty_ptr();
        let uint32_t = cx.ty_int();
        let fun_ty = cx.ty_func(&[void_ptr, uint32_t], uint32_t);
        let name = &format!("given_flag_instance_{}", &self.module.sym);
        let llfunc = cx.declare_int_c_fn(name, fun_ty);

        let OsdiCompilationUnit { inst_data, cx, .. } = &self;

        unsafe {
            let zero = cx.const_int(0);
            let one = cx.const_int(1);

            let entry = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let not_found = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let llbuilder = LLVMCreateBuilderInContext(NonNull::from(cx.llcx).as_ptr());

            LLVMPositionBuilderAtEnd(llbuilder, entry);

            // get params
            let ptr = LLVMGetParam(NonNull::from(llfunc).as_ptr(), 0);
            let param_id = LLVMGetParam(NonNull::from(llfunc).as_ptr(), 1);

            //
            // start building function body

            // create switch statement, based on param_id, default block is opvar_bb
            // number of cases obtained from inst_data
            let switch_inst =
                LLVMBuildSwitch(llbuilder, param_id, not_found, inst_data.params.len() as u32);

            // build cases, one for each instance parameter
            // assumes osdi ids of instance parameters are 0..inst_data.params.len()
            for param_idx in 0..inst_data.params.len() {
                // create building block bb
                let bb = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                LLVMPositionBuilderAtEnd(llbuilder, bb);
                // construct case constant, add case with building block bb
                let case = cx.const_unsigned_int(param_idx as u32);
                LLVMAddCase(switch_inst, NonNull::from(case).as_ptr(), bb);

                // Build code for checking the parameter given flag
                let is_given =
                    inst_data.is_nth_param_given(cx, param_idx as u32, &*ptr, &*llbuilder);
                let is_given = LLVMBuildSelect(
                    llbuilder,
                    NonNull::from(is_given).as_ptr(),
                    NonNull::from(one).as_ptr(),
                    NonNull::from(zero).as_ptr(),
                    UNNAMED,
                );

                // Return value
                LLVMBuildRet(llbuilder, is_given);
            }

            // build not_found block
            LLVMPositionBuilderAtEnd(llbuilder, not_found);

            // Return 0
            LLVMBuildRet(llbuilder, NonNull::from(zero).as_ptr());

            //Do we have to dispose this?
            //LLVMDisposeBuilder(llbuilder);
        }

        llfunc
    }

    pub fn given_flag_model(&self) -> &'ll llvm_sys::LLVMValue {
        let OsdiCompilationUnit { inst_data, model_data, cx, .. } = &self;
        let args_ = [cx.ty_ptr(), cx.ty_int()];
        let fun_ty = cx.ty_func(&args_, cx.ty_int());
        let name = &format!("given_flag_model_{}", self.module.sym);
        let llfunc = cx.declare_int_c_fn(name, fun_ty);

        unsafe {
            let zero = cx.const_int(0);
            let one = cx.const_int(1);

            let entry = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let not_found = LLVMAppendBasicBlockInContext(
                NonNull::from(cx.llcx).as_ptr(),
                NonNull::from(llfunc).as_ptr(),
                UNNAMED,
            );
            let llbuilder = LLVMCreateBuilderInContext(NonNull::from(cx.llcx).as_ptr());

            LLVMPositionBuilderAtEnd(llbuilder, entry);

            // get params
            let ptr = LLVMGetParam(NonNull::from(llfunc).as_ptr(), 0);
            let param_id = LLVMGetParam(NonNull::from(llfunc).as_ptr(), 1);

            //
            // start building function body

            // create switch statement, based on param_id, default block is opvar_bb
            // number of cases obtained from inst_data
            let switch_inst = LLVMBuildSwitch(
                llbuilder,
                param_id,
                not_found,
                (model_data.params.len() + inst_data.params.len()) as u32,
            );

            // build cases, one for each instance parameter
            // assumes osdi ids of instance parameters are 0..inst_data.params.len()
            for param_idx in 0..inst_data.params.len() {
                // create building block bb
                let bb = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                LLVMPositionBuilderAtEnd(llbuilder, bb);
                // construct case constant, add case with building block bb
                let case = cx.const_unsigned_int(param_idx as u32);
                LLVMAddCase(switch_inst, NonNull::from(case).as_ptr(), bb);

                // Build code for checking the parameter given flag
                let is_given =
                    model_data.is_nth_inst_param_given(cx, param_idx as u32, &*ptr, &*llbuilder);
                let is_given = LLVMBuildSelect(
                    llbuilder,
                    NonNull::from(is_given).as_ptr(),
                    NonNull::from(one).as_ptr(),
                    NonNull::from(zero).as_ptr(),
                    UNNAMED,
                );

                // Return value
                LLVMBuildRet(llbuilder, is_given);
            }

            // build cases, one for each model parameter
            // assumes osdi ids of model parameters start with inst_data.params.len()
            for param_idx in 0..model_data.params.len() {
                // create building block bb
                let bb = LLVMAppendBasicBlockInContext(
                    NonNull::from(cx.llcx).as_ptr(),
                    NonNull::from(llfunc).as_ptr(),
                    UNNAMED,
                );
                LLVMPositionBuilderAtEnd(llbuilder, bb);
                // construct case constant, add case with building block bb
                let case = cx.const_unsigned_int((inst_data.params.len() + param_idx) as u32);
                LLVMAddCase(switch_inst, NonNull::from(case).as_ptr(), bb);

                // Build code for checking the parameter given flag
                let is_given =
                    model_data.is_nth_param_given(cx, param_idx as u32, &*ptr, &*llbuilder);
                let is_given = LLVMBuildSelect(
                    llbuilder,
                    NonNull::from(is_given).as_ptr(),
                    NonNull::from(one).as_ptr(),
                    NonNull::from(zero).as_ptr(),
                    UNNAMED,
                );

                // Return value
                LLVMBuildRet(llbuilder, is_given);
            }

            // build not_found block
            LLVMPositionBuilderAtEnd(llbuilder, not_found);

            // Return 0
            LLVMBuildRet(llbuilder, NonNull::from(zero).as_ptr());

            //Do we have to dispose this?
            //LLVMDisposeBuilder(llbuilder);
        }

        llfunc
    }
}
