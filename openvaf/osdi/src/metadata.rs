use core::ptr::NonNull;
use std::iter::once;

use hir::{CompilationDB, ParamSysFun, Type};
use hir_def::db::HirDefDB;
use hir_def::ndatable::NDATable;
use hir_lower::{CurrentKind, ImplicitEquation, ParamKind};
use lasso::{Rodeo, Spur};
use llvm_sys::core::{
    LLVMConstArray2, LLVMConstInt, LLVMConstPtrToInt, LLVMGetArrayLength2, LLVMGetDataLayoutStr,
    LLVMGetElementType, LLVMGetUndef,
};
use llvm_sys::prelude::LLVMValueRef;
use llvm_sys::target::{
    LLVMABISizeOfType, LLVMByteOrder, LLVMByteOrdering, LLVMCreateTargetData, LLVMOffsetOfElement,
    LLVMTargetDataRef,
};
use llvm_sys::LLVMValue;
use mir::{ValueDef, F_ZERO};
use mir_llvm::CodegenCx;
use sim_back::dae::{MatrixEntry, NoiseSourceKind, ResidualNatureKind};
use sim_back::SimUnknownKind;
use smol_str::SmolStr;
use stdx::iter::zip;

use crate::compilation_unit::{OsdiCompilationUnit, OsdiModule};
use crate::inst_data::{
    OsdiInstanceParam, COLLAPSED, JACOBIAN_PTR_REACT, JACOBIAN_PTR_RESIST, NODE_MAPPING, STATE_IDX,
};
use crate::load::JacobianLoadType;
use crate::metadata::osdi_0_5::{
    OsdiAbsDelayInfo, OsdiDescriptor, OsdiJacobianEntry, OsdiNatureRef, OsdiNode, OsdiNodePair,
    OsdiNoiseSource, OsdiParamOpvar, OsdiTys, JACOBIAN_ENTRY_REACT, JACOBIAN_ENTRY_REACT_CONST,
    JACOBIAN_ENTRY_RESIST, JACOBIAN_ENTRY_RESIST_CONST, MODULEFLAG_ABSTIME, NATREF_DISCIPLINE_FLOW,
    NATREF_DISCIPLINE_POTENTIAL, NATREF_NONE, NOISE_TYPE_FLICKER, NOISE_TYPE_TABLE,
    NOISE_TYPE_WHITE, PARA_KIND_INST, PARA_KIND_MODEL, PARA_KIND_OPVAR, PARA_TY_INT, PARA_TY_REAL,
    PARA_TY_STR,
};
use crate::ty_len;

#[allow(unused_parens, dead_code)]
pub mod osdi_0_5;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct OsdiLimFunction {
    pub name: Spur,
    pub num_args: u32,
}

impl OsdiLimFunction {
    pub fn to_ll_val<'ll>(
        self,
        ctx: &CodegenCx<'_, 'll>,
        tys: &'ll OsdiTys,
    ) -> &'ll llvm_sys::LLVMValue {
        osdi_0_5::OsdiLimFunction {
            name: ctx.literals.resolve(&self.name).to_owned(),
            num_args: self.num_args,
            func_ptr: ctx.const_null_ptr(),
        }
        .to_ll_val(ctx, tys)
    }
}

impl osdi_0_5::OsdiAttributeValue {
    pub fn to_ll_val<'ll>(
        &self,
        ctx: &CodegenCx<'_, 'll>,
        tys: &'ll OsdiTys,
    ) -> &'ll llvm_sys::LLVMValue {
        // Union storage type (array of integers)
        let ty = tys.osdi_attribute_value;
        unsafe {
            // TODO: handle endianness. Currently works for little endian (PC, x86 & arm64 MACS).
            // Array elements are i64 or larger. When lowering integers/pointers/doubles that are
            // smaller than the array element this is wrong on big endian.
            // Check target (it must be little endian)
            let data_layout = LLVMGetDataLayoutStr(NonNull::from(ctx.llmod).as_ptr());
            let target_data = LLVMCreateTargetData(data_layout);
            let order = LLVMByteOrder(target_data);
            if order != LLVMByteOrdering::LLVMLittleEndian {
                panic!("Can handle little endian only.")
            }
            // Raw pointers
            let raw_ty = NonNull::from(ty).as_ptr();
            // Get array length
            let len = LLVMGetArrayLength2(raw_ty);
            // Get array member size in bytes
            let elem_ty = LLVMGetElementType(raw_ty);
            // Element size is >= entry size
            // Initializer array with undef values
            let mut elems = vec![LLVMGetUndef(elem_ty); len as usize];
            match self {
                osdi_0_5::OsdiAttributeValue::String(s) => {
                    // Constant global string
                    let llval = ctx.const_str_uninterned(s);
                    let valref = llval as *const LLVMValue as LLVMValueRef;
                    // Cast to array entry type
                    let ptr_as_int = LLVMConstPtrToInt(valref, elem_ty);
                    // Fill initializer array
                    elems[0] = ptr_as_int;
                }
                osdi_0_5::OsdiAttributeValue::Real(f) => {
                    // Real number
                    let ipat = f.to_bits();
                    // Create array entry
                    let entry = LLVMConstInt(elem_ty, ipat, 0);
                    // Fill initializer array
                    elems[0] = entry;
                }
                osdi_0_5::OsdiAttributeValue::Integer(i) => {
                    // Integer (i32)
                    let entry = LLVMConstInt(elem_ty, *i as i64 as u64, 0);
                    // Fill initializer array
                    elems[0] = entry;
                }
                _ => panic!("Unknown attribute value union member type."),
            }
            // Construct array
            &*LLVMConstArray2(elem_ty, elems.as_mut_ptr(), len)
        }
    }
}

impl<'ll> OsdiCompilationUnit<'_, '_, 'll> {
    pub fn param_opvar(&self) -> Vec<OsdiParamOpvar> {
        let OsdiCompilationUnit { inst_data, model_data, module, .. } = self;
        fn para_ty_flags(ty: &Type) -> u32 {
            match ty.base_type() {
                Type::Real => PARA_TY_REAL,
                Type::Integer => PARA_TY_INT,
                Type::String => PARA_TY_STR,
                _ => unreachable!(),
            }
        }

        let inst_params = inst_data.params.keys().map(|param| match param {
            OsdiInstanceParam::Builtin(builtin) => {
                let mut name = vec![format!("${builtin:?}")];
                if let Some(alias) = self.module.info.sys_fun_alias.get(builtin) {
                    name.extend(alias.iter().map(SmolStr::to_string))
                }
                OsdiParamOpvar {
                    num_alias: name.len() as u32 - 1,
                    name,
                    description: match builtin {
                        ParamSysFun::mfactor => "Multiplier (Verilog-A $mfactor)".to_owned(),
                        _ => "".to_owned(),
                    },
                    units: match builtin {
                        ParamSysFun::yposition | ParamSysFun::xposition => "m".to_owned(),
                        ParamSysFun::angle => "deg".to_owned(),
                        _ => "".to_owned(),
                    },
                    flags: PARA_TY_REAL | PARA_KIND_INST,
                    len: 0,
                }
            }
            OsdiInstanceParam::User(param) => {
                let param_info = &module.info.params[param];
                let ty = param.ty(self.db);

                let flags = para_ty_flags(&ty) | PARA_KIND_INST;
                OsdiParamOpvar {
                    name: once(&param_info.name)
                        .chain(&*param_info.alias)
                        .map(SmolStr::to_string)
                        .collect(),
                    num_alias: param_info.alias.len() as u32,
                    description: param_info.description.clone(),
                    units: param_info.unit.clone(),
                    flags,
                    len: ty_len(&ty).unwrap_or(0),
                }
            }
        });

        let model_params = model_data.params.keys().filter_map(|param| {
            let param_info = &module.info.params[param];
            if param_info.is_instance {
                return None;
            }
            let ty = param.ty(self.db);
            let flags = para_ty_flags(&ty) | PARA_KIND_MODEL;
            let param_opvar = OsdiParamOpvar {
                name: once(&param_info.name)
                    .chain(&*param_info.alias)
                    .map(SmolStr::to_string)
                    .collect(),
                num_alias: param_info.alias.len() as u32,
                description: param_info.description.clone(),
                units: param_info.unit.clone(),
                flags,
                len: ty_len(&ty).unwrap_or(0),
            };
            Some(param_opvar)
        });

        let opvars = inst_data.opvars.keys().map(|opvar| {
            let opvar_info = &module.info.op_vars[opvar];
            // TODO inst params
            let ty = opvar.ty(self.db);
            let flags = para_ty_flags(&ty) | PARA_KIND_OPVAR;
            OsdiParamOpvar {
                name: vec![opvar.name(self.db).to_string()],
                num_alias: 0,
                description: opvar_info.description.clone(),
                units: opvar_info.unit.clone(),
                flags,
                len: ty_len(&ty).unwrap_or(0),
            }
        });

        inst_params.chain(model_params).chain(opvars).collect()
    }

    pub fn nodes(&self, target_data: &LLVMTargetDataRef, db: &CompilationDB) -> Vec<OsdiNode> {
        let OsdiCompilationUnit { inst_data, module, .. } = self;
        module
            .dae_system
            .unknowns
            .iter_enumerated()
            .map(|(id, unknown)| {
                let residual_nature_kind = module.dae_system.residual[id].nature_kind;
                let (name, units, residual_units, is_flow, _, _) =
                    sim_unknown_info(*unknown, residual_nature_kind, db);
                let resist_residual_off =
                    inst_data.residual_off(id, false, target_data).unwrap_or(u32::MAX);
                let react_residual_off =
                    inst_data.residual_off(id, true, target_data).unwrap_or(u32::MAX);

                let resist_limit_rhs_off =
                    inst_data.lim_rhs_off(id, false, target_data).unwrap_or(u32::MAX);
                let react_limit_rhs_off =
                    inst_data.lim_rhs_off(id, true, target_data).unwrap_or(u32::MAX);
                OsdiNode {
                    name,
                    units,
                    residual_units,
                    resist_residual_off,
                    react_residual_off,
                    is_flow,
                    resist_limit_rhs_off,
                    react_limit_rhs_off,
                }
            })
            .collect()
    }

    fn is_const(&self, entry: &MatrixEntry, reactive: bool) -> bool {
        let entry = if reactive { entry.react } else { entry.resist };
        match self.module.eval.dfg.value_def(entry) {
            ValueDef::Result(_, _) => false,
            ValueDef::Param(param) => self
                .module
                .intern
                .params
                .get_index(param)
                .map_or(true, |(kind, _)| !kind.op_dependent()),
            ValueDef::Const(_) => true,
            ValueDef::Invalid => unreachable!(),
        }
    }

    pub fn jacobian_entries(&self, target_data: &LLVMTargetDataRef) -> Vec<OsdiJacobianEntry> {
        let OsdiCompilationUnit { inst_data, module, .. } = self;
        let mut jacobian_ptr_react_offset = unsafe {
            LLVMOffsetOfElement(
                *target_data,
                NonNull::from(inst_data.ty).as_ptr(),
                JACOBIAN_PTR_REACT,
            )
        } as u32;

        module
            .dae_system
            .jacobian
            .iter()
            .map(|entry| {
                let mut flags = 0;
                let mut react_ptr_off = u32::MAX;

                if self.is_const(entry, false) {
                    flags |= JACOBIAN_ENTRY_RESIST_CONST
                }

                if self.is_const(entry, true) {
                    flags |= JACOBIAN_ENTRY_REACT_CONST
                }

                if entry.resist != F_ZERO {
                    flags |= JACOBIAN_ENTRY_RESIST;
                }

                if entry.react != F_ZERO {
                    flags |= JACOBIAN_ENTRY_REACT;
                    react_ptr_off = jacobian_ptr_react_offset;
                    jacobian_ptr_react_offset += 8;
                }
                OsdiJacobianEntry {
                    nodes: OsdiNodePair { node_1: entry.row.into(), node_2: entry.col.into() },
                    react_ptr_off,
                    flags,
                }
            })
            .collect()
    }

    pub fn collapsible(&self) -> Vec<OsdiNodePair> {
        self.module
            .node_collapse
            .pairs()
            .map(|(_, node1, node2)| OsdiNodePair {
                node_1: node1.into(),
                node_2: node2.map_or(u32::MAX, u32::from),
            })
            .collect()
    }

    pub fn inputs(&self) -> Vec<OsdiNodePair> {
        self.module
            .dae_system
            .model_inputs
            .iter()
            .map(|(node1, node2)| OsdiNodePair { node_1: (*node1).into(), node_2: (*node2).into() })
            .collect()
    }

    pub fn absdelays(&self, target_data: &LLVMTargetDataRef) -> Vec<OsdiAbsDelayInfo> {
        let OsdiCompilationUnit { inst_data, module, .. } = self;
        let find_node = |eq: ImplicitEquation| -> u32 {
            module
                .dae_system
                .unknowns
                .index(&SimUnknownKind::Implicit(eq))
                .map_or(u32::MAX, u32::from)
        };
        module
            .intern
            .absdelay_equations
            .iter()
            .enumerate()
            .map(|(i, &(eq_y, eq_z))| OsdiAbsDelayInfo {
                y_node: find_node(eq_y),
                z_node: find_node(eq_z),
                td_offset: inst_data.delay_time_offset(i, target_data).unwrap_or(u32::MAX),
            })
            .collect()
    }

    pub fn unknown_residual_natures(
        &self,
        db: &CompilationDB,
    ) -> (Vec<OsdiNatureRef>, Vec<OsdiNatureRef>) {
        let mut uvec = Vec::new();
        let mut rvec = Vec::new();
        for (idx, &unknown) in self.module.dae_system.unknowns.iter_enumerated() {
            let residual_nature_kind = self.module.dae_system.residual[idx].nature_kind;
            let (_, _, _, _, unknown_natref, residual_natref) =
                sim_unknown_info(unknown, residual_nature_kind, db);
            uvec.push(unknown_natref);
            rvec.push(residual_natref);
        }
        (uvec, rvec)
    }

    pub fn descriptor(
        &self,
        target_data: &llvm_sys::target::LLVMTargetDataRef,
        db: &CompilationDB,
    ) -> OsdiDescriptor<'ll> {
        let collapsible = self.collapsible();
        let inputs = self.inputs();
        let OsdiCompilationUnit { ref inst_data, ref model_data, module, cx, .. } = *self;

        unsafe {
            let node_mapping_offset = LLVMOffsetOfElement(
                *target_data,
                NonNull::from(inst_data.ty).as_ptr(),
                NODE_MAPPING,
            ) as u32;
            let jacobian_ptr_resist_offset = LLVMOffsetOfElement(
                *target_data,
                NonNull::from(inst_data.ty).as_ptr(),
                JACOBIAN_PTR_RESIST,
            ) as u32;

            let collapsed_offset =
                LLVMOffsetOfElement(*target_data, NonNull::from(inst_data.ty).as_ptr(), COLLAPSED)
                    as u32;
            let bound_step_offset = inst_data.bound_step_elem().map_or(u32::MAX, |elem| {
                LLVMOffsetOfElement(*target_data, NonNull::from(inst_data.ty).as_ptr(), elem) as u32
            });

            let state_idx_off =
                LLVMOffsetOfElement(*target_data, NonNull::from(inst_data.ty).as_ptr(), STATE_IDX)
                    as u32;

            let instance_size =
                LLVMABISizeOfType(*target_data, NonNull::from(inst_data.ty).as_ptr()) as u32;
            let model_size =
                LLVMABISizeOfType(*target_data, NonNull::from(model_data.ty).as_ptr()) as u32;

            let noise_sources: Vec<_> = module
                .dae_system
                .noise_sources
                .iter()
                .map(|source| {
                    let node_1: u32 = source.hi.into();
                    let node_2: u32 = source.lo.map_or(u32::MAX, u32::from);
                    let name = cx.literals.resolve(&source.name).to_owned();
                    OsdiNoiseSource { name, nodes: OsdiNodePair { node_1, node_2 } }
                })
                .collect();

            let noise_source_type: Vec<_> =
                zip(&module.dae_system.noise_sources, &self.inst_data.noise)
                    .map(|(src, eval_outputs)| match src.kind {
                        NoiseSourceKind::WhiteNoise { .. } => NOISE_TYPE_WHITE,
                        NoiseSourceKind::FlickerNoise { .. } => NOISE_TYPE_FLICKER,
                        NoiseSourceKind::NoiseTable { .. } => NOISE_TYPE_TABLE,
                    })
                    .collect();

            let (uvec, rvec) = self.unknown_residual_natures(db);

            let mut module_flags = 0u32;
            module.intern.params.iter().for_each(|(p, _)| {
                if let ParamKind::Abstime = p {
                    module_flags |= MODULEFLAG_ABSTIME;
                }
            });

            OsdiDescriptor {
                name: module.info.module.name(db),
                num_nodes: module.dae_system.unknowns.len() as u32,
                num_terminals: module.info.module.ports(db).len() as u32,
                nodes: self.nodes(target_data, db),
                num_jacobian_entries: module.dae_system.jacobian.len() as u32,
                jacobian_entries: self.jacobian_entries(target_data),
                num_collapsible: collapsible.len() as u32,
                collapsible,
                collapsed_offset,
                bound_step_offset,

                // TODO noise
                num_noise_src: noise_sources.len() as u32,
                noise_sources,

                num_params: model_data.params.len() as u32 + inst_data.params.len() as u32,
                num_instance_params: inst_data.params.len() as u32,
                num_opvars: inst_data.opvars.len() as u32,
                param_opvar: self.param_opvar(),

                node_mapping_offset,
                jacobian_ptr_resist_offset,
                state_idx_off,
                instance_size,
                model_size,
                access: self.access_function_prototype(),
                setup_model: self.setup_model_prototype(),
                setup_instance: self.setup_instance_prototype(),
                eval: self.eval_prototype(),
                load_noise: self.load_noise(),
                load_residual_resist: self.load_residual(false),
                load_residual_react: self.load_residual(true),
                load_spice_rhs_dc: self.load_spice_rhs(false),
                load_spice_rhs_tran: self.load_spice_rhs(true),
                load_jacobian_resist: self.load_jacobian(JacobianLoadType::Resist, false),
                load_jacobian_react: self.load_jacobian(JacobianLoadType::React, false),
                load_jacobian_tran: self.load_jacobian(JacobianLoadType::Tran, false),
                num_states: self.module.intern.lim_state.len() as u32,
                load_limit_rhs_resist: self.load_lim_rhs(false),
                load_limit_rhs_react: self.load_lim_rhs(true),
                given_flag_model: self.given_flag_model(),
                given_flag_instance: self.given_flag_instance(),
                num_resistive_jacobian_entries: module.dae_system.num_resistive,
                num_reactive_jacobian_entries: module.dae_system.num_reactive,
                write_jacobian_array_resist: self.write_jacobian_array(JacobianLoadType::Resist),
                write_jacobian_array_react: self.write_jacobian_array(JacobianLoadType::React),
                num_inputs: inputs.len() as u32,
                inputs,
                load_jacobian_with_offset_resist: self
                    .load_jacobian(JacobianLoadType::Resist, true),
                load_jacobian_with_offset_react: self.load_jacobian(JacobianLoadType::React, true),
                unknown_nature: uvec,
                residual_nature: rvec,
                noise_source_type,
                load_noise_params: self.load_noise_params(),
                module_flags,
                absdelay_count: module.intern.absdelay_equations.len() as u32,
                absdelays: self.absdelays(target_data),
            }
        }
    }
}

impl OsdiModule<'_> {
    pub fn intern_node_strs(&self, intern: &mut Rodeo, db: &CompilationDB) {
        for (idx, &unknown) in self.dae_system.unknowns.iter_enumerated() {
            let residual_nature_kind = self.dae_system.residual[idx].nature_kind;
            let (name, units, residual_units, _, _, _) =
                sim_unknown_info(unknown, residual_nature_kind, db);
            intern.get_or_intern(&name);
            intern.get_or_intern(&units);
            intern.get_or_intern(&residual_units);
        }
    }
}

fn sim_unknown_info(
    unknown: SimUnknownKind,
    residual_nature_kind: ResidualNatureKind,
    db: &CompilationDB,
) -> (String, String, String, bool, OsdiNatureRef, OsdiNatureRef) {
    let name;
    let discipline;
    let is_flow;
    let mut unknown_nature = OsdiNatureRef { ref_type: NATREF_NONE, index: u32::MAX };
    let mut residual_nature = OsdiNatureRef { ref_type: NATREF_NONE, index: u32::MAX };

    match unknown {
        SimUnknownKind::KirchoffLaw(node) => {
            name = node.name(db).to_string();
            discipline = Some(node.discipline(db));
            is_flow = false;
        }

        SimUnknownKind::Current(CurrentKind::Unnamed { hi, lo }) => {
            name = if let Some(lo) = lo {
                format!("flow({},{})", &hi.name(db), &lo.name(db))
            } else {
                format!("flow({})", &hi.name(db))
            };
            discipline = Some(hi.discipline(db));
            is_flow = true;
        }
        SimUnknownKind::Current(CurrentKind::Branch(br)) => {
            name = format!("flow({})", &br.name(db));
            discipline = Some(br.discipline(db));
            is_flow = true;
        }
        SimUnknownKind::Current(CurrentKind::Port(node)) => {
            name = format!("flow(<{}>)", &node.name(db));
            discipline = Some(node.discipline(db));
            is_flow = true;
        }
        SimUnknownKind::Implicit(equ) => {
            name = format!("implicit_equation_{}", u32::from(equ));
            discipline = None;
            is_flow = false;
        }
    };

    // Get discipline index
    let cu = db.compilation_unit();
    let nda_table = db.nda_table(cu.root_file());

    // Get units
    let mut units = String::default();
    let mut residual_units = String::default();
    if let Some(discipline) = discipline {
        // Discipline index
        let ndx = nda_table.discipline_name_map.get(&discipline.name(db)).unwrap().into_raw();

        // Unknown
        let nature = if is_flow {
            unknown_nature.ref_type = NATREF_DISCIPLINE_FLOW;
            unknown_nature.index = ndx;
            discipline.flow(db)
        } else {
            unknown_nature.ref_type = NATREF_DISCIPLINE_POTENTIAL;
            unknown_nature.index = ndx;
            discipline.potential(db)
        };
        if let Some(nature) = nature {
            units = nature.units(db)
        }
        // Residual
        let nature = match residual_nature_kind {
            ResidualNatureKind::Flow => {
                residual_nature.ref_type = NATREF_DISCIPLINE_FLOW;
                residual_nature.index = ndx;
                discipline.flow(db)
            }
            ResidualNatureKind::Potential => {
                residual_nature.ref_type = NATREF_DISCIPLINE_POTENTIAL;
                residual_nature.index = ndx;
                discipline.potential(db)
            }
            _ => None,
        };
        if let Some(nature) = nature {
            residual_units = nature.units(db);
        }
    }
    (name, units, residual_units, is_flow, unknown_nature, residual_nature)
}
