//! Constness of the Jacobian entries in the final eval function
//!
//! Reuses the taint solver of the init split ([`propagate_taint`]) without
//! modifying it. The seeds are given by an allow-list: every parameter and
//! every callback result that is not explicitly allowed taints, so new kinds
//! of parameters and callbacks are non-constant by default.
//! - CONST: allowed are model/instance parameters, their given flags, instance
//!   system parameters (`$mfactor`, ...), temperature, port connection flags,
//!   and MIR constants. Values cached by the instance setup are eval parameters
//!   that are not in the interner, so they are never seeds.
//! - OPTIME: additionally allows the results of `analysis()` and `$simparam`.

use ahash::AHashSet;
use bitset::BitSet;
use hir_lower::{CallBackKind, ParamKind};
use mir::{strip_optbarrier, Function, Inst, Value, ValueDef};
use mir_opt::propagate_taint;
use typed_index_collections::TiVec;

use crate::context::Context;
use crate::dae::{DaeSystem, MatrixEntryId};

/// Constness of the resistive and the reactive part of a Jacobian entry
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct JacobianConstness {
    /// Depends only on parameters, temperature, and constants
    pub resist_const: bool,
    pub react_const: bool,
    /// Additionally may depend on the analysis and on simulator parameters
    pub resist_optime_const: bool,
    pub react_optime_const: bool,
}

/// Parameters that do not taint
fn is_allowed_param(kind: &ParamKind) -> bool {
    matches!(
        kind,
        ParamKind::Param(_)
            | ParamKind::ParamGiven { .. }
            | ParamKind::ParamSysFun(_)
            | ParamKind::Temperature
            | ParamKind::PortConnected { .. }
    )
}

/// Callbacks whose results do not taint OPTIME constness
fn is_optime_allowed_callback(cb: &CallBackKind) -> bool {
    matches!(
        cb,
        CallBackKind::Analysis
            | CallBackKind::SimParam
            | CallBackKind::SimParamOpt
            | CallBackKind::SimParamStr
    )
}

struct Taint {
    seeds: AHashSet<Value>,
    insts: BitSet<Inst>,
}

impl Taint {
    fn new(cx: &Context, callback_allowed: impl Fn(&CallBackKind) -> bool) -> Taint {
        let func = &cx.func;
        let mut seeds = AHashSet::new();
        for (kind, &val) in cx.intern.params.iter() {
            if !func.dfg.value_dead(val) && !is_allowed_param(kind) {
                seeds.insert(val);
            }
        }
        for (cb, uses) in cx.intern.callback_uses.iter_enumerated() {
            if !callback_allowed(&cx.intern.callbacks[cb]) {
                for &inst in uses {
                    // skip instructions removed from the function
                    if func.layout.inst_block(inst).is_some() {
                        seeds.extend(func.dfg.inst_results(inst).iter().copied());
                    }
                }
            }
        }

        let mut insts = BitSet::new_empty(func.dfg.num_insts());
        propagate_taint(func, &cx.dom_tree, &cx.cfg, seeds.iter().copied(), &mut insts);
        Taint { seeds, insts }
    }

    fn val_tainted(&self, func: &Function, val: Value) -> bool {
        if self.seeds.contains(&val) {
            return true;
        }
        match func.dfg.value_def(val) {
            ValueDef::Result(inst, _) => self.insts.contains(inst),
            _ => false,
        }
    }

    /// `propagate_taint` marks the users of the seeds, the seeds themselves
    /// are checked separately. Both the output value and the value behind its
    /// optbarriers are checked.
    fn tainted(&self, func: &Function, val: Value) -> bool {
        self.val_tainted(func, val) || self.val_tainted(func, strip_optbarrier(func, val))
    }
}

/// Computes the constness of all Jacobian entries. Must be called on the final
/// eval function. Recomputes the CFG and the dominator tree of `cx.func`.
pub(crate) fn jacobian_constness(
    cx: &mut Context,
    dae_system: &DaeSystem,
) -> TiVec<MatrixEntryId, JacobianConstness> {
    cx.compute_cfg();
    cx.compute_domtree(true, true, false);

    let strict = Taint::new(cx, |_| false);
    let optime = Taint::new(cx, is_optime_allowed_callback);

    let func = &cx.func;
    dae_system
        .jacobian
        .iter()
        .map(|entry| {
            let res = JacobianConstness {
                resist_const: !strict.tainted(func, entry.resist),
                react_const: !strict.tainted(func, entry.react),
                resist_optime_const: !optime.tainted(func, entry.resist),
                react_optime_const: !optime.tainted(func, entry.react),
            };
            debug_assert!(!res.resist_const || res.resist_optime_const);
            debug_assert!(!res.react_const || res.react_optime_const);
            res
        })
        .collect()
}
