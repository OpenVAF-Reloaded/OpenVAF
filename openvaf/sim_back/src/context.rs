use ahash::{AHashMap, AHashSet};
use bitset::{BitSet, SparseBitMatrix};
use hir::{CompilationDB, Variable};
use hir_lower::{HirInterner, MirBuilder, ParamKind, PlaceKind};
use lasso::Rodeo;
use mir::builder::InstBuilder;
use mir::cursor::{Cursor, FuncCursor};
use mir::{
    strip_optbarrier, Block, ControlFlowGraph, DominatorTree, Function, Inst, InstructionData,
    Value,
};
use mir_opt::{
    aggressive_dead_code_elimination, aggressive_dead_code_elimination_with_param_edges,
    dead_code_elimination, inst_combine, propagate_direct_taint, propagate_taint, simplify_cfg,
    simplify_cfg_no_phi_merge, sparse_conditional_constant_propagation, GVN,
};
use stdx::packed_option::PackedOption;

use crate::ModuleInfo;

#[cfg(test)]
mod tests;

pub(crate) struct Context<'a> {
    pub(crate) func: Function,
    pub(crate) cfg: ControlFlowGraph,
    pub(crate) dom_tree: DominatorTree,
    pub(crate) intern: HirInterner,
    pub(crate) db: &'a CompilationDB,
    pub(crate) module: &'a ModuleInfo,
    pub(crate) output_values: BitSet<Value>,
    pub(crate) op_dependent_insts: BitSet<Inst>,
    pub(crate) op_dependent_vals: Vec<Value>,
}

#[derive(PartialEq, Eq, Debug)]
pub enum OptimiziationStage {
    Initial,
    PostDerivative,
    Final,
}

impl<'a> Context<'a> {
    pub fn new(db: &'a CompilationDB, literals: &mut Rodeo, module: &'a ModuleInfo) -> Self {
        let (mut func, mut intern) = MirBuilder::new(
            db,
            module.module,
            &|kind| match kind {
                PlaceKind::Contribute { .. }
                | PlaceKind::ImplicitResidual { .. }
                | PlaceKind::CollapseImplicitEquation(_)
                | PlaceKind::IsVoltageSrc(_)
                | PlaceKind::BoundStep
                | PlaceKind::AbsDelayTime(_)
                | PlaceKind::AbsDelayMax(_) => true,
                PlaceKind::Var(var) => module.op_vars.contains_key(&var),
                _ => false,
            },
            &mut module.op_vars.keys().copied(),
        )
        .with_equations()
        .with_tagged_writes()
        .build(literals);
        intern.insert_var_init(db, &mut func, literals, |_| true);

        Context {
            output_values: BitSet::new_empty(func.dfg.num_values()),
            func,
            cfg: ControlFlowGraph::new(),
            dom_tree: DominatorTree::default(),
            intern,
            db,
            module,
            op_dependent_insts: BitSet::new_empty(0),
            op_dependent_vals: Vec::new(),
        }
    }

    /// Find variables whose value must be carried from one evaluation to the next.
    ///
    /// Performs a mock build of the module in which the final value of every variable
    /// is an output. A variable is hidden state if
    /// - it is not constant, i.e. its final value can differ from its initial value, and
    /// - its `HiddenState` parameter still reaches a real output or a side effect
    ///   (the value from the previous evaluation is observable). The value may also
    ///   be observed indirectly in a later evaluation: once the `HiddenState`
    ///   parameter of a modified variable is live, its final value is live, too.
    ///
    /// The constant variables are found optimistically. Initially all variables are
    /// assumed to be constant and their `HiddenState` parameters are replaced by their
    /// initializers. After optimization the variables whose final value is not their
    /// initial value are no longer considered constant. This is repeated until the set
    /// of constant variables does not change. If all variables in the set hold their
    /// initial value on entry, they also hold it on exit, so by induction they hold it
    /// in every evaluation.
    ///
    /// Output variables (op vars) are never hidden state. They start from their
    /// initializer in every evaluation, so they stay in the set of constant variables.
    pub fn detect_hidden_state(
        db: &CompilationDB,
        literals: &mut Rodeo,
        module: &ModuleInfo,
    ) -> Vec<Variable> {
        let is_real_output = |kind: PlaceKind| match kind {
            PlaceKind::Contribute { .. }
            | PlaceKind::ImplicitResidual { .. }
            | PlaceKind::CollapseImplicitEquation(_)
            | PlaceKind::IsVoltageSrc(_)
            | PlaceKind::BoundStep
            | PlaceKind::AbsDelayTime(_)
            | PlaceKind::AbsDelayMax(_) => true,
            PlaceKind::Var(var) => module.op_vars.contains_key(&var),
            _ => false,
        };
        let (probe, probe_intern) = MirBuilder::new(
            db,
            module.module,
            &|kind| is_real_output(kind) || matches!(kind, PlaceKind::Var(_)),
            &mut module.op_vars.keys().copied(),
        )
        .with_equations()
        .build(literals);

        let mut constant: AHashSet<Variable> = probe_intern
            .params
            .iter()
            .filter_map(|(kind, _)| match *kind {
                ParamKind::HiddenState(var) => Some(var),
                _ => None,
            })
            .collect();

        let (mut func, intern, mut cfg, dom_tree, mut output_values) = loop {
            let mut func = probe.clone();
            let mut intern = probe_intern.clone();
            let init =
                intern.insert_var_init(db, &mut func, literals, |var| constant.contains(&var));

            // Optimization replaces values. To find the optimized initial values
            // they are passed through optbarriers that are kept alive.
            let entry = func.layout.entry_block().unwrap();
            let mut cursor = FuncCursor::new(&mut func).at_last_inst(entry);
            let init: Vec<_> =
                init.into_iter().map(|(var, val)| (var, cursor.ins().optbarrier(val))).collect();

            // Simplify with the final and the initial values of all variables kept alive
            let mut output_values = BitSet::new_empty(func.dfg.num_values() + 1);
            output_values.extend(intern.outputs.values().copied().filter_map(PackedOption::expand));
            output_values.extend(init.iter().map(|&(_, val)| val));
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(&func);
            dead_code_elimination(&mut func, &output_values);
            sparse_conditional_constant_propagation(&mut func, &cfg);
            inst_combine(&mut func);
            simplify_cfg(&mut func, &mut cfg);
            let mut dom_tree = DominatorTree::default();
            dom_tree.compute(&func, &cfg, true, true, false);
            let mut gvn = GVN::default();
            gvn.init(&func, &dom_tree, intern.params.len() as u32);
            gvn.solve(&mut func);
            gvn.remove_unnecessary_insts(&mut func, &dom_tree);

            // Variables whose final value differs from their initial value are not constant.
            // Output variables always start from their initializer and stay constant.
            let mut changed = false;
            for (var, init_val) in init {
                if module.op_vars.contains_key(&var) {
                    continue;
                }
                let Some(out) = intern.outputs.get(&PlaceKind::Var(var)).and_then(|v| v.expand())
                else {
                    continue;
                };
                if strip_optbarrier(&func, out) != strip_optbarrier(&func, init_val) {
                    constant.remove(&var);
                    changed = true;
                }
            }
            if !changed {
                break (func, intern, cfg, dom_tree, output_values);
            }
        };

        // Variables that are not constant and whose final value differs from their
        // value on entry, with their HiddenState parameter and their final value (output)
        let modified: Vec<_> = intern
            .params
            .iter()
            .filter_map(|(kind, &param)| {
                let ParamKind::HiddenState(var) = *kind else { return None };
                if constant.contains(&var) {
                    return None;
                }
                let out = intern.outputs.get(&PlaceKind::Var(var))?.expand()?;
                (strip_optbarrier(&func, out) != param).then_some((var, param, out))
            })
            .collect();

        // The final value of a modified variable is the value of its
        // HiddenState parameter in the next evaluation
        let next_eval: AHashMap<Value, Value> =
            modified.iter().map(|&(_, param, out)| (param, out)).collect();

        // Keep only the real outputs and side effects alive
        output_values.clear();
        for (&kind, val) in intern.outputs.iter() {
            if is_real_output(kind) {
                if let Some(val) = val.expand() {
                    output_values.insert(val);
                }
            }
        }
        let mut control_dep = SparseBitMatrix::new_square(0);
        dom_tree.compute_postdom_frontiers(&cfg, &mut control_dep);
        aggressive_dead_code_elimination_with_param_edges(
            &mut func,
            &mut cfg,
            &|val, _| output_values.contains(val),
            &|param| next_eval.get(&param).copied(),
            &control_dep,
        );

        modified
            .into_iter()
            .filter_map(|(var, param, _)| (!func.dfg.value_dead(param)).then_some(var))
            .collect()
    }

    pub fn optimize(&mut self, stage: OptimiziationStage) -> GVN {
        if stage == OptimiziationStage::Initial {
            dead_code_elimination(&mut self.func, &self.output_values);
        }
        sparse_conditional_constant_propagation(&mut self.func, &self.cfg);
        inst_combine(&mut self.func);
        if stage == OptimiziationStage::Final {
            simplify_cfg(&mut self.func, &mut self.cfg);
        } else {
            simplify_cfg_no_phi_merge(&mut self.func, &mut self.cfg);
        }
        self.compute_domtree(true, true, false);

        let mut gvn = GVN::default();
        gvn.init(&self.func, &self.dom_tree, self.intern.params.len() as u32);
        gvn.solve(&mut self.func);
        gvn.remove_unnecessary_insts(&mut self.func, &self.dom_tree);

        if stage == OptimiziationStage::Final {
            let mut control_dep = SparseBitMatrix::new_square(0);
            self.dom_tree.compute_postdom_frontiers(&self.cfg, &mut control_dep);
            aggressive_dead_code_elimination(
                &mut self.func,
                &mut self.cfg,
                &|val, _| self.output_values.contains(val),
                &control_dep,
            );
            simplify_cfg(&mut self.func, &mut self.cfg);
        }

        gvn
    }

    pub fn compute_cfg(&mut self) {
        self.cfg.compute(&self.func);
    }

    pub fn compute_domtree(&mut self, dom: bool, pdom: bool, postorder: bool) {
        self.dom_tree.compute(&self.func, &self.cfg, dom, pdom, postorder);
    }

    pub fn compute_outputs(&mut self, contributes: bool) {
        self.output_values.clear();
        self.output_values.ensure(self.func.dfg.num_values() + 1);
        if contributes {
            self.output_values
                .extend(self.intern.outputs.values().copied().filter_map(PackedOption::expand));
        } else {
            for (kind, val) in self.intern.outputs.iter() {
                if matches!(kind, PlaceKind::Var(var) if self.module.op_vars.contains_key(var))
                    || matches!(
                        kind,
                        PlaceKind::CollapseImplicitEquation(_)
                            | PlaceKind::BoundStep
                            | PlaceKind::AbsDelayTime(_)
                            | PlaceKind::AbsDelayMax(_)
                    )
                {
                    self.output_values.insert(val.unwrap_unchecked());
                }
            }
        }
    }

    pub fn init_op_dependent_insts(&mut self, dom_frontiers: &mut SparseBitMatrix<Block, Block>) {
        self.dom_tree.compute_dom_frontiers(&self.cfg, dom_frontiers);
        let dfg = &mut self.func.dfg;
        self.op_dependent_insts.ensure(dfg.num_insts());

        for (cb, uses) in self.intern.callback_uses.iter_mut_enumerated() {
            if self.intern.callbacks[cb].is_noise() {
                uses.retain(|&inst| {
                    if self.func.layout.inst_block(inst).is_none() {
                        return false;
                    }
                    self.op_dependent_insts.insert(inst);
                    for &result in dfg.inst_results(inst) {
                        self.op_dependent_vals.push(result);
                    }
                    true
                })
            }
        }
        for (param, &val) in self.intern.params.iter() {
            if !dfg.value_dead(val) && param.op_dependent() {
                self.op_dependent_vals.push(val)
            }
        }

        // Propagate taint
        propagate_direct_taint(
            &self.func,
            dom_frontiers,
            self.op_dependent_vals.iter().copied(),
            &mut self.op_dependent_insts,
        );
    }

    pub fn refresh_op_dependent_insts(&mut self) {
        let dfg = &mut self.func.dfg;
        self.op_dependent_vals.clear();
        self.op_dependent_insts.clear();
        self.op_dependent_insts.ensure(dfg.num_insts());
        // Go through all callbacks and their uses
        for (cb, uses) in self.intern.callback_uses.iter_mut_enumerated() {
            // Ff callback is op dependent
            if self.intern.callbacks[cb].op_dependent() {
                // Remove uses that appear in instructions that are not inserted into the layout.
                // Add to op dependent instructions.
                // Add the results of these instructions to op dependent values.
                uses.retain(|&inst| {
                    if self.func.layout.inst_block(inst).is_none() {
                        return false;
                    }
                    self.op_dependent_insts.insert(inst);
                    for &result in dfg.inst_results(inst) {
                        self.op_dependent_vals.push(result);
                    }
                    true
                })
            }
        }
        // Go through parameters, if the corresponding value is not dead and is op dependent
        // (i.e. current, voltage, abstime, ...) add it to op dependent values.
        for (param, &val) in self.intern.params.iter() {
            if !dfg.value_dead(val) && param.op_dependent() {
                self.op_dependent_vals.push(val)
            }
        }

        // Propagate taint
        propagate_taint(
            &self.func,
            &self.dom_tree,
            &self.cfg,
            self.op_dependent_vals.iter().copied(),
            &mut self.op_dependent_insts,
        );
    }
}
