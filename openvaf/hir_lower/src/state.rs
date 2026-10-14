use ahash::AHashMap;
use hir::{CompilationDB, Variable};
use lasso::Rodeo;
use mir::{Function, Value};
use mir_build::{FunctionBuilder, FunctionBuilderContext};

use crate::ctx::LoweringCtx;
use crate::{HirInterner, ParamKind};

impl HirInterner {
    /// Replaces the `HiddenState` parameters of the variables selected by `filter`
    /// with the variable initializers, which are lowered in a new entry block.
    /// Returns the initial value of each replaced variable.
    pub fn insert_var_init(
        &mut self,
        db: &CompilationDB,
        func: &mut Function,
        literals: &mut Rodeo,
        filter: impl Fn(Variable) -> bool,
    ) -> AHashMap<Variable, Value> {
        let mut ctx = FunctionBuilderContext::default();
        let (builder, term) = FunctionBuilder::edit(func, literals, &mut ctx, false);
        let mut ctx = LoweringCtx::new(db, builder, true, self);
        let mut init = AHashMap::default();
        for (kind, param) in ctx.intern.params.clone().iter() {
            if let ParamKind::HiddenState(var) = *kind {
                if !filter(var) || ctx.dfg().value_dead(*param) {
                    continue;
                }
                let val = ctx.lower_expr_body(var.init(db).borrow(), 0);
                ctx.dfg_mut().replace_uses(*param, val);
                init.insert(var, val);
            }
        }

        ctx.ensured_sealed();
        ctx.func.func.layout.append_inst_to_bb(term, ctx.current_block());
        init
    }
}
