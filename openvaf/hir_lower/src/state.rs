use ahash::AHashMap;
use hir::{CompilationDB, Module, Variable};
use lasso::Rodeo;
use mir::builder::InstBuilder;
use mir::{Function, Value};
use mir_build::{FunctionBuilder, FunctionBuilderContext};

use crate::body::BodyLoweringCtx;
use crate::ctx::LoweringCtx;
use crate::{HiddenStateKey, HirInterner, ParamKind, PlaceKind};

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
            if let ParamKind::HiddenState(HiddenStateKey::Var(var)) = *kind {
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

    /// Replaces the `HiddenState` parameters of the variables selected by `filter`
    /// with the values the variables hold after initialization. In a new entry
    /// block the variables are set to their initializers and then the analog
    /// initial blocks of `module` are lowered.
    ///
    /// Returns the value of each replaced variable after initialization. The values
    /// are passed through optbarriers placed at the end of the initialization so
    /// that they can be kept alive and tracked through optimization.
    pub fn insert_init_state(
        &mut self,
        db: &CompilationDB,
        func: &mut Function,
        literals: &mut Rodeo,
        module: Module,
        filter: impl Fn(Variable) -> bool,
    ) -> AHashMap<Variable, Value> {
        let mut ctx = FunctionBuilderContext::default();
        let (builder, term) = FunctionBuilder::edit(func, literals, &mut ctx, false);
        let mut ctx = LoweringCtx::new(db, builder, true, self);
        let vars: Vec<_> = ctx
            .intern
            .params
            .iter()
            .filter_map(|(kind, &param)| match *kind {
                ParamKind::HiddenState(HiddenStateKey::Var(var))
                    if !ctx.dfg().value_dead(param) =>
                {
                    Some((var, param))
                }
                _ => None,
            })
            .collect();

        // Analog initial blocks start from the initializers. Variables that are
        // not used by the function and are read in analog initial blocks before
        // they are written get a new HiddenState parameter (unknown value).
        for &(var, _) in &vars {
            let val = ctx.lower_expr_body(var.init(db).borrow(), 0);
            ctx.def_place(PlaceKind::Var(var), val);
        }
        let body = module.analog_initial_block(db);
        let path = module.name(db);
        BodyLoweringCtx { ctx: &mut ctx, body: body.borrow(), path: &path }.lower_entry_stmts();

        let mut init = AHashMap::default();
        for (var, param) in vars {
            if !filter(var) {
                continue;
            }
            let place = ctx.dec_place(PlaceKind::Var(var));
            let val = ctx.func.use_var(place);
            ctx.dfg_mut().replace_uses(param, val);
            init.insert(var, ctx.func.ins().optbarrier(val));
        }

        ctx.ensured_sealed();
        ctx.func.func.layout.append_inst_to_bb(term, ctx.current_block());
        init
    }
}
