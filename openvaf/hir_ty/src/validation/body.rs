use std::mem::replace;

use ahash::{HashMap, HashSet};
use hir_def::body::Body;
use hir_def::{
    BranchId, BuiltIn, DefWithBodyId, DisciplineId, Expr, ExprId, FunctionArgLoc, FunctionId,
    Literal, Lookup, NatureId, NodeId, ParamId, Path, Stmt, StmtId, VarId,
};
use stdx::impl_display;
use syntax::ast::AssignOp;
use syntax::name::{AsIdent, Name};

use crate::builtin::{
    ABSDELAY_MAX, ARANDOM_CONST_SEED, ARANDOM_NO_SEED, ARANDOM_SEED, ARANDOM_TYPED, DDT_TOL,
    IDT_IC_ASSERT_TOL, NATURE_ACCESS_BRANCH, NATURE_ACCESS_NODES, NATURE_ACCESS_NODE_GND,
    NATURE_ACCESS_PORT_FLOW, NOISE_TABLE_INLINE, NOISE_TABLE_INLINE_NAME, RANDOM_NO_SEED,
    RANDOM_SEED, RDIST_1_ARG_CONST_SEED, RDIST_1_ARG_SEED, RDIST_1_ARG_TYPED,
    RDIST_2_ARG_CONST_SEED, RDIST_2_ARG_SEED, RDIST_2_ARG_TYPED, RDIST_NORMAL_CONST_SEED,
    RDIST_NORMAL_SEED, RDIST_NORMAL_TYPED, RDIST_UNIFORM_CONST_SEED, RDIST_UNIFORM_SEED,
    RDIST_UNIFORM_TYPED, TRANSITION_DELAY_RISET_FALLT_TOL,
};
use crate::db::HirTyDB;
use crate::inference::{BranchWrite, InferenceResult, ResolvedFun};
use crate::lower::BranchKind;
use crate::types::{Signature, Ty};

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum IllegalCtxAccessKind {
    NatureAccess,
    AnalogOperator { name: Name, is_standard: bool, non_const_dominator: Box<[ExprId]> },
    AnalysisFun { name: Name },
    Builtin { name: Name },
    Var(VarId),
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct IllegalCtxAccess {
    pub kind: IllegalCtxAccessKind,
    pub ctx: BodyCtx,
    pub expr: ExprId,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum BodyValidationDiagnostic {
    ExpectedPort {
        expr: ExprId,
        node: NodeId,
    },
    TrivialBranchAccess {
        branch: BranchWrite,
        expr: ExprId,
        stmt: StmtId,
    },
    PotentialOfPortFlow {
        expr: ExprId,
        branch: Option<BranchId>,
    },
    IllegalContribute {
        stmt: StmtId,
        ctx: BodyCtx,
    },
    IllegalEventControl {
        stmt: StmtId,
        ctx: BodyCtx,
    },

    WriteToInputArg {
        expr: ExprId,
        arg: FunctionArgLoc,
    },

    IllegalParamAccess {
        def: ParamId,
        expr: ExprId,
        param: ParamId,
    },

    IllegalCtxAccess(IllegalCtxAccess),

    ConstSimparam {
        known: bool,
        expr: ExprId,
        stmt: StmtId,
    },

    UnsupportedFunction {
        expr: ExprId,
        func: BuiltIn,
    },

    IncompatibleNatureAccess {
        candidates: [Option<(Name, Name)>; 2],
        access_nature: Option<NatureId>,
        access_expr: ExprId,
        branch: String,
    },

    IllegalNatureAccess {
        is_pot: bool,
        access_expr: ExprId,
    },

    IncompatibleImplicitBranch {
        access: ExprId,
        node1: NodeId,
        node2: NodeId,
    },

    /// Illegal `$random`/`$arandom` call. If `fun` is set, `expr` is a call of
    /// that function, which (possibly indirectly) contains the illegal call.
    IllegalRandom {
        expr: ExprId,
        kind: IllegalRandomKind,
        fun: Option<FunctionId>,
    },
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum IllegalRandomKind {
    /// Untyped forms need hidden state (`-s`)
    RequiresFullSemantics,
    /// Untyped forms are not allowed in analog initial blocks
    AnalogInitial,
    /// Only `$arandom` and `$rdist_*` with a constant seed are allowed in
    /// parameter initializers
    ParamInit,
    /// Only a constant seed is allowed in variable initializers
    VarInit,
    /// The seed is neither an integer variable nor a constant expression
    NonConstSeed,
    /// The type string is not "global" or "instance"
    InvalidType,
}

/// Signature of a call whose signature inference does not record (builtins with a
/// single signature), the same as `BodyRef::get_call_signature` returns
const NO_SIGNATURE: Signature = Signature(u32::MAX);

/// Form of a `$random`/`$arandom`/`$dist_*`/`$rdist_*` call
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum RandomForm {
    /// `$random()`, `$arandom()`
    NoSeed,
    /// `$random(var)`, `$arandom(var)`, `$dist_*(var, ...)`, `$rdist_*(var, ...)`
    VarSeed,
    /// `$arandom(constant)`, `$rdist_*(constant, ...)`
    ConstSeed,
    /// `$arandom(seed, type)`, `$rdist_*(seed, ..., type)`
    Typed,
}

impl RandomForm {
    /// `signature` is ignored for builtins with a single signature (inference does
    /// not record it for them)
    pub fn new(call: BuiltIn, signature: Signature) -> Option<RandomForm> {
        let form = match (call, signature) {
            (BuiltIn::random, RANDOM_NO_SEED) | (BuiltIn::arandom, ARANDOM_NO_SEED) => {
                RandomForm::NoSeed
            }
            (BuiltIn::random, RANDOM_SEED)
            | (BuiltIn::arandom, ARANDOM_SEED)
            | (
                BuiltIn::dist_uniform
                | BuiltIn::dist_normal
                | BuiltIn::dist_exponential
                | BuiltIn::dist_poisson
                | BuiltIn::dist_chi_square
                | BuiltIn::dist_t
                | BuiltIn::dist_erlang,
                _,
            ) => RandomForm::VarSeed,
            (BuiltIn::rdist_uniform, RDIST_UNIFORM_SEED)
            | (BuiltIn::rdist_normal, RDIST_NORMAL_SEED)
            | (
                BuiltIn::rdist_exponential
                | BuiltIn::rdist_poisson
                | BuiltIn::rdist_chi_square
                | BuiltIn::rdist_t,
                RDIST_1_ARG_SEED,
            )
            | (BuiltIn::rdist_erlang, RDIST_2_ARG_SEED) => RandomForm::VarSeed,
            (BuiltIn::arandom, ARANDOM_CONST_SEED)
            | (BuiltIn::rdist_uniform, RDIST_UNIFORM_CONST_SEED)
            | (BuiltIn::rdist_normal, RDIST_NORMAL_CONST_SEED)
            | (
                BuiltIn::rdist_exponential
                | BuiltIn::rdist_poisson
                | BuiltIn::rdist_chi_square
                | BuiltIn::rdist_t,
                RDIST_1_ARG_CONST_SEED,
            )
            | (BuiltIn::rdist_erlang, RDIST_2_ARG_CONST_SEED) => RandomForm::ConstSeed,
            (BuiltIn::arandom, ARANDOM_TYPED)
            | (BuiltIn::rdist_uniform, RDIST_UNIFORM_TYPED)
            | (BuiltIn::rdist_normal, RDIST_NORMAL_TYPED)
            | (
                BuiltIn::rdist_exponential
                | BuiltIn::rdist_poisson
                | BuiltIn::rdist_chi_square
                | BuiltIn::rdist_t,
                RDIST_1_ARG_TYPED,
            )
            | (BuiltIn::rdist_erlang, RDIST_2_ARG_TYPED) => RandomForm::Typed,
            _ => return None,
        };
        Some(form)
    }
}

impl BodyValidationDiagnostic {
    pub fn collect(db: &dyn HirTyDB, def: DefWithBodyId) -> Vec<BodyValidationDiagnostic> {
        let body = db.body(def);
        let infere = db.inference_result(def);

        let ctx = match def {
            DefWithBodyId::ModuleId { initial: false, .. } => BodyCtx::AnalogBlock,
            DefWithBodyId::ModuleId { initial: true, .. } => BodyCtx::AnalogInitialBlock,
            DefWithBodyId::FunctionId(_) => BodyCtx::Function,
            _ => BodyCtx::Const,
        };

        let mut validator = BodyValidator {
            db,
            owner: def,
            body: &body,
            infer: &infere,
            diagnostics: Vec::new(),
            ctx,
            non_const_dominator: Box::default(),
            non_trivial_branches: HashSet::default(),
            trivial_probes: HashMap::default(),
        };

        for stmt in &*body.entry_stmts {
            validator.validate_stmt(*stmt)
        }

        for (branch, exprs) in validator.trivial_probes {
            for (stmt, expr) in exprs {
                validator.diagnostics.push(BodyValidationDiagnostic::TrivialBranchAccess {
                    branch,
                    expr,
                    stmt,
                })
            }
        }

        validator.diagnostics
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum BodyCtx {
    AnalogBlock,
    AnalogInitialBlock,
    Conditional,
    EventControl,
    Function,
    ConstOrAnalysis,
    Const,
}

impl BodyCtx {
    fn allow_nature_access(self) -> bool {
        matches!(self, Self::AnalogBlock | Self::Conditional | Self::EventControl)
    }

    fn allow_contribute(self) -> bool {
        matches!(self, Self::AnalogBlock | Self::Conditional)
    }

    fn allow_analog_operator(self) -> bool {
        matches!(self, Self::AnalogBlock)
    }

    fn allow_analysis_fun(self) -> bool {
        !matches!(self, Self::Const)
    }

    /// `$stop`, `$abstime`, `analysis()` and `$discontinuity` require a running analysis
    fn allow_analysis_state(self) -> bool {
        !matches!(self, Self::AnalogInitialBlock)
    }

    fn allow_var_ref(self) -> bool {
        !matches!(self, Self::Const | Self::ConstOrAnalysis)
    }
}

impl_display! {
    match BodyCtx{
       BodyCtx::AnalogBlock => "analog block";
       BodyCtx::AnalogInitialBlock => "analog initial block";
       BodyCtx::Conditional => "conditions";
       BodyCtx::EventControl => "events";
       BodyCtx::Function => "analog functions";
       BodyCtx::ConstOrAnalysis => "constant or analysis";
       BodyCtx::Const => "constants";
    }
}

struct BodyValidator<'a> {
    db: &'a dyn HirTyDB,
    owner: DefWithBodyId,
    body: &'a Body,
    infer: &'a InferenceResult,
    diagnostics: Vec<BodyValidationDiagnostic>,
    ctx: BodyCtx,
    non_const_dominator: Box<[ExprId]>,
    non_trivial_branches: HashSet<BranchWrite>,
    trivial_probes: HashMap<BranchWrite, Vec<(StmtId, ExprId)>>,
}

impl BodyValidator<'_> {
    fn validate_stmt(&mut self, stmt: StmtId) {
        let cond = match self.body.stmts[stmt] {
            Stmt::Assignment { dst, val, assignment_kind } => {
                self.validate_expr(val, stmt);

                if assignment_kind == AssignOp::Contribute && !self.ctx.allow_contribute() {
                    self.diagnostics
                        .push(BodyValidationDiagnostic::IllegalContribute { stmt, ctx: self.ctx })
                }
                // avoid duplicate errors
                else if self.infer.assignment_destination.contains_key(&stmt) {
                    self.validate_assignment_dst(dst, stmt);
                }

                return;
            }
            Stmt::EventControl { body, .. } => {
                // keep the analog initial context so that its body is still checked
                if self.ctx == BodyCtx::AnalogInitialBlock {
                    self.diagnostics.push(BodyValidationDiagnostic::IllegalEventControl {
                        stmt,
                        ctx: self.ctx,
                    });
                    self.validate_stmt(body);
                    return;
                }
                let old = replace(&mut self.ctx, BodyCtx::EventControl);
                self.validate_stmt(body);
                self.ctx = old;
                return;
            }
            Stmt::Block { ref body } => {
                body.iter().for_each(|stmt| self.validate_stmt(*stmt));
                return;
            }

            Stmt::Missing | Stmt::Empty => return,

            Stmt::Expr(e) => {
                self.validate_expr(e, stmt);
                return;
            }

            Stmt::If { cond, .. }
            | Stmt::ForLoop { cond, .. }
            | Stmt::WhileLoop { cond, .. }
            | Stmt::Case { discr: cond, .. } => cond,
        };

        self.validate_condition(cond, stmt, |s| {
            s.body.stmts[stmt].walk_child_stmts(|stmt| s.validate_stmt(stmt))
        });
    }

    fn validate_condition(
        &mut self,
        cond: ExprId,
        stmt: StmtId,
        f: impl FnOnce(&mut Self),
    ) -> Option<Box<[ExprId]>> {
        if self.ctx == BodyCtx::AnalogBlock || self.ctx == BodyCtx::Conditional {
            let mut non_const_access = Vec::new();
            ExprValidator {
                parent: self,
                cond_diagnostic_sink: Some(&mut non_const_access),
                write: false,
                stmt,
            }
            .validate_expr(cond);

            if !non_const_access.is_empty() {
                let non_const_dominator =
                    replace(&mut self.non_const_dominator, non_const_access.into_boxed_slice());
                let ctx = replace(&mut self.ctx, BodyCtx::Conditional);
                f(self);
                self.ctx = ctx;
                return Some(replace(&mut self.non_const_dominator, non_const_dominator));
            }
        } else {
            self.validate_expr(cond, stmt);
        }

        f(self);
        None
    }

    fn validate_expr(&mut self, expr: ExprId, stmt: StmtId) {
        ExprValidator { parent: self, cond_diagnostic_sink: None, write: false, stmt }
            .validate_expr(expr)
    }

    fn validate_assignment_dst(&mut self, expr: ExprId, stmt: StmtId) {
        ExprValidator { parent: self, cond_diagnostic_sink: None, write: true, stmt }
            .validate_expr(expr)
    }
}

struct ExprValidator<'a, 'b> {
    parent: &'a mut BodyValidator<'b>,
    cond_diagnostic_sink: Option<&'a mut Vec<ExprId>>,
    write: bool,
    stmt: StmtId,
}

impl ExprValidator<'_, '_> {
    fn report_illegal_access(&mut self, kind: IllegalCtxAccessKind, expr: ExprId) {
        let err = IllegalCtxAccess { kind, ctx: self.parent.ctx, expr };
        self.report(BodyValidationDiagnostic::IllegalCtxAccess(err));
    }

    fn check_access(
        &mut self,
        kind: impl FnOnce(&Self) -> IllegalCtxAccessKind,
        expr: ExprId,
        allowed: bool,
    ) {
        if let Some(sink) = &mut self.cond_diagnostic_sink {
            sink.push(expr)
        }

        if !allowed {
            self.report_illegal_access(kind(self), expr)
        }
    }

    fn report(&mut self, diagnostic: BodyValidationDiagnostic) {
        self.parent.diagnostics.push(diagnostic)
    }

    fn report_illegal_nature_access(
        &mut self,
        branch: String,
        discipline: DisciplineId,
        access_nature: Option<NatureId>,
        access_expr: ExprId,
    ) {
        let db = self.parent.db;
        let discipline = db.discipline_info(discipline);

        let nature_info = |nature: NatureId| {
            let nature = nature.lookup(db.upcast());
            let nature = &nature.item_tree(db.upcast())[nature.id];
            Some((nature.name.clone(), nature.access.clone()?.0))
        };
        let pot = discipline.potential.and_then(nature_info);
        let flow = discipline.flow.and_then(nature_info);
        self.parent.diagnostics.push(BodyValidationDiagnostic::IncompatibleNatureAccess {
            candidates: [pot, flow],
            access_nature,
            access_expr,
            branch,
        })
    }

    fn validate_implicit_branch(
        &mut self,
        expr: ExprId,
        node1: NodeId,
        node2: NodeId,
    ) -> Option<DisciplineId> {
        if let Some(discipline1) = self.parent.db.node_discipline(node1) {
            if let Some(discipline2) = self.parent.db.node_discipline(node2) {
                let discipline2 = self.parent.db.discipline_info(discipline2);
                if !discipline2.compatible(discipline1, self.parent.db) {
                    self.report(BodyValidationDiagnostic::IncompatibleImplicitBranch {
                        access: expr,
                        node1,
                        node2,
                    });
                } else {
                    return Some(discipline1);
                }
            }
        }

        None
    }

    fn lint_trivial_branch(&mut self, branch: BranchWrite, call: BuiltIn, expr: ExprId) {
        let is_flow = call == BuiltIn::flow;
        if self.write {
            self.parent.non_trivial_branches.insert(branch);
            self.parent.trivial_probes.remove(&branch);
        } else if is_flow && !self.parent.non_trivial_branches.contains(&branch) {
            self.parent.trivial_probes.entry(branch).or_default().push((self.stmt, expr))
        }
    }

    fn validate_flow_or_pot(&mut self, expr: ExprId, call: BuiltIn, discipline: DisciplineId) {
        let is_pot = call == BuiltIn::potential;
        let discipline_ = self.parent.db.discipline_info(discipline);
        if discipline_.potential.is_none() && is_pot || discipline_.flow.is_none() && !is_pot {
            self.report(BodyValidationDiagnostic::IllegalNatureAccess { is_pot, access_expr: expr })
        }
    }

    fn validate_nature_access(
        &mut self,
        access_nature: NatureId,
        access_expr: ExprId,
        args: &[ExprId],
    ) {
        match self.parent.infer.resolved_signatures.get(&access_expr).copied() {
            Some(NATURE_ACCESS_BRANCH) => {
                let branch = self.parent.infer.expr_types[args[0]].unwrap_branch();
                if let Some(branch_info) = self.parent.db.branch_info(branch) {
                    self.report_illegal_nature_access(
                        self.parent.db.branch_data(branch).name.to_string(),
                        branch_info.discipline,
                        Some(access_nature),
                        access_expr,
                    )
                }
            }

            Some(NATURE_ACCESS_NODE_GND) => {
                let node = self.parent.infer.expr_types[args[0]].unwrap_node();
                if let Some(discipline) = self.parent.db.node_discipline(node) {
                    let node = self.parent.db.node_data(node);
                    self.report_illegal_nature_access(
                        format!("({})", node.name),
                        discipline,
                        Some(access_nature),
                        access_expr,
                    )
                }
            }

            Some(NATURE_ACCESS_NODES) => {
                let node1 = self.parent.infer.expr_types[args[0]].unwrap_node();
                let node2 = self.parent.infer.expr_types[args[0]].unwrap_node();
                if let Some(discipline1) = self.parent.db.node_discipline(node1) {
                    if let Some(discipline2) = self.parent.db.node_discipline(node2) {
                        let discipline2 = self.parent.db.discipline_info(discipline2);
                        if discipline2.compatible(discipline1, self.parent.db) {
                            let node1 = self.parent.db.node_data(node1);
                            let node2 = self.parent.db.node_data(node2);
                            self.report_illegal_nature_access(
                                format!("({}, {})", node1.name, node2.name),
                                discipline1,
                                Some(access_nature),
                                access_expr,
                            )
                        } else {
                            self.report(BodyValidationDiagnostic::IncompatibleImplicitBranch {
                                access: access_expr,
                                node1,
                                node2,
                            })
                        }
                    }
                }
            }

            Some(NATURE_ACCESS_PORT_FLOW) => {
                let node = self.parent.infer.expr_types[args[0]].unwrap_port_flow();
                if let Some(discipline) = self.parent.db.node_discipline(node) {
                    let node = self.parent.db.node_data(node);
                    self.report_illegal_nature_access(
                        format!("(<{}>)", node.name),
                        discipline,
                        Some(access_nature),
                        access_expr,
                    )
                }
            }
            Some(_) => unreachable!(),
            None => (),
        };
    }

    fn validate_expr(&mut self, expr: ExprId) {
        match self.parent.body.exprs[expr] {
            Expr::Call { ref fun, ref args, .. } => {
                match self.parent.infer.resolved_calls.get(&expr) {
                    Some(ResolvedFun::BuiltIn(builtin)) => {
                        let signature = self.parent.infer.resolved_signatures.get(&expr);
                        self.validate_builtin(fun, expr, args, *builtin, signature.cloned());
                        return;
                    }
                    Some(ResolvedFun::InvalidNatureAccess(nature)) => {
                        self.validate_nature_access(*nature, expr, args);
                        return;
                    }
                    Some(&ResolvedFun::User { func, .. }) => self.validate_user_call(expr, func),
                    _ => (),
                }
            }

            Expr::Select { cond, then_val, else_val } => {
                if let Some(non_const_dominators) =
                    self.parent.validate_condition(cond, self.stmt, |s| {
                        let mut validator = ExprValidator {
                            parent: s,
                            cond_diagnostic_sink: self.cond_diagnostic_sink.as_deref_mut(),
                            write: false,
                            stmt: self.stmt,
                        };
                        validator.validate_expr(then_val);
                        validator.validate_expr(else_val);
                    })
                {
                    if let Some(sink) = &mut self.cond_diagnostic_sink {
                        sink.extend(non_const_dominators.to_vec())
                    }
                }
            }

            Expr::Path { port: false, .. } => {
                match self.parent.infer.expr_types[expr] {
                    Ty::FunctionVar { arg: Some(arg), fun, .. } => {
                        let is_output = self.parent.db.function_data(fun).args[arg].is_output;
                        if self.write && !is_output {
                            self.report(BodyValidationDiagnostic::WriteToInputArg {
                                expr,
                                arg: FunctionArgLoc { fun, id: arg },
                            })
                        }
                    }

                    Ty::Var(_, var) => {
                        self.check_access(
                            |__| IllegalCtxAccessKind::Var(var),
                            expr,
                            self.parent.ctx.allow_var_ref(),
                        );
                    }
                    Ty::Param(_, param) => {
                        if let DefWithBodyId::ParamId(def) = self.parent.owner {
                            if def.lookup(self.parent.db.upcast()).id
                                < param.lookup(self.parent.db.upcast()).id
                            {
                                self.report(BodyValidationDiagnostic::IllegalParamAccess {
                                    def,
                                    expr,
                                    param,
                                })
                            }
                        }
                    }
                    _ => (),
                };
                return;
            }

            _ => (),
        }

        self.parent.body.exprs[expr].walk_child_exprs(|child| self.validate_expr(child))
    }

    /// Checks a `$random`/`$arandom`/`$dist_*`/`$rdist_*` call. Typed calls
    /// (`$arandom(seed, type)`) are allowed everywhere. Untyped calls need full
    /// Verilog-A semantics and are not allowed in analog initial blocks. In
    /// initializers only a constant seed is allowed (only `$arandom` and
    /// `$rdist_*`).
    fn validate_random(
        &mut self,
        expr: ExprId,
        args: &[ExprId],
        call: BuiltIn,
        signature: Option<Signature>,
    ) {
        let signature = signature.unwrap_or(NO_SIGNATURE);
        let Some(form) = RandomForm::new(call, signature) else { return };
        let kind = match form {
            RandomForm::Typed => {
                let valid = matches!(
                    &self.parent.body.exprs[*args.last().unwrap()],
                    Expr::Literal(Literal::String(ty)) if matches!(&**ty, "global" | "instance")
                );
                if valid {
                    return;
                }
                IllegalRandomKind::InvalidType
            }
            _ if !self.parent.db.full_semantics() => IllegalRandomKind::RequiresFullSemantics,
            _ => {
                let init_kind = match self.parent.owner {
                    DefWithBodyId::ModuleId { initial: true, .. } => {
                        Some(IllegalRandomKind::AnalogInitial)
                    }
                    DefWithBodyId::VarId(_) => Some(IllegalRandomKind::VarInit),
                    DefWithBodyId::ModuleId { initial: false, .. }
                    | DefWithBodyId::FunctionId(_) => None,
                    _ => Some(IllegalRandomKind::ParamInit),
                };
                match (form, init_kind) {
                    (_, Some(IllegalRandomKind::AnalogInitial)) => IllegalRandomKind::AnalogInitial,
                    (RandomForm::ConstSeed, _) if !self.is_const_expr(args[0]) => {
                        IllegalRandomKind::NonConstSeed
                    }
                    (RandomForm::ConstSeed, _) | (_, None) => return,
                    (_, Some(kind)) => kind,
                }
            }
        };
        self.report(BodyValidationDiagnostic::IllegalRandom { expr, kind, fun: None })
    }

    /// Analog initial blocks and initializers must not call functions that contain
    /// untyped `$random`/`$arandom` calls (initializers allow a constant seed).
    fn validate_user_call(&mut self, expr: ExprId, fun: FunctionId) {
        let (kind, allow_const) = match self.parent.owner {
            DefWithBodyId::ModuleId { initial: true, .. } => {
                (IllegalRandomKind::AnalogInitial, false)
            }
            DefWithBodyId::VarId(_) => (IllegalRandomKind::VarInit, true),
            DefWithBodyId::ParamId(_) => (IllegalRandomKind::ParamInit, true),
            _ => return,
        };
        // without full semantics the function body reports the calls
        if !self.parent.db.full_semantics() {
            return;
        }
        let mut visited = HashSet::default();
        if calls_untyped_random(self.parent.db, fun, allow_const, &mut visited) {
            self.report(BodyValidationDiagnostic::IllegalRandom { expr, kind, fun: Some(fun) })
        }
    }

    /// Constant expression: literals and parameters combined with operators
    fn is_const_expr(&self, expr: ExprId) -> bool {
        match self.parent.body.exprs[expr] {
            Expr::Literal(_) => true,
            Expr::Path { port: false, .. } => {
                matches!(self.parent.infer.expr_types[expr], Ty::Param(..))
            }
            Expr::UnaryOp { expr, .. } => self.is_const_expr(expr),
            Expr::BinaryOp { lhs, rhs, .. } => self.is_const_expr(lhs) && self.is_const_expr(rhs),
            Expr::Select { cond, then_val, else_val } => {
                self.is_const_expr(cond)
                    && self.is_const_expr(then_val)
                    && self.is_const_expr(else_val)
            }
            _ => false,
        }
    }

    fn validate_builtin(
        &mut self,
        name: &Option<Path>,
        expr: ExprId,
        mut args: &[ExprId],
        call: BuiltIn,
        signature: Option<Signature>,
    ) {
        if matches!(
            call,
            BuiltIn::random
                | BuiltIn::arandom
                | BuiltIn::dist_uniform
                | BuiltIn::dist_normal
                | BuiltIn::dist_exponential
                | BuiltIn::dist_poisson
                | BuiltIn::dist_chi_square
                | BuiltIn::dist_t
                | BuiltIn::dist_erlang
                | BuiltIn::rdist_uniform
                | BuiltIn::rdist_normal
                | BuiltIn::rdist_exponential
                | BuiltIn::rdist_poisson
                | BuiltIn::rdist_chi_square
                | BuiltIn::rdist_t
                | BuiltIn::rdist_erlang
        ) {
            self.validate_random(expr, args, call, signature.clone());
        }

        match call {
            _ if call.is_unsupported() => self
                .parent
                .diagnostics
                .push(BodyValidationDiagnostic::UnsupportedFunction { expr, func: call }),
            BuiltIn::potential | BuiltIn::flow => self.check_access(
                |_| IllegalCtxAccessKind::NatureAccess,
                expr,
                self.parent.ctx.allow_nature_access(),
            ),

            _ if call.is_analog_operator() && call != BuiltIn::ddx
                || call.is_analog_operator_sysfun() =>
            {
                // let non_const_dominator = if self.cond_diagnostic_sink.is_none() {
                // self.parent.non_const_dominator.clone()
                // } else {
                // vec![].into_boxed_slice()
                // };

                self.check_access(
                    |sel| IllegalCtxAccessKind::AnalogOperator {
                        name: name.as_ref().and_then(|p| p.as_ident()).unwrap(),
                        is_standard: call.is_analog_operator(),
                        non_const_dominator: sel.parent.non_const_dominator.clone(),
                    },
                    expr,
                    self.parent.ctx.allow_analog_operator(),
                )
            }

            _ if call.is_analysis_var() && !self.parent.ctx.allow_analysis_fun() => self
                .report_illegal_access(
                    IllegalCtxAccessKind::AnalysisFun {
                        name: name.as_ref().and_then(|p| p.as_ident()).unwrap(),
                    },
                    expr,
                ),
            BuiltIn::stop | BuiltIn::abstime | BuiltIn::analysis | BuiltIn::discontinuity
                if !self.parent.ctx.allow_analysis_state() =>
            {
                self.report_illegal_access(
                    IllegalCtxAccessKind::Builtin {
                        name: name.as_ref().and_then(|p| p.as_ident()).unwrap(),
                    },
                    expr,
                )
            }
            _ => (),
        }

        match (call, signature) {
            (BuiltIn::potential | BuiltIn::flow, Some(NATURE_ACCESS_NODES)) => {
                let hi = self.parent.infer.expr_types[args[0]].unwrap_node();
                let lo = self.parent.infer.expr_types[args[1]].unwrap_node();
                let branch = if hi >= lo {
                    BranchWrite::Unnamed { hi, lo: Some(lo) }
                } else {
                    BranchWrite::Unnamed { hi: lo, lo: Some(hi) }
                };
                self.lint_trivial_branch(branch, call, expr);
                if let Some(discipline) = self.validate_implicit_branch(expr, hi, lo) {
                    self.validate_flow_or_pot(expr, call, discipline)
                }
            }

            (BuiltIn::potential | BuiltIn::flow, Some(NATURE_ACCESS_NODE_GND)) => {
                let node = self.parent.infer.expr_types[args[0]].unwrap_node();
                if let Some(discipline) = self.parent.db.node_discipline(node) {
                    self.lint_trivial_branch(
                        BranchWrite::Unnamed { hi: node, lo: None },
                        call,
                        expr,
                    );
                    self.validate_flow_or_pot(expr, call, discipline)
                }
            }

            (BuiltIn::flow, Some(NATURE_ACCESS_PORT_FLOW)) => {
                let node = self.parent.infer.expr_types[args[0]].unwrap_port_flow();
                let node_data = self.parent.db.node_data(node);
                if !(node_data.is_input | node_data.is_output) {
                    self.report(BodyValidationDiagnostic::ExpectedPort { node, expr })
                }

                if let Some(discipline) = self.parent.db.node_discipline(node) {
                    self.validate_flow_or_pot(expr, BuiltIn::flow, discipline)
                }
            }

            (BuiltIn::potential, Some(NATURE_ACCESS_PORT_FLOW)) => {
                self.report(BodyValidationDiagnostic::PotentialOfPortFlow { expr, branch: None })
            }

            (BuiltIn::potential | BuiltIn::flow, Some(NATURE_ACCESS_BRANCH)) => {
                let branch = self.parent.infer.expr_types[args[0]].unwrap_branch();

                if let Some(branch_info) = self.parent.db.branch_info(branch) {
                    match branch_info.kind {
                        BranchKind::PortFlow(_) => {
                            if call == BuiltIn::potential {
                                self.report(BodyValidationDiagnostic::PotentialOfPortFlow {
                                    expr,
                                    branch: Some(branch),
                                })
                            } else if !self.write {
                                self.validate_flow_or_pot(
                                    expr,
                                    BuiltIn::flow,
                                    branch_info.discipline,
                                )
                            }
                        }
                        BranchKind::NodeGnd(node) => {
                            self.lint_trivial_branch(
                                BranchWrite::Unnamed { hi: node, lo: None },
                                call,
                                expr,
                            );
                            self.validate_flow_or_pot(expr, call, branch_info.discipline)
                        }
                        BranchKind::Nodes(hi, lo) => {
                            let branch = if hi >= lo {
                                BranchWrite::Unnamed { hi, lo: Some(lo) }
                            } else {
                                BranchWrite::Unnamed { hi: lo, lo: Some(hi) }
                            };
                            self.lint_trivial_branch(branch, call, expr);
                            self.validate_flow_or_pot(expr, call, branch_info.discipline)
                        }
                    }
                }
            }

            (BuiltIn::port_connected, _) => {
                let node = self.parent.infer.expr_types[args[0]].unwrap_node();
                let node_data = self.parent.db.node_data(node);
                if !(node_data.is_input | node_data.is_output) {
                    self.report(BodyValidationDiagnostic::ExpectedPort { node, expr })
                }
            }

            (
                BuiltIn::noise_table | BuiltIn::noise_table_log,
                Some(NOISE_TABLE_INLINE | NOISE_TABLE_INLINE_NAME),
            ) => self.validate_const_expr(args[0]),
            (BuiltIn::discontinuity, _) if !args.is_empty() => self.validate_const_expr(args[0]),
            (func @ (BuiltIn::simparam | BuiltIn::simparam_str), _) => {
                if self.parent.ctx == BodyCtx::Const {
                    let known = if let Expr::Literal(Literal::String(name)) =
                        &self.parent.body.exprs[args[0]]
                    {
                        matches!(
                            (func, &**name),
                            (
                                BuiltIn::simparam,
                                "minr"
                                    | "imelt"
                                    | "shrink"
                                    | "imax"
                                    | "rthresh"
                                    | "scale"
                                    | "simulatorSubversion"
                                    | "simulatorVersion"
                                    | "tnom"
                            ) | (BuiltIn::simparam_str, "cwd" | "module" | "instance" | "path")
                        )
                    } else {
                        false
                    };

                    self.report(BodyValidationDiagnostic::ConstSimparam {
                        known,
                        expr,
                        stmt: self.stmt,
                    });
                }
            }

            (BuiltIn::absdelay, Some(ABSDELAY_MAX))
            | (BuiltIn::transition, Some(TRANSITION_DELAY_RISET_FALLT_TOL))
            | (BuiltIn::ddt, Some(DDT_TOL))
            | (BuiltIn::idt | BuiltIn::idtmod, Some(IDT_IC_ASSERT_TOL)) => {
                if let [other_args @ .., const_expr] = args {
                    // Do not type check const expr twice
                    args = other_args;
                    self.validate_const_expr(*const_expr);
                };
            }

            (
                BuiltIn::laplace_nd
                | BuiltIn::laplace_np
                | BuiltIn::laplace_zp
                | BuiltIn::laplace_zd,
                Some(_),
            ) => {
                // args[0] (input signal) and args[1]/args[2] (num/den, or zero/pole) are
                // validated normally below: num/den may be either an array literal (whose
                // elements may be ordinary runtime expressions, e.g. parameters) or a bare
                // reference to a module-body array variable (Enhancement-4) -- neither is
                // required to be a compile-time constant, since each element is lowered as an
                // ordinary MIR value, not constant-folded. Only the optional trailing
                // tolerance/nature argument (unused, see Enhancement-4.md §1.3) still must be
                // constant.
                if let [_in, _num, _den, const_args @ ..] = args {
                    args = &args[..3];
                    for arg in const_args {
                        self.validate_const_expr(*arg)
                    }
                }
            }

            (BuiltIn::zi_nd | BuiltIn::zi_np | BuiltIn::zi_zd | BuiltIn::zi_zp, Some(_)) => {
                if let [_expr, const_args @ ..] = args {
                    args = &args[..1];
                    for arg in const_args {
                        self.validate_const_expr(*arg)
                    }
                }
            }

            _ => (),
        }

        for arg in args {
            self.validate_expr(*arg)
        }
    }

    fn validate_const_expr(&mut self, expr: ExprId) {
        let old = replace(&mut self.parent.ctx, BodyCtx::Const);
        let sink = self.cond_diagnostic_sink.take();
        self.validate_expr(expr);
        self.cond_diagnostic_sink = sink;
        self.parent.ctx = old;
    }
}

/// Whether `fun` or a function it calls contains an untyped `$random`/`$arandom`/
/// `$rdist_*` or a `$dist_*` call (other than a constant seed if
/// `allow_const` is set)
fn calls_untyped_random(
    db: &dyn HirTyDB,
    fun: FunctionId,
    allow_const: bool,
    visited: &mut HashSet<FunctionId>,
) -> bool {
    if !visited.insert(fun) {
        return false;
    }
    let infer = db.inference_result(DefWithBodyId::FunctionId(fun));
    infer.resolved_calls.iter().any(|(expr, call)| match *call {
        ResolvedFun::BuiltIn(
            builtin @ (BuiltIn::random
            | BuiltIn::arandom
            | BuiltIn::dist_uniform
            | BuiltIn::dist_normal
            | BuiltIn::dist_exponential
            | BuiltIn::dist_poisson
            | BuiltIn::dist_chi_square
            | BuiltIn::dist_t
            | BuiltIn::dist_erlang
            | BuiltIn::rdist_uniform
            | BuiltIn::rdist_normal
            | BuiltIn::rdist_exponential
            | BuiltIn::rdist_poisson
            | BuiltIn::rdist_chi_square
            | BuiltIn::rdist_t
            | BuiltIn::rdist_erlang),
        ) => {
            let sig = infer.resolved_signatures.get(expr).cloned().unwrap_or(NO_SIGNATURE);
            let form = RandomForm::new(builtin, sig);
            match form {
                Some(RandomForm::Typed) | None => false,
                Some(RandomForm::ConstSeed) => !allow_const,
                Some(_) => true,
            }
        }
        ResolvedFun::User { func, .. } => calls_untyped_random(db, func, allow_const, visited),
        _ => false,
    })
}
