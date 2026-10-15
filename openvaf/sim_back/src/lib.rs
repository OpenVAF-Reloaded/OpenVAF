use hir::{BranchWrite, CompilationDB, Node, Variable};
use hir_lower::{CurrentKind, HirInterner, ImplicitEquation, ParamKind};
use lasso::Rodeo;
use mir::Function;
use mir_opt::{simplify_cfg, sparse_conditional_constant_propagation};
pub use module_info::{collect_modules, ModuleInfo};
use stdx::impl_debug_display;

use crate::context::{Context, OptimiziationStage};
use crate::dae::DaeSystem;
use crate::init::Initialization;
use crate::node_collapse::NodeCollapse;
use crate::topology::Topology;

mod context;
pub mod dae;
pub mod init;
mod module_info;
pub mod node_collapse;
mod noise;
mod topology;

mod util;

// #[cfg(test)]
// mod tests;

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub enum SimUnknownKind {
    KirchoffLaw(Node),
    Current(CurrentKind),
    Implicit(ImplicitEquation),
}

impl_debug_display! {
    match SimUnknownKind{
        SimUnknownKind::KirchoffLaw(node) => "{node:?}";
        SimUnknownKind::Current(curr) => "br[{curr:?}]";
        SimUnknownKind::Implicit(node) => "{node}";
    }
}

pub struct CompiledModule<'a> {
    pub info: &'a ModuleInfo,
    pub dae_system: DaeSystem,
    pub eval: Function,
    pub intern: HirInterner,
    pub init: Initialization,
    pub model_param_setup: Function,
    pub model_param_intern: HirInterner,
    pub node_collapse: NodeCollapse,
    /// Variables whose value must be kept between evaluations
    /// (empty unless hidden state detection is enabled)
    pub hidden_state: Vec<Variable>,
}

pub fn print_module(
    pfx: &str,
    db: &CompilationDB,
    module: &ModuleInfo,
    dae_system: &DaeSystem,
    init: &Initialization,
) {
    let m = module.module;

    println!("{pfx}Module: {:?}", m.name(&db));
    println!("{pfx}Ports: {:?}", m.ports(&db));
    println!("{pfx}Internal nodes: {:?}", m.internal_nodes(&db));

    let dae_str = format!("{dae_system:#?}");
    println!("{pfx}{}", dae_str);
    println!("");

    println!("Cached values during instance setup");
    init.cached_vals.iter().for_each(|(val, slot)| {
        println!("  {:?} -> {:?}", val, slot);
    });
    init.cache_slots.iter_enumerated().for_each(|(slot, (cls, ty))| {
        println!("  {:?} -> {:?} {:?}", slot, cls, ty);
    });
}

pub fn print_intern(pfx: &str, db: &CompilationDB, intern: &HirInterner) {
    println!("{pfx}Parameters:");
    intern.params.iter().for_each(|(p, val)| {
        print!("{pfx}  {:?}", p);
        match p {
            ParamKind::Param(param) => {
                println!("{pfx} .. {:?} -> {:?}", param.name(db), val);
            }
            ParamKind::ParamGiven { param } => {
                println!("{pfx} .. {:?} -> {:?}", param.name(db), val);
            }
            ParamKind::Voltage { hi, lo } => {
                if lo.is_some() {
                    print!("{pfx} .. V({:?},{:?})", hi.name(db), lo.unwrap().name(db));
                } else {
                    print!("{pfx} .. V({:?})", hi.name(db));
                }
                println!(" -> {:?}", val);
            }
            ParamKind::Current(ck) => match ck {
                CurrentKind::Branch(br) => {
                    println!("{pfx} .. {:?} -> {:?}", br.name(db), val);
                }
                CurrentKind::Unnamed { hi, lo } => {
                    if lo.is_some() {
                        print!("{pfx} .. I({:?},{:?})", hi.name(db), lo.unwrap().name(db));
                    } else {
                        print!("{pfx} .. I({:?})", hi.name(db));
                    }
                    println!(" -> {:?}", val);
                }
                CurrentKind::Port(n) => {
                    println!("{pfx} .. {:?} -> {:?}", n.name(db), val);
                }
            },
            ParamKind::HiddenState(var) => {
                println!("{pfx} .. {:?} -> {:?}", var.name(db), val);
            }
            // ParamKind::ImplicitUnknown
            ParamKind::PortConnected { port } => {
                println!("{pfx} .. {:?} -> {:?}", port.name(db), val);
            }
            _ => {
                println!("{pfx} -> {:?}", val);
            }
        }
    });
    println!("");

    println!("{pfx}Outputs:");
    intern.outputs.iter().for_each(|(p, val)| {
        if val.is_some() {
            println!("{pfx}  {:?} -> {:?}", p, val.unwrap());
        } else {
            println!("{pfx}  {:?} -> None", p);
        }
    });
    println!("");

    println!("{pfx}Tagged reads:");
    intern.tagged_reads.iter().for_each(|(val, var)| {
        println!("{pfx}  {:?} -> {:?}", val, var);
    });
    println!("");

    println!("{pfx}Implicit equations:");
    for (i, &iek) in intern.implicit_equations.iter().enumerate() {
        println!("{pfx}  {:?} : {:?}", i, iek);
    }
}

pub fn print_mir(literals: &Rodeo, func: &Function) {
    println!("{}", func.print(&literals));
}

impl<'a> CompiledModule<'a> {
    pub fn new(
        db: &CompilationDB,
        module: &'a ModuleInfo,
        literals: &mut Rodeo,
        dump_unopt_mir: bool,
        dump_mir: bool,
        hidden_state: bool,
        dump_hs: bool,
    ) -> CompiledModule<'a> {
        let hidden_state = if hidden_state {
            Context::detect_hidden_state(db, literals, module)
        } else {
            Vec::new()
        };
        if dump_hs {
            println!("Hidden state of {}", module.module.name(db));
            for var in &hidden_state {
                println!("  {}", var.name(db));
            }
        }

        // Build MIR for the module
        let mut cx = Context::new(db, literals, module, &hidden_state);

        if dump_unopt_mir {
            println!("Unoptimized MIR (no DAE) of {}", module.module.name(db));
            print_mir(literals, &cx.func);
        }

        // Some basic optimization
        cx.compute_outputs(true);
        cx.compute_cfg();
        cx.optimize(OptimiziationStage::Initial);
        debug_assert!(cx.func.validate());

        // Add extra stuff needed for evaluating the DAE system
        let topology = Topology::new(&mut cx);
        debug_assert!(cx.func.validate());
        let mut dae_system = DaeSystem::new(&mut cx, topology);

        if dump_unopt_mir {
            println!("Partially optimized MIR (with DAE) of {}", module.module.name(db));
            print_mir(literals, &cx.func);
        }

        debug_assert!(cx.func.validate());

        // Optimization
        cx.compute_cfg();
        let gvn = cx.optimize(OptimiziationStage::PostDerivative);
        dae_system.sparsify(&mut cx);
        debug_assert!(cx.func.validate());

        // Instance setup MIR - a copy of module MIR where only those instructions
        // are kept that do not depend on op.
        // This removes all instructions that do not depend on op from module MIR.
        cx.refresh_op_dependent_insts();
        let mut init = Initialization::new(&mut cx, gvn);
        // Build node collapse pairs
        let node_collapse = NodeCollapse::new(&init, &dae_system, &cx);
        debug_assert!(cx.func.validate());
        debug_assert!(init.func.validate());

        // TODO: refactor param intilization to use tables
        // Make a list of instance parameters
        let inst_params: Vec<_> = module
            .params
            .iter()
            .filter_map(|(param, info)| info.is_instance.then_some(*param))
            .collect();
        // Add initialization of instance parameters
        init.intern.insert_param_init(db, &mut init.func, literals, false, true, &inst_params);

        // Model setup MIR
        let mut model_param_setup = Function::default();
        let model_params: Vec<_> = module.params.keys().copied().collect();
        let mut model_param_intern = HirInterner::default();
        model_param_intern.insert_param_init(
            db,
            &mut model_param_setup,
            literals,
            false,
            true,
            &model_params,
        );
        cx.cfg.compute(&model_param_setup);
        simplify_cfg(&mut model_param_setup, &mut cx.cfg);
        sparse_conditional_constant_propagation(&mut model_param_setup, &cx.cfg);
        simplify_cfg(&mut model_param_setup, &mut cx.cfg);

        if dump_mir {
            println!("Optimized model setup MIR of {}", module.module.name(db));
            print_mir(literals, &model_param_setup);
            println!();

            println!("Optimized instance setup MIR of {}", module.module.name(db));
            print_mir(literals, &init.func);
            println!();

            println!("Optimized evaluation MIR of {}", module.module.name(db));
            print_mir(literals, &cx.func);
            println!();
        }

        CompiledModule {
            eval: cx.func,
            intern: cx.intern,
            info: module,
            dae_system,
            init,
            model_param_intern,
            model_param_setup,
            node_collapse,
            hidden_state,
        }
    }
}
