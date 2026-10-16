use std::fs;

use expect_test::expect_file;
use hir::diagnostics::ConsoleSink;
use hir::CompilationDB;
use hir_lower::PlaceKind;
use indoc::indoc;
use lasso::Rodeo;
use stdx::{integration_test_dir, openvaf_test_data};

use crate::context::{Context, OptimiziationStage};
use crate::dae::DaeSystem;
use crate::init::Initialization;
use crate::topology::Topology;

fn run_test(src: &str) {
    let db = CompilationDB::new_virtual(src).unwrap();
    let module = crate::collect_modules(&db, false, &mut ConsoleSink::new(&db)).unwrap().remove(0);
    let mut literals = Rodeo::new();
    let mut cx = Context::new(&db, &mut literals, &module, &[]);
    let init = build_init(&mut cx);
    let name = module.module.name(&db);
    let test_dir = openvaf_test_data("init");
    let topology = format!("{:#?}\n{:#?}", init.cached_vals, init.cache_slots);
    expect_file![test_dir.join(format!("{name}_system.snap"))].assert_eq(&topology);
    let func = format!("{:#?}", init.func);
    expect_file![test_dir.join(format!("{name}_init_mir.snap"))].assert_eq(&func);
    let func = format!("{:#?}", &cx.func);
    expect_file![test_dir.join(format!("{name}_eval_mir.snap"))].assert_eq(&func);
}

fn build_init(cx: &mut Context) -> Initialization {
    cx.compute_outputs(true);
    cx.compute_cfg();
    cx.optimize(OptimiziationStage::Initial);

    let topology = Topology::new(cx);
    let mut dae_system = DaeSystem::new(cx, topology);

    cx.compute_cfg();
    let gvn = cx.optimize(OptimiziationStage::PostDerivative);
    dae_system.sparsify(cx);

    cx.refresh_op_dependent_insts();
    let init = Initialization::new(cx, gvn);
    assert!(cx.func.validate());
    assert!(init.func.validate());
    init
}

#[test]
fn diode() {
    let src = fs::read_to_string(integration_test_dir("DIODE").join("diode.va")).unwrap();
    run_test(&src);
}

#[test]
fn resistor() {
    cov_mark::check!(cache_output);
    cov_mark::check!(op_independent_output);
    let src = fs::read_to_string(integration_test_dir("RESISTOR").join("resistor.va")).unwrap();
    run_test(&src);
}

#[test]
fn op_dependent_collapse_hint() {
    cov_mark::check!(ignore_if_op_dependent);
    let src = indoc! {r#"
        `include "disciplines.vams"
        module op_dependent_collapse_hint(inout a, inout c);
            electrical a, c, d;
            parameter real foo=1.0;
            analog begin
                if (foo == 0) 
                    V(d) <+ 0.0;
                if (V(a, c) < 0) 
                    V(d) <+ 0.0;
                else
                    V(d) <+ foo;
                I(a, c) <+ V(d);
            end
        endmodule
    "#};
    run_test(src);
}

#[test]
fn analysis() {
    let src = indoc! {r#"
        `include "disciplines.vams"
        module analysis_dependent(inout a, inout c);
            electrical a, c;
            parameter real R=1.0;
            analog begin
                if (analysis("tran"))
                    I(a, c) <+ R * V(a,c);
            end
        endmodule
    "#};
    run_test(src);
}

/// The values of the hidden state variables after the analog initial blocks are
/// computed by init. The MIR of the modules with hidden state is compared to
/// snapshots.
#[test]
fn hidden_state() {
    let src =
        fs::read_to_string(openvaf_test_data("hidden_state").join("hidden_state.va")).unwrap();
    let db = CompilationDB::new_virtual(&src).unwrap();
    let modules = crate::collect_modules(&db, false, &mut ConsoleSink::new(&db)).unwrap();
    let test_dir = openvaf_test_data("init").join("hidden_state");
    let mut literals = Rodeo::new();
    for module in &modules {
        let name = module.module.name(&db);
        let hidden_state = Context::detect_hidden_state(&db, &mut literals, module);
        let mut cx = Context::new(&db, &mut literals, module, &hidden_state);
        let init = build_init(&mut cx);

        let mut outputs = String::new();
        for var in &hidden_state {
            let kind = PlaceKind::HiddenStateInit(*var);
            let val = init.intern.outputs.get(&kind).and_then(|val| val.expand());
            let val =
                val.unwrap_or_else(|| panic!("no init value for {} in {name}", var.name(&db)));
            assert!(
                cx.intern.outputs[&kind].is_none(),
                "init value of {} in {name} is an eval output",
                var.name(&db)
            );
            outputs.push_str(&format!("{} -> {val}\n", var.name(&db)));
        }

        if !matches!(&*name, "hidden_state" | "hs_ainit") {
            continue;
        }
        expect_file![test_dir.join(format!("{name}_outputs.snap"))].assert_eq(&outputs);
        let func = format!("{:#?}", init.func);
        expect_file![test_dir.join(format!("{name}_init_mir.snap"))].assert_eq(&func);
        let func = format!("{:#?}", &cx.func);
        expect_file![test_dir.join(format!("{name}_eval_mir.snap"))].assert_eq(&func);
    }
}
