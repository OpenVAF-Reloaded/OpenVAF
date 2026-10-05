use std::f64::consts;
use std::ffi::OsStr;
use std::path::Path;

use camino::{Utf8Path, Utf8PathBuf};
use expect_test::expect_file;
use float_cmp::assert_approx_eq;
use mini_harness::{harness, Result};
use openvaf::{CompilationDestination, CompilationTermination, LLVMCodeGenOptLevel};
use stdx::{ignore_dev_tests, openvaf_test_data, project_root};
use target::spec::Target;

use crate::load::{load_osdi_lib, EvalFlags, OsdiDescriptor};
use crate::mock_sim::{MockSimulation, ALPHA};

mod load;
mod mock_sim;

fn absdelay_maxdelay_offset_test() -> Result<()> {
    const SRC: &str = r#"`include "constants.vams"
`include "disciplines.vams"

module absdelay_mix(A,B,C);
    inout A, B, C;
    electrical A,B,C;

    branch (A,B) br_a_b;
    branch (B,C) br_b_c;

    parameter real td = 1e-9 from [0:inf];
    parameter real tdmax = 2e-9 from [0:inf];

    analog begin
        I(br_a_b) <+ absdelay(V(br_a_b), td);
        I(br_b_c) <+ absdelay(V(br_b_c), td, tdmax);
    end
endmodule
"#;
    let root_file: Utf8PathBuf =
        Utf8PathBuf::try_from(std::env::temp_dir())?.join("openvaf_absdelay_maxdelay_test.va");
    std::fs::write(&root_file, SRC)?;
    let descr = compile_and_load(&root_file);
    println!("absdelay_count = {}", descr.absdelay_count);
    assert_eq!(descr.absdelay_count, 2);
    let slots =
        unsafe { std::slice::from_raw_parts(descr.absdelays, descr.absdelay_count as usize) };
    for (i, s) in slots.iter().enumerate() {
        println!(
            "slot {i}: y_node={} z_node={} td_offset={} maxdelay_offset={}",
            s.y_node, s.z_node, s.td_offset, s.maxdelay_offset
        );
    }
    let no_max = slots.iter().find(|s| s.maxdelay_offset == u32::MAX).unwrap();
    let has_max = slots.iter().find(|s| s.maxdelay_offset != u32::MAX).unwrap();
    assert_eq!(no_max.maxdelay_offset, u32::MAX, "2-arg slot must have maxdelay_offset == MAX");
    assert_ne!(has_max.maxdelay_offset, u32::MAX, "3-arg slot must have a real maxdelay_offset");
    assert_ne!(
        has_max.maxdelay_offset, has_max.td_offset,
        "maxdelay_offset must differ from td_offset"
    );
    Ok(())
}

fn compile_and_load(root_file: &Utf8Path) -> &'static OsdiDescriptor {
    let openvaf_opts = openvaf::Opts {
        defines: Vec::new(),
        codegen_opts: Vec::new(),
        lints: Vec::new(),
        input: root_file.to_path_buf(),
        output: CompilationDestination::Path { lib_file: root_file.with_extension("osdi") },
        include: Vec::new(),
        opt_lvl: LLVMCodeGenOptLevel::LLVMCodeGenLevelAggressive,
        target: Target::host_target().expect(
            "Failed to determine host target. This architecture may not be supported by OpenVAF. \
             Supported targets include: x86_64-unknown-linux, aarch64-unknown-linux, riscv64-unknown-linux, etc."
        ),
        target_cpu: "native".to_owned(),
        dry_run: false,
        dump_mir: false,
        dump_unopt_mir: false,
        dump_ir: false,
        dump_unopt_ir: false,
    };

    let res = openvaf::compile(&openvaf_opts).unwrap();
    let lib_file = match res {
        CompilationTermination::Compiled { lib_file } => lib_file,
        CompilationTermination::FatalDiagnostic => {
            panic!("openvaf: compilation of {root_file} failed");
        }
    };
    let libs = unsafe { load_osdi_lib(&lib_file).unwrap() };
    assert_eq!(libs.len(), 1);
    &libs[0]
}

// fn integration_test(dir: &str) -> Result {
//     let path: Utf8PathBuf = project_root().join("integration_tests").try_into().unwrap();
//     let name = dir.to_lowercase();
//     let main_file = path.join(dir).join(format!("{name}.va"));
//     let device = compile_and_load(&main_file);

//     Ok(())
// }

fn integration_test(dir: &Path) -> Result {
    let name = dir.file_name().unwrap().to_str().unwrap().to_lowercase();
    let main_file = dir.join(format!("{name}.va"));
    test_descriptor(&main_file)?;
    Ok(())
}

/// Test a single Verilog-A file directly (for VACASK models)
/// Uses "vacask_" prefix for snapshot names to avoid conflicts with OpenVAF models
fn vacask_test(file: &Path) -> Result {
    test_descriptor_with_prefix(file, "vacask_")?;
    Ok(())
}

/// Test a single Verilog-A file with SPICE naming prefix
fn vacask_spice_test(file: &Path) -> Result {
    test_descriptor_with_prefix(file, "vacask_spice_")?;
    Ok(())
}

/// Test a single Verilog-A file with simplified SPICE naming prefix
fn vacask_spice_sn_test(file: &Path) -> Result {
    test_descriptor_with_prefix(file, "vacask_spice_sn_")?;
    Ok(())
}

/// Filter to only include .va files
fn is_va_file(path: &Path) -> bool {
    path.extension() == Some(OsStr::new("va"))
}

/// Get path to VACASK devices directory
fn vacask_devices() -> std::path::PathBuf {
    project_root().join("external/vacask/devices")
}

fn test_descriptor(main_file: &Path) -> Result<&'static OsdiDescriptor> {
    test_descriptor_with_prefix(main_file, "")
}

fn test_descriptor_with_prefix(main_file: &Path, prefix: &str) -> Result<&'static OsdiDescriptor> {
    let main_file: &Utf8Path = main_file.try_into().unwrap();
    let name = main_file.file_stem().unwrap();
    let desc = compile_and_load(main_file);
    let expect = format!("{desc:?}");
    let test_dir = openvaf_test_data("osdi");
    expect_file![test_dir.join(format!("{prefix}{name}.snap"))].assert_eq(&expect);
    let default_model = desc.new_model();
    default_model.process_params()?;
    let mut instance = default_model.new_instance();
    instance.process_params(&default_model, desc.num_terminals, 300.0)?;
    Ok(desc)
}

macro_rules! assert_approx_eq {
    ($val: expr, $resist: expr, $react: expr) => {
        let (resist, react) = $val;
        let resist_ref: f64 = $resist;
        if (resist - resist_ref).abs() / resist.min(resist_ref) >= 0.01 {
            float_cmp::assert_approx_eq!(f64, resist, resist_ref, epsilon = 1e-10)
        }
        let react_ref: f64 = $react;
        if (react - react_ref).abs() / react.min(react_ref) >= 0.01 {
            float_cmp::assert_approx_eq!(f64, react, react_ref, epsilon = 1e-10)
        }
    };
}

fn test_limit() -> Result<()> {
    // skipping in CI for now as we don't have a toolchain there
    // currently
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    const KB: f64 = 1.3806488e-23;
    const Q: f64 = 1.602176565e-19;
    const VT: f64 = KB * 300.0 / Q;
    const IS: f64 = 1e-12;
    const CJ0: f64 = 10e-9;
    let vcrit = VT * f64::ln(VT / (consts::SQRT_2 * IS));
    let check_dae_equations = |sim: &MockSimulation, vd_lim, vd| {
        let id = |vd| IS * (f64::exp(vd / VT) - 1.0);
        let id_vd = |vd| IS / VT * f64::exp(vd / VT);
        let cj = |vd| CJ0 * vd;
        assert_approx_eq!(sim.read_jacobian("A", "A"), id_vd(vd_lim), CJ0);
        assert_approx_eq!(sim.read_jacobian("C", "C"), id_vd(vd_lim), CJ0);
        assert_approx_eq!(sim.read_jacobian("A", "C"), -id_vd(vd_lim), -CJ0);
        assert_approx_eq!(sim.read_jacobian("C", "A"), -id_vd(vd_lim), -CJ0);
        assert_approx_eq!(
            sim.read_residual("A"),
            id(vd_lim) - id_vd(vd_lim) * (vd_lim - vd),
            cj(vd_lim) - CJ0 * (vd_lim - vd)
        );
        assert_approx_eq!(
            sim.read_residual("C"),
            id_vd(vd_lim) * (vd_lim - vd) - id(vd_lim),
            CJ0 * (vd_lim - vd) - cj(vd_lim)
        );
    };

    let check_spice_equations = |sim: &MockSimulation, vd_lim, vd| {
        let id = |vd| IS * (f64::exp(vd / VT) - 1.0);
        let id_vd = |vd| IS / VT * f64::exp(vd / VT);
        let cj = |vd| CJ0 * vd;
        assert_approx_eq!(
            sim.read_residual("A"),
            id_vd(vd_lim) * vd_lim - id(vd_lim) + ALPHA * (CJ0 * vd_lim - cj(vd_lim)),
            0.0
        );
        assert_approx_eq!(
            sim.read_residual("C"),
            id_vd(vd_lim) * (vd_lim - vd) - id(vd_lim),
            CJ0 * (vd_lim - vd) - cj(vd_lim)
        );
        assert_approx_eq!(sim.read_jacobian("A", "A"), id_vd(vd_lim) + ALPHA * CJ0, 0.0);
        assert_approx_eq!(sim.read_jacobian("C", "C"), id_vd(vd_lim) + ALPHA * CJ0, 0.0);
        assert_approx_eq!(sim.read_jacobian("A", "C"), -id_vd(vd_lim) - ALPHA * CJ0, 0.0);
        assert_approx_eq!(sim.read_jacobian("C", "A"), -id_vd(vd_lim) - ALPHA * CJ0, 0.0);
    };

    // compile model and setup simulation
    let desc = test_descriptor(&openvaf_test_data("osdi").join("diode_lim.va"))?;
    let model = desc.new_model();
    model.set_real_param(1, IS);
    model.set_real_param(5, CJ0);
    model.process_params()?;
    let mut instance = model.new_instance();
    let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;

    instance.eval(&model, &mut sim, EvalFlags::INIT_LIM | EvalFlags::ENABLE_LIM);
    instance.load_dae(&model, &mut sim);
    check_dae_equations(&sim, vcrit, 0.0);
    sim.clear();
    instance.load_spice(&model, &mut sim);
    check_spice_equations(&sim, vcrit, 0.0);

    sim.next_iter();
    sim.set_voltage("A", 2.0 * vcrit);
    instance.eval(&model, &mut sim, EvalFlags::ENABLE_LIM);
    instance.load_dae(&model, &mut sim);
    check_dae_equations(&sim, 1.5 * vcrit, 2.0 * vcrit);
    sim.clear();
    instance.load_spice(&model, &mut sim);
    check_spice_equations(&sim, 1.5 * vcrit, 2.0 * vcrit);
    Ok(())
}

macro_rules! assert_approx_eq {
    ($val: expr, $expect: expr) => {
        let resist = $val;
        let resist_ref: f64 = $expect;
        if (resist - resist_ref).abs() / resist.min(resist_ref) >= 0.01 {
            float_cmp::assert_approx_eq!(f64, resist, resist_ref, epsilon = 1e-10)
        }
    };
}

fn test_noise() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    // skipping in CI for now as we don't have a toolchain there
    // currently
    const MFACTOR: f64 = 2.0;
    const PWR: f64 = 3.0;
    const EXP: f64 = 7.0;
    const V_AC: f64 = 13.0;

    // compile model and setup simulation
    let desc = test_descriptor(&openvaf_test_data("osdi").join("noise.va"))?;
    let model = desc.new_model();
    model.set_real_param(0, MFACTOR);
    model.set_real_param(1, PWR);
    model.set_real_param(2, EXP);
    model.process_params()?;
    let mut instance = model.new_instance();
    let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;

    sim.set_voltage("a", V_AC);
    instance.eval(&model, &mut sim, EvalFlags::empty());
    for freq in 1..10 {
        let freq = freq as f64;
        instance.load_noise(&model, &mut sim, freq);
        let white_noise1 = MFACTOR * PWR * V_AC;
        let white_noise2 = MFACTOR * PWR * PWR * V_AC;
        let flickr_noise1 = MFACTOR * V_AC * PWR * PWR / (freq.powf(EXP));
        let flickr_noise2 = MFACTOR * PWR * PWR / (freq.powf(EXP * V_AC));
        assert_approx_eq!(sim.read_noise(0), white_noise1);
        assert_approx_eq!(sim.read_noise(1), white_noise2);
        assert_approx_eq!(sim.read_noise(2), flickr_noise1);
        assert_approx_eq!(sim.read_noise(3), flickr_noise2);
    }
    Ok(())
}

// Enhancement-2: indirect branch assignment `V(out) : V(pin,nin) == 0` (ideal op-amp).
// The implicit equation must be `V(pin,nin) = 0`, independent of V(out), and V(out) must
// follow the implicit unknown through the voltage branch.
fn indirect_opamp_test() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    const SRC: &str = r#"`include "disciplines.vams"
module indirect_opamp(out, pin, nin);
    inout out, pin, nin;
    electrical out, pin, nin;
    analog
        V(out) : V(pin,nin) == 0;
endmodule
"#;
    let root_file: Utf8PathBuf =
        Utf8PathBuf::try_from(std::env::temp_dir())?.join("openvaf_indirect_opamp_test.va");
    std::fs::write(&root_file, SRC)?;
    let desc = compile_and_load(&root_file);
    let model = desc.new_model();
    model.process_params()?;
    let mut instance = model.new_instance();
    let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;
    const V_OUT: f64 = 0.7;
    const V_PIN: f64 = 1.3;
    const V_NIN: f64 = 0.2;
    const I_OUT: f64 = 2e-3;
    const V_IMPLICIT: f64 = 0.5;
    sim.set_voltage("out", V_OUT);
    sim.set_voltage("pin", V_PIN);
    sim.set_voltage("nin", V_NIN);
    sim.set_voltage("flow(out)", I_OUT);
    sim.set_voltage("implicit_equation_0", V_IMPLICIT);
    instance.eval(&model, &mut sim, EvalFlags::empty());
    instance.load_dae(&model, &mut sim);

    // KCL at out: the branch current flows out of the node
    assert_eq!(sim.read_residual("out"), (I_OUT, 0.0));
    assert_eq!(sim.read_residual("pin"), (0.0, 0.0));
    assert_eq!(sim.read_residual("nin"), (0.0, 0.0));
    // branch equation: V(out) follows the implicit unknown
    assert_approx_eq!(sim.read_residual("flow(out)").0, V_IMPLICIT - V_OUT);
    // implicit equation: V(pin,nin) - 0, independent of V(out)
    assert_approx_eq!(sim.read_residual("implicit_equation_0").0, V_PIN - V_NIN);

    assert_eq!(sim.read_jacobian("out", "flow(out)"), (1.0, 0.0));
    assert_eq!(sim.read_jacobian("flow(out)", "out"), (-1.0, 0.0));
    assert_eq!(sim.read_jacobian("flow(out)", "implicit_equation_0"), (1.0, 0.0));
    assert_eq!(sim.read_jacobian("implicit_equation_0", "pin"), (1.0, 0.0));
    assert_eq!(sim.read_jacobian("implicit_equation_0", "nin"), (-1.0, 0.0));
    // exactly the five entries above (index 0 is the ground placeholder)
    assert_eq!(sim.jacobian_info.len(), 6);
    Ok(())
}

// Enhancement-3: vector ports. A 4-bit DAC with a bus port followed by a scalar port, in
// non-ANSI and ANSI style. The OSDI terminals must be `d[0] d[1] d[2] d[3] out` (simulators
// bind instance terminals by position) and the output must be computed from the right bits.
fn bus_port_dac_test() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    const NON_ANSI: &str = r#"`include "disciplines.vams"
module dac4(d, out);
    input [0:3] d;
    output out;
    electrical [0:3] d;
    electrical out;
    parameter real vref = 1.0;
    analog V(out) <+ vref * (V(d[0]) + 2*V(d[1]) + 4*V(d[2]) + 8*V(d[3])) / 16;
endmodule
"#;
    const ANSI: &str = r#"`include "disciplines.vams"
module dac4(input electrical [0:3] d, output electrical out);
    parameter real vref = 1.0;
    analog V(out) <+ vref * (V(d[0]) + 2*V(d[1]) + 4*V(d[2]) + 8*V(d[3])) / 16;
endmodule
"#;
    for (style, src) in [("non_ansi", NON_ANSI), ("ansi", ANSI)] {
        let root_file: Utf8PathBuf = Utf8PathBuf::try_from(std::env::temp_dir())?
            .join(format!("openvaf_bus_port_dac_{style}_test.va"));
        std::fs::write(&root_file, src)?;
        let desc = compile_and_load(&root_file);
        assert_eq!(desc.num_terminals, 5, "{style}");
        let model = desc.new_model();
        model.process_params()?;
        let mut instance = model.new_instance();
        let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;
        // terminals in port order followed by the internal unknown of the voltage source
        let nodes: Vec<_> = sim.nodes.iter().copied().collect();
        assert_eq!(nodes, ["gnd", "d[0]", "d[1]", "d[2]", "d[3]", "out", "flow(out)"], "{style}");

        // code = 1 + 4 + 8 = 13
        const V_OUT: f64 = 0.25;
        for (bit, v) in ["d[0]", "d[1]", "d[2]", "d[3]"].into_iter().zip([1.0, 0.0, 1.0, 1.0]) {
            sim.set_voltage(bit, v);
        }
        sim.set_voltage("out", V_OUT);
        instance.eval(&model, &mut sim, EvalFlags::empty());
        instance.load_dae(&model, &mut sim);

        assert_approx_eq!(sim.read_residual("flow(out)").0, 13.0 / 16.0 - V_OUT);
        // each bit is read from its own terminal with weight 2^i / 16
        for (i, bit) in ["d[0]", "d[1]", "d[2]", "d[3]"].into_iter().enumerate() {
            assert_eq!(sim.read_residual(bit), (0.0, 0.0), "{style}");
            assert_eq!(
                sim.read_jacobian("flow(out)", bit),
                ((1 << i) as f64 / 16.0, 0.0),
                "{style}: {bit}"
            );
        }
        assert_eq!(sim.read_jacobian("flow(out)", "out"), (-1.0, 0.0), "{style}");
        assert_eq!(sim.read_jacobian("out", "flow(out)"), (1.0, 0.0), "{style}");
    }
    Ok(())
}

harness! {
    // TODO: run this in CI, somehow this test is flakey tough regarding the linker invocation (and really slow)
    Test::from_dir("integration", &integration_test, &ignore_dev_tests, &project_root().join("integration_tests")),
    // VACASK basic device models
    Test::from_dir_filtered("vacask", &vacask_test, &is_va_file, &ignore_dev_tests, &vacask_devices()),
    // VACASK SPICE models
    Test::from_dir_filtered("vacask_spice", &vacask_spice_test, &is_va_file, &ignore_dev_tests, &vacask_devices().join("spice")),
    // VACASK simplified SPICE models
    Test::from_dir_filtered("vacask_spice_sn", &vacask_spice_sn_test, &is_va_file, &ignore_dev_tests, &vacask_devices().join("spice/sn")),
    [Test::new("$limit", &test_limit),Test::new("noise", &test_noise),Test::new("absdelay_maxdelay_offset", &absdelay_maxdelay_offset_test),Test::new("indirect_opamp", &indirect_opamp_test),Test::new("bus_port_dac", &bus_port_dac_test)]
}
