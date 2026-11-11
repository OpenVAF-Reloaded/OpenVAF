//! `$random`/`$arandom`: generator sequences (checked against a reimplementation of
//! the stdlib generator) and the compile errors of illegal calls.

use camino::Utf8PathBuf;
use mini_harness::Result;

use crate::load::EvalFlags;
use crate::{compile_and_load_modules, compile_and_load_modules_with, compile_opts, compiles};

fn fmix32(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85eb_ca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2_ae35);
    h ^= h >> 16;
    h
}

fn mix32(base: u32, site_id: u32) -> u32 {
    fmix32(base ^ fmix32(site_id.wrapping_add(0x9e37_79b9)))
}

/// Initial state of a generator seeded with the entity seed
fn site_seed(entity_seed: u32, site_id: u32) -> i32 {
    mix32(entity_seed, site_id) as i32
}

/// Next state of a generator
fn next(state: i32) -> i32 {
    69069u32.wrapping_mul(state as u32).wrapping_add(1) as i32
}

/// Random value of a generator state
fn value(state: i32) -> i32 {
    fmix32(state as u32) as i32
}

const SRC: &str = r#"`include "disciplines.vams"
module random_test(a, b, c, d, e, f, g, h, l);
    inout a, b, c, d, e, f, g, h, l;
    electrical a, b, c, d, e, f, g, h, l;
    parameter integer seed = 7;
    parameter integer p = $arandom(11);
    integer x = $arandom(13);
    integer s = 5;
    integer k, last;

    analog function integer rnd;
        input dummy;
        integer dummy;
        begin
            rnd = $random();
        end
    endfunction

    analog begin
        I(a) <+ $random();
        I(b) <+ $arandom(seed + 1);
        I(c) <+ $random(s);
        I(d) <+ p;
        I(e) <+ x;
        I(f) <+ $arandom(s, "global");
        I(g) <+ rnd(0);
        I(h) <+ rnd(1);
        for (k = 0; k < 10; k = k + 1)
            last = $arandom(17);
        I(l) <+ last;
    end
endmodule
"#;

/// With full Verilog-A (`-s`) `$random()`, `$arandom()` and `$arandom(constant)` keep
/// the generator state as hidden state, `$random(var)` in the variable. Each generator
/// advances once per executed call (10 times per evaluation in the loop), the advanced
/// state is kept only by an accepted evaluation. Generators without a seed are seeded with
/// the entity seed mixed with their site id (each inlined function call gets its own).
/// In initializers `$arandom(constant)` gives the first value of the sequence.
/// Typed calls return 0.
pub fn generators() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    let tmp_dir = Utf8PathBuf::try_from(std::env::temp_dir())?;
    let root_file = tmp_dir.join("openvaf_random_test.va");
    std::fs::write(&root_file, SRC)?;
    let libs = compile_and_load_modules(&root_file, false);
    assert_eq!(libs.len(), 1);
    let desc = &libs[0];

    for entity_seed in [0, 12345, 0xdead_beef] {
        let model = desc.new_model();
        model.process_params()?;
        let mut instance = model.new_instance();
        instance.entity_seed = entity_seed;
        let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;

        // node, generator state, calls per evaluation (site ids: a 0, b 1, g 2, h 3, l 4)
        let mut states = [
            ("a", site_seed(entity_seed, 0), 1),
            ("b", 8, 1),
            ("c", 5, 1),
            ("g", site_seed(entity_seed, 2), 1),
            ("h", site_seed(entity_seed, 3), 1),
            ("l", 17, 10),
        ];
        let constants = [("d", value(next(11))), ("e", value(next(13))), ("f", 0)];

        for step in 1..=3 {
            let t = step as f64 * 1e-6;
            sim.abstime = t;
            sim.dt = 1e-6;
            for (_, state, calls) in &mut states {
                for _ in 0..*calls {
                    *state = next(*state);
                }
            }
            // without accept the generators do not advance
            for _ in 0..2 {
                sim.clear();
                instance.eval(&model, &mut sim, EvalFlags::ANALYSIS_TRAN);
                instance.load_dae(&model, &mut sim);
                for &(node, state, _) in &states {
                    let expected = value(state) as f64;
                    assert_eq!(sim.read_residual(node).0, expected, "{node} step {step}");
                }
                for &(node, expected) in &constants {
                    assert_eq!(sim.read_residual(node).0, expected as f64, "{node} step {step}");
                }
            }
            instance.accept(&model, t, 1e-6);
        }
    }
    Ok(())
}

/// One step of the IEEE 1364-2005 `$random` (`rtl_dist_uniform(seed, INT32_MIN, INT32_MAX)`),
/// returns the new seed and the value
fn ieee_random(seed: i32) -> (i32, i32) {
    let old = match seed as u32 {
        0 => 259_341_593,
        seed => seed,
    };
    let new = 69069u32.wrapping_mul(old).wrapping_add(1);
    // uniform(seed, INT32_MIN, INT32_MAX)
    let (a, b) = (i32::MIN as f64, i32::MAX as f64);
    let d = 0.00000011920928955078125;
    let c = 1.0 + (new >> 9) as f64 * 0.00000011920928955078125;
    let c = c + c * d;
    let u = (b - a) * (c - 1.0) + a;
    let r = (u + 2147483648.0) / 4294967295.0;
    let r = r * 4294967296.0 - 2147483648.0;
    let i = if r >= 0.0 { r as i64 } else { (r - 1.0) as i64 };
    (new as i32, i as u32 as i32)
}

/// With `--ieee1364` `$random(var)` and `$arandom(constant)` use the IEEE 1364-2005
/// generator.
pub fn ieee1364() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    const SRC: &str = r#"`include "disciplines.vams"
module random_ieee(a, b);
    inout a, b;
    electrical a, b;
    integer s = 0;
    analog begin
        I(a) <+ $random(s);
        I(b) <+ $arandom(5);
    end
endmodule
"#;
    let tmp_dir = Utf8PathBuf::try_from(std::env::temp_dir())?;
    let root_file = tmp_dir.join("openvaf_random_ieee_test.va");
    std::fs::write(&root_file, SRC)?;
    let mut opts = compile_opts(&root_file, false);
    opts.ieee1364 = true;
    let libs = compile_and_load_modules_with(&opts);
    assert_eq!(libs.len(), 1);
    let desc = &libs[0];
    let model = desc.new_model();
    model.process_params()?;
    let mut instance = model.new_instance();
    let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;

    let mut states = [("a", 0), ("b", 5)];
    for step in 1..=3 {
        let t = step as f64 * 1e-6;
        sim.abstime = t;
        sim.dt = 1e-6;
        sim.clear();
        instance.eval(&model, &mut sim, EvalFlags::ANALYSIS_TRAN);
        instance.load_dae(&model, &mut sim);
        for (node, state) in &mut states {
            let (next, value) = ieee_random(*state);
            assert_eq!(sim.read_residual(node).0, value as f64, "{node} step {step}");
            *state = next;
        }
        instance.accept(&model, t, 1e-6);
    }
    Ok(())
}

/// A voltage contribution that is zero after optimization but not a literal zero (a
/// typed `$arandom`, `1 - 1`) has no collapse hint. It keeps its branch equation
/// `V = 0` with the branch current as unknown.
pub fn zero_voltage() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    const SRC: &str = r#"`include "disciplines.vams"
module zero_voltage(d, e);
    output d, e;
    electrical d, e;
    analog begin
        V(d) <+ $arandom(12345, "instance");
        V(e) <+ 1 - 1;
    end
endmodule
"#;
    let tmp_dir = Utf8PathBuf::try_from(std::env::temp_dir())?;
    let root_file = tmp_dir.join("openvaf_random_zero_voltage_test.va");
    std::fs::write(&root_file, SRC)?;
    let libs = compile_and_load_modules(&root_file, true);
    assert_eq!(libs.len(), 1);
    let desc = &libs[0];
    let model = desc.new_model();
    model.process_params()?;
    let mut instance = model.new_instance();
    let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;

    for (node, v) in [("d", 0.3), ("e", 0.2)] {
        sim.set_voltage(node, v);
    }
    instance.eval(&model, &mut sim, EvalFlags::empty());
    instance.load_dae(&model, &mut sim);
    for (node, v) in [("d", 0.3), ("e", 0.2)] {
        let flow = format!("flow({node})");
        // branch equation: 0 - V(node)
        assert_eq!(sim.read_residual(&flow), (-v, 0.0), "{node}");
        assert_eq!(sim.read_jacobian(&flow, node), (-1.0, 0.0), "{node}");
        // KCL: the branch current flows out of the node
        assert_eq!(sim.read_jacobian(node, &flow), (1.0, 0.0), "{node}");
    }
    Ok(())
}

fn module(name: &str, decls: &str, initial: &str, analog: &str) -> String {
    format!(
        r#"`include "disciplines.vams"
module {name}(a);
    inout a;
    electrical a;
    parameter integer seed = 7;
    integer s = 1;
    real r = 1.0;
{decls}
    analog initial begin
{initial}
    end

    analog begin
{analog}
    end
endmodule
"#
    )
}

/// Illegal calls are compile errors. Without `-s` only typed calls are allowed.
pub fn errors() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    const RND: &str = "
    analog function integer rnd;
        input dummy;
        integer dummy;
        begin
            rnd = $random();
        end
    endfunction
";
    const RND_X: &str = "
    analog function integer rnd;
        input dummy;
        integer dummy;
        begin
            rnd = $random();
        end
    endfunction
    integer x = rnd(0);
";

    // (decls, analog initial, analog, compiles without -s, compiles with -s)
    let cases = [
        ("", "", "I(a) <+ $random();", false, true),
        ("", "", "I(a) <+ $random(s);", false, true),
        ("", "", "I(a) <+ $arandom(seed);", false, true),
        ("", "", "I(a) <+ $arandom(s, \"instance\");", true, true),
        ("", "s = $arandom(3, \"global\");", "I(a) <+ s;", true, true),
        ("", "", "I(a) <+ $arandom(1, \"local\");", false, false),
        ("", "", "I(a) <+ $arandom(r);", false, false),
        ("", "s = $random(s);", "I(a) <+ s;", false, false),
        (RND, "", "I(a) <+ rnd(0);", false, true),
        (RND, "s = rnd(0);", "I(a) <+ s;", false, false),
        ("parameter integer p = $arandom(seed);", "", "I(a) <+ p;", false, true),
        ("parameter integer p = $arandom(seed, \"global\");", "", "I(a) <+ p;", true, true),
        ("parameter integer p = $arandom();", "", "I(a) <+ p;", false, false),
        ("integer x = $arandom(seed * 2);", "", "I(a) <+ x;", false, true),
        ("integer x = $arandom();", "", "I(a) <+ x;", false, false),
        (RND_X, "", "I(a) <+ x;", false, false),
    ];

    let tmp_dir = Utf8PathBuf::try_from(std::env::temp_dir())?;
    for (i, (decls, initial, analog, compact_ok, full_ok)) in cases.into_iter().enumerate() {
        let name = format!("random_errors_{i}");
        let root_file = tmp_dir.join(format!("openvaf_{name}.va"));
        std::fs::write(&root_file, module(&name, decls, initial, analog))?;
        assert_eq!(
            compiles(&root_file, true),
            compact_ok,
            "case {i} without -s: {decls} {initial} {analog}"
        );
        assert_eq!(
            compiles(&root_file, false),
            full_ok,
            "case {i} with -s: {decls} {initial} {analog}"
        );
    }
    Ok(())
}
