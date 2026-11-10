//! `$random`/`$arandom`: generator sequences (checked against a reimplementation of
//! the stdlib generator) and the compile errors of illegal calls.

use camino::Utf8PathBuf;
use mini_harness::Result;

use crate::load::EvalFlags;
use crate::{compile_and_load_modules, compiles};

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
    match mix32(entity_seed, site_id) {
        0 => 1,
        seed => seed as i32,
    }
}

/// Next state of a generator
fn next(state: i32) -> i32 {
    let state = match state as u32 {
        0 => 259_341_593,
        state => state,
    };
    69069u32.wrapping_mul(state).wrapping_add(1) as i32
}

/// Random value of a generator state
fn value(state: i32) -> i32 {
    fmix32(state as u32) as i32
}

const SRC: &str = r#"`include "disciplines.vams"
module random_test(a, b, c, d, e, f, g, h);
    inout a, b, c, d, e, f, g, h;
    electrical a, b, c, d, e, f, g, h;
    parameter integer seed = 7;
    parameter integer p = $arandom(11);
    integer x = $arandom(13);
    integer s = 5;

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
    end
endmodule
"#;

/// With full Verilog-A (`-s`) `$random()`, `$arandom()` and `$arandom(constant)` keep
/// the generator state as hidden state, `$random(var)` in the variable. Each generator
/// advances once per accepted evaluation. Generators without a seed are seeded with
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

        // node, generator state (site ids: a 0, b 1, g 2, h 3)
        let mut states = [
            ("a", site_seed(entity_seed, 0)),
            ("b", 8),
            ("c", 5),
            ("g", site_seed(entity_seed, 2)),
            ("h", site_seed(entity_seed, 3)),
        ];
        let constants = [("d", value(next(11))), ("e", value(next(13))), ("f", 0)];

        for step in 1..=3 {
            let t = step as f64 * 1e-6;
            sim.abstime = t;
            sim.dt = 1e-6;
            for (_, state) in &mut states {
                *state = next(*state);
            }
            // without accept the generators do not advance
            for _ in 0..2 {
                sim.clear();
                instance.eval(&model, &mut sim, EvalFlags::ANALYSIS_TRAN);
                instance.load_dae(&model, &mut sim);
                for &(node, state) in &states {
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
