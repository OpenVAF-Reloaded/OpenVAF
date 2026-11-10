use std::fs;

use hir::diagnostics::ConsoleSink;
use hir::CompilationDB;
use lasso::Rodeo;
use stdx::openvaf_test_data;

use crate::context::Context;

/// Expected hidden state of each module in `hidden_state.va`.
///
/// The names follow the convention of the test file: `s_*` variables are
/// hidden state, `c_*` and `n_*` variables are not, and `p_*` variables depend
/// on policy (the expected result documents the current one).
fn expected_hidden_state(module: &str) -> &'static [&'static str] {
    match module {
        "hidden_state" => &[
            "p_case_par",
            "p_fcnt",
            "p_istep_marker",
            "p_loop_par",
            "s_acc",
            "s_ainit",
            "s_arr[0]",
            "s_arr[1]",
            "s_blkloc",
            "s_c1",
            "s_c2",
            "s_c3",
            "s_case_op",
            "s_chain_x",
            "s_chain_y",
            "s_cnt",
            "s_dep",
            "s_first",
            "s_fstep",
            "s_inner",
            "s_istep_acc",
            "s_istep_v0",
            "s_lag",
            "s_loopv",
            "s_str",
            "s_sticky",
            "s_swap1",
            "s_swap2",
            "s_trig",
        ],
        "hs_m1" | "hs_m2" | "hs_m3" | "hs_m4" | "hs_m5" | "hs_m6" => &[],
        "hs_ainit" => &["s_ainit_x"],
        _ => unreachable!("unknown module {module}"),
    }
}

/// A variable used as the seed of `$random(seed)` is hidden state, also next to an
/// unseeded `$random`. GVN used to merge different pure calls (the two random
/// callbacks), which disconnected `seed` from the output.
#[test]
fn hidden_state_random_seed() {
    let src = r#"`include "disciplines.vams"
module rnd(a, c);
    output a, c;
    electrical a, c;
    integer seed;
    analog initial begin
        seed = 12345;
    end
    analog begin
        V(a) <+ $random;
        V(c) <+ $random(seed);
    end
endmodule
"#;
    let mut db = CompilationDB::new_virtual(src).unwrap();
    db.set_full_semantics_flag(true);
    let modules = crate::collect_modules(&db, false, &mut ConsoleSink::new(&db)).unwrap();
    let mut literals = Rodeo::new();
    let found: Vec<String> = Context::detect_hidden_state(&db, &mut literals, &modules[0])
        .into_iter()
        .map(|var| var.name(&db).to_string())
        .collect();
    assert_eq!(found, ["seed"]);
}

#[test]
fn hidden_state() {
    let src =
        fs::read_to_string(openvaf_test_data("hidden_state").join("hidden_state.va")).unwrap();
    let db = CompilationDB::new_virtual(&src).unwrap();
    let modules = crate::collect_modules(&db, false, &mut ConsoleSink::new(&db)).unwrap();
    assert_eq!(modules.len(), 8);
    let mut literals = Rodeo::new();
    for module in &modules {
        let name = module.module.name(&db);
        let mut found: Vec<String> = Context::detect_hidden_state(&db, &mut literals, module)
            .into_iter()
            .map(|var| var.name(&db).to_string())
            .collect();
        found.sort();
        for var in &found {
            assert!(
                var.starts_with("s_") || var.starts_with("p_"),
                "{var} in module {name} is not hidden state"
            );
        }
        let mut expected = expected_hidden_state(&name).to_vec();
        expected.sort();
        assert_eq!(found, expected, "hidden state of module {name}");
    }
}
