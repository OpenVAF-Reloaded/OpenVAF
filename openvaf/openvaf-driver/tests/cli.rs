use std::env;
use std::path::PathBuf;

use mini_harness::{harness, Result};
use stdx::{ignore_never, project_root};

// Adapted from
// https://github.com/rust-lang/cargo/blob/485670b3983b52289a2f353d589c57fae2f60f82/tests/testsuite/support/mod.rs#L507
pub fn target_dir() -> PathBuf {
    env::current_exe()
        .ok()
        .map(|mut path| {
            path.pop();
            if path.ends_with("deps") {
                path.pop();
            }
            path
        })
        .unwrap()
}

/// Returns the path of a binary build by cargo
pub fn cargo_bin(name: &str) -> PathBuf {
    let env_var = format!("CARGO_BIN_EXE_{}", name);
    std::env::var_os(env_var)
        .map(|p| p.into())
        .unwrap_or_else(|| target_dir().join(format!("{}{}", name, env::consts::EXE_SUFFIX)))
}

fn smoke_test(args: &str) -> Result {
    let args = args.split(' ');
    let sh = xshell::Shell::new().unwrap();
    sh.change_dir(project_root());
    let openvaf = cargo_bin("openvaf-r");
    xshell::cmd!(sh, "{openvaf} --dry-run {args...} integration_tests/DIODE/diode.va").run()?;
    Ok(())
}

fn link_diode() -> Result {
    let sh = xshell::Shell::new().unwrap();
    sh.change_dir(project_root());
    let openvaf = cargo_bin("openvaf-r");
    xshell::cmd!(sh, "{openvaf} -O 0 integration_tests/DIODE/diode.va").run()?;
    sh.remove_path("integration_tests/DIODE/diode.osdi").unwrap();
    Ok(())
}

/// Whether a WebAssembly linker can be found, the same way the linker crate
/// looks for one (OPENVAF_WASM_LD, $EMSDK/upstream/bin/wasm-ld, wasm-ld).
fn have_wasm_ld() -> bool {
    let mut candidates: Vec<PathBuf> = Vec::new();
    if let Some(path) = env::var_os("OPENVAF_WASM_LD") {
        candidates.push(path.into());
    }
    if let Some(emsdk) = env::var_os("EMSDK") {
        candidates.push(PathBuf::from(emsdk).join("upstream").join("bin").join("wasm-ld"));
    }
    candidates.push("wasm-ld".into());
    candidates.iter().any(|ld| {
        std::process::Command::new(ld)
            .arg("--version")
            .output()
            .map_or(false, |out| out.status.success())
    })
}

/// Links the diode as an Emscripten side module (Pyodide). Skipped when no
/// wasm-ld is installed, e.g. without the Emscripten SDK.
fn link_diode_wasm() -> Result {
    if !have_wasm_ld() {
        eprintln!("skipping cli::link_diode_wasm: wasm-ld not found");
        return Ok(());
    }
    let sh = xshell::Shell::new().unwrap();
    sh.change_dir(project_root());
    let openvaf = cargo_bin("openvaf-r");
    let out = target_dir().join("diode_wasm32.osdi");
    xshell::cmd!(
        sh,
        "{openvaf} -O 0 --target wasm32-unknown-emscripten integration_tests/DIODE/diode.va -o {out}"
    )
    .run()?;
    let module = sh.read_binary_file(&out)?;
    sh.remove_path(&out)?;
    // Wasm magic and version, then the dylink.0 custom section that makes it
    // loadable as a side module (it must come first).
    assert_eq!(&module[..8], b"\0asm\x01\0\0\0", "not a WebAssembly module");
    assert_eq!(module[8], 0, "first section is not a custom section");
    assert!(module[9..20].windows(8).any(|w| w == b"dylink.0"), "no dylink.0 section");
    // The library must not refer to its own symbols through the GOT: the
    // Emscripten dynamic linker resolves GOT entries globally by name, so they
    // would bind to the symbols of the first OSDI library that was loaded.
    for got in [&b"GOT.func"[..], &b"GOT.mem"[..]] {
        assert!(
            !module.windows(got.len()).any(|w| w == got),
            "imports from {}",
            String::from_utf8_lossy(got)
        );
    }
    Ok(())
}

harness! {
    Test::new("cli::link_diode", &link_diode),
    Test::new("cli::link_diode_wasm", &link_diode_wasm),
    Test::from_list(
        "cli::smoke_test",
         &smoke_test,
         &ignore_never,
         &[
            "--target_cpu generic",
            "--target_cpu skylake",
             // "--dump-json",
             "--supported-targets",
             "--batch",
             "--batch --cache-dir sourcegen",
             "-O 0",
             "-O 1",
             "-O 2",
             "-O 3",
             "-I sourcegen",
             "-D foo",
             "--print-expansion",
             "--supported-targets",
             "--lints",
             "-D all",
             "-D warnings",
             "-D macro_overwritten",
             "-W errors",
             "-W all",
             "-W macro_overwritten",
             "-A errors",
             "-A warnings",
             "-A all",
             "-A macro_overwritten",
        ]
    )
}
