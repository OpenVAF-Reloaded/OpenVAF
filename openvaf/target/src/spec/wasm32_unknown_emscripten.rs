use crate::spec::{LinkerFlavor, Target, TargetOptions};

/// WebAssembly side module for Emscripten dynamic linking (Pyodide).
///
/// The output is a PIC wasm module with a `dylink.0` section that the
/// Emscripten runtime loads with `dlopen`. Undefined symbols (libc/libm,
/// e.g. `malloc`, `exp`, `snprintf`) are imported from the main module.
pub fn target() -> Target {
    let mut options = TargetOptions { linker_flavor: LinkerFlavor::WasmLd, ..Default::default() };
    // Mirrors `emcc -sSIDE_MODULE=1` (Emscripten 4.0.x) without the
    // Emscripten-specific exports and the optional wasm-opt pass.
    options.pre_link_args.insert(
        LinkerFlavor::WasmLd,
        [
            "--experimental-pic",
            "-shared",
            "--import-memory",
            "--strip-debug",
            "--export-dynamic",
            "--unresolved-symbols=import-dynamic",
            "--export-if-defined=__wasm_apply_data_relocs",
            "--export=__wasm_call_ctors",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect(),
    );
    Target {
        llvm_target: "wasm32-unknown-emscripten".to_string(),
        pointer_width: 32,
        data_layout: "e-m:e-p:32:32-p10:8:8-p20:8:8-i64:64-i128:128-f128:64-n32:64-S128-ni:1:10:20"
            .to_string(),
        arch: "wasm32".to_string(),
        options,
    }
}
