fn main() {
    pyo3_build_config::add_extension_module_link_args();
    pyo3_build_config::use_pyo3_cfgs();

    // pyo3-ffi 0.29 links libpython on Windows via raw-dylib, but only for DLL names
    // like `python312`. MinGW (MSYS2) Python uses `python3.12`, which matches none of
    // them, so no link attribute is generated. Link it the traditional way instead.
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target_env = std::env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();
    if target_os == "windows" && target_env == "gnu" {
        let config = pyo3_build_config::get();
        if let Some(lib_name) = config.lib_name() {
            println!("cargo:rustc-link-lib=dylib={lib_name}");
        }
        if let Some(lib_dir) = config.lib_dir() {
            println!("cargo:rustc-link-search=native={lib_dir}");
        }
    }
}
