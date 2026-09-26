use std::env;
use std::ffi::{OsStr, OsString};
use std::fmt::Display;
use std::path::Path;

use target::spec::get_targets;
use xshell::{cmd, Shell};

/// Reads an environment variable and adds it to dependencies.
/// Supposed to be used for all variables except those set for build scripts by cargo
/// <https://doc.rust-lang.org/cargo/reference/environment-variables.html#environment-variables-cargo-sets-for-build-scripts>
fn tracked_env_var_os<K: AsRef<OsStr> + Display>(key: K) -> Option<OsString> {
    println!("cargo:rerun-if-env-changed={}", key);
    env::var_os(key)
}

fn main() {
    // If we're just running `check`, there's no need to actually compute the stdlib just
    // populate dummies
    let no_gen = tracked_env_var_os("RUST_CHECK").is_some();
    let sh = Shell::new().unwrap();
    let osdi_dir = stdx::project_root().join("openvaf").join("osdi");
    let src_file = osdi_dir.join("stdlib.c");

    // Use clang from LLVM prefix environment variables (check newest first)
    // Fall back to Homebrew LLVM on macOS, then system clang
    let clang_path = tracked_env_var_os("LLVM_SYS_221_PREFIX")
        .or_else(|| tracked_env_var_os("LLVM_SYS_211_PREFIX"))
        .or_else(|| tracked_env_var_os("LLVM_SYS_201_PREFIX"))
        .or_else(|| tracked_env_var_os("LLVM_SYS_191_PREFIX"))
        .or_else(|| tracked_env_var_os("LLVM_SYS_181_PREFIX"))
        .map(|prefix| Path::new(&prefix).join("bin/clang"))
        .and_then(|path| path.exists().then_some(path))
        .or_else(|| {
            // Try Homebrew LLVM paths on macOS
            #[cfg(target_os = "macos")]
            {
                // Check HOMEBREW_PREFIX first, then common default locations
                if let Some(prefix) = tracked_env_var_os("HOMEBREW_PREFIX") {
                    let p = Path::new(&prefix).join("opt/llvm/bin/clang");
                    if p.exists() {
                        return Some(p);
                    }
                }
                let homebrew_paths = [
                    "/opt/homebrew/opt/llvm/bin/clang", // Apple Silicon
                    "/usr/local/opt/llvm/bin/clang",    // Intel Mac
                ];
                for path in homebrew_paths {
                    let p = Path::new(path);
                    if p.exists() {
                        return Some(p.to_path_buf());
                    }
                }
            }
            None
        })
        .map(|path| path.display().to_string())
        .unwrap_or_else(|| "clang".to_string());

    sh.change_dir(osdi_dir);
    for file in sh.read_dir("header").unwrap() {
        if file.extension().map_or(true, |ext| ext != "h")
            || !file
                .file_stem()
                .and_then(|name| name.to_str())
                .map_or(false, |name| name.starts_with("osdi_"))
        {
            continue;
        }

        let name = file.file_stem().unwrap().to_str().unwrap();
        let def_name = name.to_uppercase();
        let version_str = name.strip_prefix("osdi_").unwrap();

        let out_dir = env::var_os("OUT_DIR").unwrap();
        for target in get_targets() {
            let target_name = &target.llvm_target;
            let out_file =
                Path::new(&out_dir).join(&format!("stdlib_{version_str}_{target_name}.bc"));
            if no_gen {
                sh.write_file(out_file, []).expect("failed to write dummy file");
            } else {
                println!("cargo:rerun-if-changed={}", file.display());

                let mut cmd = cmd!(sh, "{clang_path} -emit-llvm -O3 -D{def_name} -DNO_STD -o {out_file} -c {src_file} -target {target_name}");
                if !target.options.is_like_windows {
                    cmd = cmd.arg("-fPIC");
                }
                cmd.run().expect("failed to generate bitcode");
            }
        }
    }

    println!("cargo:rerun-if-changed={}", src_file.display());
}
