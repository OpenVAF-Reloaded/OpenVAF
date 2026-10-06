use std::path::Path;

use basedb::lints::LintLevel;
use basedb::AbsPathBuf;
use expect_test::expect_file;
use hir::CompilationDB;
use mini_harness::{harness, Result};
use stdx::{ignore_dev_tests, ignore_never, is_va_file, openvaf_test_data, project_root};

fn integration_test(dir: &Path) -> Result {
    let name = dir.file_name().unwrap().to_str().unwrap().to_lowercase();
    let main_file = dir.join(format!("{name}.va"));

    let db =
        CompilationDB::new_fs(AbsPathBuf::assert(main_file.canonicalize().unwrap()), &[], &[], &[])
            .unwrap();
    expect_file![dir.join("frontend.log")].assert_eq(&db.compilation_unit().test_diagnostics(&db));

    Ok(())
}

/// Lint levels a UI test sets the way the command line does (`--warn <lint>` etc.),
/// for lints that are off by default.
fn cli_lints(file: &Path) -> Vec<(String, LintLevel)> {
    match file.file_stem().and_then(|stem| stem.to_str()) {
        Some("reserved_module_name") => vec![("reserved_module_name".to_owned(), LintLevel::Warn)],
        _ => Vec::new(),
    }
}

fn ui_test(file: &Path) -> Result {
    let db = CompilationDB::new_fs(
        AbsPathBuf::assert(file.canonicalize().unwrap()),
        &[],
        &[],
        &cli_lints(file),
    )
    .unwrap();
    let actual = db.compilation_unit().test_diagnostics(&db);
    expect_file![file.with_extension("log")].assert_eq(&actual);
    Ok(())
}

harness! {
    Test::from_dir_filtered("integration", &integration_test, &Path::is_dir, &ignore_dev_tests, &project_root().join("integration_tests")),
    Test::from_dir_filtered("ui", &ui_test, &is_va_file, &ignore_never, &openvaf_test_data("ui"))
}
