use std::ops::Deref;

use basedb::diagnostics::{Diagnostic, Label, LabelStyle, Report};
use basedb::lints::{self, Lint, LintSrc};
use basedb::{AstIdMap, BaseDB, ErasedAstId, FileId};
use stdx::{impl_display, pretty};
use syntax::name::Name;
use syntax::sourcemap::{FileSpan, SourceMap};
use syntax::{Parse, SourceFile};

use super::{ResolvedPath, ScopeDefItem};
use crate::db::HirDefDB;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathResolveError {
    NotFound { name: Name },
    NotFoundIn { name: Name, scope: Name },
    ExpectedScope { name: Name, found: ScopeDefItem },
    ExpectedItemKind { name: Name, expected: &'static str, found: ResolvedPath },
    ExpectedNatureAttributeIdent { found: Box<[Name]> },
}

impl_display! {
    match PathResolveError{
        PathResolveError::NotFound {name} => "'{}' was not found in the current scope", name;
        PathResolveError::NotFoundIn {name, scope} => "'{}' was not found in '{}'", name, scope;
        PathResolveError::ExpectedScope {name, found} => "expected a scope but found {} '{}'", found.item_kind(), name;
        PathResolveError::ExpectedItemKind{name, expected, found} => "expected {} but found {} '{}'", expected, found, name;
        PathResolveError::ExpectedNatureAttributeIdent{found} => "expected a nature attribute identifier found path {}",  pretty::List::path(found.deref());
    }
}

impl PathResolveError {
    pub fn message(&self) -> String {
        match self {
            PathResolveError::NotFound { .. } | PathResolveError::NotFoundIn { .. } => {
                "not found".to_owned()
            }
            PathResolveError::ExpectedScope { .. }
            | PathResolveError::ExpectedNatureAttributeIdent { .. } => {
                "failed to resolve path".to_owned()
            }
            PathResolveError::ExpectedItemKind { expected, .. } => format!("expected {}", expected),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum DefDiagnostic {
    AlreadyDeclared {
        old: ScopeDefItem,
        new: ScopeDefItem,
        name: Name,
    },
    /// A module instantiation (`resistor r1(...)`) referenced a module name
    /// that doesn't exist anywhere at the top level of this file.
    UnknownInstantiatedModule {
        ast_id: ErasedAstId,
        module: Name,
    },
    /// An instantiation's port-connection list has a different length than
    /// the instantiated module's port list (only checked for a fully
    /// positional connection list, where the count must match exactly).
    InstancePortCountMismatch {
        ast_id: ErasedAstId,
        instance: Name,
        module: Name,
        expected: usize,
        found: usize,
    },
    /// A named port connection (`.p(net)`) named a port that the
    /// instantiated module doesn't declare.
    UnknownInstancePort {
        ast_id: ErasedAstId,
        instance: Name,
        module: Name,
        port: Name,
    },
    /// A named parameter override (`#(.r(1e3))`) named a parameter that the
    /// instantiated module doesn't declare.
    UnknownInstanceParam {
        ast_id: ErasedAstId,
        instance: Name,
        module: Name,
        param: Name,
    },
    /// A positional parameter-override list is longer than the number of
    /// parameters the instantiated module declares.
    TooManyInstanceParams {
        ast_id: ErasedAstId,
        instance: Name,
        module: Name,
        expected: usize,
        found: usize,
    },
    /// Module instantiation forms a cycle (directly or transitively
    /// instantiates itself), which isn't a physically meaningful circuit
    /// and can't be flattened.
    CyclicInstantiation {
        ast_id: ErasedAstId,
        module: Name,
    },
    /// A top-level module's name collides with one of ngspice's built-in
    /// native SPICE device type names (e.g. `resistor`, case-insensitive).
    /// `.model <name> <this module>` then silently binds to ngspice's
    /// built-in device instead of the OSDI one -- a real, easy-to-hit
    /// footgun once a module is meant to be `.model`-able directly (rather
    /// than only reached through `instantiate`), so it's a lint
    /// (`reserved_module_name`, warn by default) rather than a hard error:
    /// nothing is actually wrong with the Verilog-A itself.
    ReservedModuleName {
        ast_id: ErasedAstId,
        module: Name,
        builtin: &'static str,
    },
}

pub struct DefDiagnosticWrapped<'a> {
    pub db: &'a dyn HirDefDB,
    pub diag: &'a DefDiagnostic,
    pub parse: &'a Parse<SourceFile>,
    pub sm: &'a SourceMap,
    pub ast_id_map: &'a AstIdMap,
}

impl Diagnostic for DefDiagnosticWrapped<'_> {
    fn build_report(&self, _root_file: FileId, _db: &dyn BaseDB) -> Report {
        match self.diag {
            DefDiagnostic::AlreadyDeclared { old, new, name } => {
                let FileSpan { range, file } = self.parse.to_file_span(
                    new.text_range(self.db, self.ast_id_map, self.parse).unwrap(),
                    self.sm,
                );

                let mut labels = vec![Label {
                    style: LabelStyle::Primary,
                    file_id: file,
                    range: range.into(),
                    message: "already declared in this scope".to_owned(),
                }];

                if let Some(def) = old.text_range(self.db, self.ast_id_map, self.parse) {
                    let FileSpan { range, file } = self.parse.to_file_span(def, self.sm);
                    labels.push(Label {
                        style: LabelStyle::Secondary,
                        file_id: file,
                        range: range.into(),
                        message: format!("help '{}' was first declared here", name),
                    })
                }
                Report::error()
                    .with_message(format!("'{}' was already declared in this scope", name))
                    .with_labels(labels)
            }
            DefDiagnostic::UnknownInstantiatedModule { ast_id, module } => {
                let range = self.ast_id_map.get_syntax(*ast_id).range();
                let span = self.parse.to_file_span(range, self.sm);
                Report::error().with_message(format!("unknown module '{module}'")).with_labels(
                    vec![Label {
                        style: LabelStyle::Primary,
                        file_id: span.file,
                        range: span.range.into(),
                        message: format!("no module named '{module}' was found in this file"),
                    }],
                )
            }
            DefDiagnostic::InstancePortCountMismatch {
                ast_id,
                instance,
                module,
                expected,
                found,
            } => {
                let range = self.ast_id_map.get_syntax(*ast_id).range();
                let span = self.parse.to_file_span(range, self.sm);
                Report::error()
                    .with_message(format!(
                        "instance '{instance}' of module '{module}' has {found} port \
                         connection(s), expected {expected}"
                    ))
                    .with_labels(vec![Label {
                        style: LabelStyle::Primary,
                        file_id: span.file,
                        range: span.range.into(),
                        message: format!("'{module}' declares {expected} port(s)"),
                    }])
            }
            DefDiagnostic::UnknownInstancePort { ast_id, instance, module, port } => {
                let range = self.ast_id_map.get_syntax(*ast_id).range();
                let span = self.parse.to_file_span(range, self.sm);
                Report::error()
                    .with_message(format!(
                        "module '{module}' has no port named '{port}' (instance '{instance}')"
                    ))
                    .with_labels(vec![Label {
                        style: LabelStyle::Primary,
                        file_id: span.file,
                        range: span.range.into(),
                        message: format!("'{port}' is not a port of '{module}'"),
                    }])
            }
            DefDiagnostic::UnknownInstanceParam { ast_id, instance, module, param } => {
                let range = self.ast_id_map.get_syntax(*ast_id).range();
                let span = self.parse.to_file_span(range, self.sm);
                Report::error()
                    .with_message(format!(
                        "module '{module}' has no parameter named '{param}' (instance '{instance}')"
                    ))
                    .with_labels(vec![Label {
                        style: LabelStyle::Primary,
                        file_id: span.file,
                        range: span.range.into(),
                        message: format!("'{param}' is not a parameter of '{module}'"),
                    }])
            }
            DefDiagnostic::TooManyInstanceParams { ast_id, instance, module, expected, found } => {
                let range = self.ast_id_map.get_syntax(*ast_id).range();
                let span = self.parse.to_file_span(range, self.sm);
                Report::error()
                    .with_message(format!(
                        "instance '{instance}' of module '{module}' has {found} positional \
                         parameter override(s), but '{module}' only declares {expected}"
                    ))
                    .with_labels(vec![Label {
                        style: LabelStyle::Primary,
                        file_id: span.file,
                        range: span.range.into(),
                        message: "too many positional parameter overrides".to_owned(),
                    }])
            }
            DefDiagnostic::CyclicInstantiation { ast_id, module } => {
                let range = self.ast_id_map.get_syntax(*ast_id).range();
                let span = self.parse.to_file_span(range, self.sm);
                Report::error()
                    .with_message(format!(
                        "module '{module}' instantiates itself (directly or transitively)"
                    ))
                    .with_labels(vec![Label {
                        style: LabelStyle::Primary,
                        file_id: span.file,
                        range: span.range.into(),
                        message: "this instantiation creates a cycle".to_owned(),
                    }])
                    .with_notes(vec![
                        "help: a module cannot instantiate itself, directly or through a chain \
                         of other modules, since there would be no way to flatten it into a \
                         finite circuit"
                            .to_owned(),
                    ])
            }
            DefDiagnostic::ReservedModuleName { ast_id, module, builtin } => {
                let range = self.ast_id_map.get_syntax(*ast_id).range();
                let span = self.parse.to_file_span(range, self.sm);
                Report::warning()
                    .with_message(format!(
                        "module name '{module}' collides with ngspice's built-in '{builtin}' device"
                    ))
                    .with_labels(vec![Label {
                        style: LabelStyle::Primary,
                        file_id: span.file,
                        range: span.range.into(),
                        message: format!("'{module}' matches a built-in ngspice device name"),
                    }])
                    .with_notes(vec![format!(
                        "help: `.model <name> {module}` in a SPICE netlist may silently bind to \
                         ngspice's built-in '{builtin}' device instead of this OSDI module; \
                         rename '{module}' to something that doesn't collide, or only ever \
                         reach it via Verilog-A `instantiate`, never `.model` directly"
                    )])
            }
        }
    }

    fn lint(&self, _root_file: FileId, _db: &dyn BaseDB) -> Option<(Lint, LintSrc)> {
        match *self.diag {
            DefDiagnostic::ReservedModuleName { ast_id, .. } => {
                Some((lints::builtin::reserved_module_name, LintSrc::item(ast_id)))
            }
            _ => None,
        }
    }
}
