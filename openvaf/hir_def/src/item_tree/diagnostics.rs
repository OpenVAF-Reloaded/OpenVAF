use basedb::diagnostics::{Diagnostic, Label, LabelStyle, Report};
use basedb::{AstIdMap, BaseDB, FileId};
use syntax::sourcemap::SourceMap;
use syntax::{Parse, SourceFile};

use super::ItemTreeDiagnostic;

pub struct ItemTreeDiagnosticWrapped<'a> {
    pub diag: &'a ItemTreeDiagnostic,
    pub parse: &'a Parse<SourceFile>,
    pub sm: &'a SourceMap,
    pub ast_id_map: &'a AstIdMap,
}

impl Diagnostic for ItemTreeDiagnosticWrapped<'_> {
    fn build_report(&self, _root_file: FileId, _db: &dyn BaseDB) -> Report {
        match self.diag {
            ItemTreeDiagnostic::NonConstantBusWidth { ast_id } => {
                let range = self.ast_id_map.get_syntax(*ast_id).range();
                let span = self.parse.to_file_span(range, self.sm);
                Report::error()
                    .with_message("bus width `[msb:lsb]` is not a constant expression")
                    .with_labels(vec![Label {
                        style: LabelStyle::Primary,
                        file_id: span.file,
                        range: span.range.into(),
                        message: "expected a constant integer expression on both sides of ':'"
                            .to_owned(),
                    }])
                    .with_notes(vec![
                        "help: only integer literals (optionally unary-negated) are supported \
                         here; the declaration was treated as a single scalar net/port"
                            .to_owned(),
                    ])
            }
            ItemTreeDiagnostic::BareBusReferenceInBranch { ast_id, bus_name } => {
                let range = self.ast_id_map.get_syntax(*ast_id).range();
                let span = self.parse.to_file_span(range, self.sm);
                Report::error()
                    .with_message(format!(
                        "bus '{bus_name}' requires a bit-select [i]"
                    ))
                    .with_labels(vec![Label {
                        style: LabelStyle::Primary,
                        file_id: span.file,
                        range: span.range.into(),
                        message: format!(
                            "'{bus_name}' is a vectored net; a single bit must be selected"
                        ),
                    }])
                    .with_notes(vec![format!(
                        "help: use '{bus_name}[i]' to select a single bit of the bus"
                    )])
            }
            ItemTreeDiagnostic::NonConstantBranchBitSelect { ast_id } => {
                let range = self.ast_id_map.get_syntax(*ast_id).range();
                let span = self.parse.to_file_span(range, self.sm);
                Report::error()
                    .with_message("bit-select index is not a constant expression")
                    .with_labels(vec![Label {
                        style: LabelStyle::Primary,
                        file_id: span.file,
                        range: span.range.into(),
                        message: "expected a constant integer literal index".to_owned(),
                    }])
                    .with_notes(vec![
                        "help: only integer literals (optionally unary-negated) are supported \
                         as bit-select indices"
                            .to_owned(),
                    ])
            }
            ItemTreeDiagnostic::BranchBitSelectOutOfRange { ast_id, bus_name, index, msb, lsb } => {
                let range = self.ast_id_map.get_syntax(*ast_id).range();
                let span = self.parse.to_file_span(range, self.sm);
                Report::error()
                    .with_message(format!(
                        "bit-select index {index} is out of range for bus '{bus_name}[{msb}:{lsb}]'"
                    ))
                    .with_labels(vec![Label {
                        style: LabelStyle::Primary,
                        file_id: span.file,
                        range: span.range.into(),
                        message: format!(
                            "'{bus_name}' was declared with range [{msb}:{lsb}]"
                        ),
                    }])
                    .with_notes(vec![format!(
                        "help: valid bit-select indices for '{bus_name}' are between {} and {}",
                        msb.min(lsb),
                        msb.max(lsb)
                    )])
            }
        }
    }
}
