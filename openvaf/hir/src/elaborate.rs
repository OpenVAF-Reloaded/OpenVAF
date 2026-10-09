//! Module-instantiation elaboration: a text-level "flattening" pass that
//! turns `resistor #(.r(1e3)) r1(in, out);`-style instantiation statements
//! into an ordinary, hand-written-looking flat module, by textually
//! inlining the referenced module's own declarations (alpha-renamed with a
//! per-instance prefix, with ports/parameters bound to the instantiation's
//! actual arguments) in place of the instantiation statement.
//!
//! This runs once, eagerly, right after a [`CompilationDB`] is constructed
//! (see [`elaborate_instantiations`]), entirely as ordinary Rust code
//! operating on the already-working `db`/`root_file` -- it does not hook
//! into the salsa `parse`/`preprocess` query chain. If elaboration produces
//! new text, it is registered as a new virtual file in the database's
//! `Vfs` and `db.root_file` is redirected to it; every downstream stage
//! (`hir_def`, `hir_ty`, `hir_lower`, `mir*`, `sim_back`, `osdi`) then sees
//! what looks like an ordinary flat file and requires zero changes.
//!
//! Known limitation: diagnostics for code that originated inside an
//! inlined instance point at the synthesized flattened file, not the
//! original module's source location (no cross-file span provenance is
//! tracked, unlike the `` `include``/macro-expansion machinery in
//! `preprocessor::sourcemap`, which this pass deliberately does not hook
//! into -- see `Enhancement-5.md` for the rationale).
//!
//! Bus port actuals may be whole buses or constant part-selects. Bindings
//! are built in declaration order, retaining the direction of both ranges.
//! Explicit slices are width/bounds checked rather than broadcast as text.
//! Scalar instance-array ports retain the matching-width bus heuristic.
//!
//! A bus *port* needs a different substitution mechanism than everything
//! else in this pass: an ordinary rename (`p` -> `prefix__p`) is a single
//! whole-token substitution, but a bus port's bit 0 and bit 1 need to
//! become *different* identities (e.g. `a[0]`/`a[1]`), and the source text
//! only ever contains the bare base identifier (`p`) with the bit-select
//! (`[0]`) as separate tokens right after it -- there is no single token
//! to look up a per-bit answer under. `find_bus_port_holes` handles this
//! by scanning for `ident '[' int_literal ']'` token sequences matching a
//! bus port's base name and replacing the *whole* sequence, turning it
//! into an ordinary hole for `render_with_holes`.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Range;

use basedb::{AstId, AstIdMap, BaseDB, VfsStorage};
use hir_def::db::HirDefDB;
use hir_def::item_tree::{bus_bit_name, BusDecl, ItemTree, Module as TreeModule, ModuleItem, Node};
use hir_def::nameres::diagnostics::DefDiagnostic;
use hir_def::ItemTreeId;
use syntax::name::{AsName, Name};
use syntax::{ast, AstNode, ConstExprValue, Parse, SourceFile, TextRange, TextSize};
use tokens::lexer::TokenKind;

use crate::db::CompilationDB;

/// Entry point, called once from [`CompilationDB::new`]. No-op (and cheap:
/// one `item_tree` lookup) for the overwhelming majority of files, which
/// contain no instantiations at all.
pub(crate) fn elaborate_instantiations(db: &mut CompilationDB) -> anyhow::Result<()> {
    let root_file = db.compilation_unit().root_file();
    let tree = db.item_tree(root_file);

    let has_any_instantiation = tree
        .data
        .modules
        .iter()
        .any(|m| m.items.iter().any(|it| matches!(it, ModuleItem::Instantiation(_))));
    if !has_any_instantiation {
        return Ok(());
    }

    // Cycles cannot be flattened, and unresolved child modules must not be
    // silently dropped. Keep the original file so the normal diagnostic
    // path reports these errors against their source instantiations.
    let def_map = db.def_map(root_file);
    if def_map.diagnostics.iter().any(|d| {
        matches!(d, DefDiagnostic::CyclicInstantiation { .. } | DefDiagnostic::UnknownInstantiatedModule { .. })
    }) {
        return Ok(());
    }

    let ast_id_map = db.ast_id_map(root_file);
    let parse = db.parse(root_file);
    let by_name: HashMap<Name, ItemTreeId<TreeModule>> =
        tree.data.modules.iter_enumerated().map(|(id, m)| (m.name.clone(), id)).collect();

    let mut ctx = ElabCtx {
        tree: &tree,
        ast_id_map: &ast_id_map,
        parse: &parse,
        by_name,
        errors: Vec::new(),
    };

    let mut out = String::new();
    for item in parse.tree().items() {
        match item {
            ast::Item::ModuleDecl(module_ast) => {
                let Some(name) = module_ast.name().map(|n| n.as_name()) else { continue };
                let Some(&module_id) = ctx.by_name.get(&name) else { continue };
                out.push_str(&ctx.flatten_top_level_module(module_id, &module_ast));
            }
            other => out.push_str(&other.syntax().text().to_string()),
        }
        out.push('\n');
    }

    if !ctx.errors.is_empty() {
        anyhow::bail!("{}", ctx.errors.join("\n"));
    }

    // Enhancement-58: name the synthetic file by BASENAME only. The VFS holds
    // the canonicalized absolute root path, and this name is embedded in the
    // compiled .osdi as source-file provenance -- an absolute path would leak
    // the build machine's layout into the artifact (repo examples must stay
    // machine-portable). Diagnostics still render fine against the short name.
    let root_path = db.vfs().read().file_path(root_file).to_string();
    let base_name = root_path.rsplit(['/', '\\']).next().unwrap_or(root_path.as_str()).to_owned();
    // virtual paths must start with '/' (VfsPath::new_virtual_path)
    let synth_name = format!("/{}__elaborated.va", base_name);
    let file_id = db.vfs().write().add_virt_file(&synth_name, out.into());

    let include_dirs = db.include_dirs(root_file);
    db.set_include_dirs(file_id, include_dirs);
    let macro_flags = db.macro_flags(root_file);
    db.set_macro_flags(file_id, macro_flags);
    let overwrites = db.global_lint_overwrites(root_file);
    db.set_global_lint_overwrites(file_id, overwrites);

    db.set_root_file(file_id);
    Ok(())
}

struct ElabCtx<'a> {
    tree: &'a ItemTree,
    ast_id_map: &'a AstIdMap,
    parse: &'a Parse<SourceFile>,
    by_name: HashMap<Name, ItemTreeId<TreeModule>>,
    errors: Vec<String>,
}

/// A binding for one syntactic port: either a single resolved net
/// (scalar port), or one resolved net per bit (bus port).
#[derive(Clone)]
enum PortBinding {
    Scalar(String),
    Bus(BTreeMap<i32, String>),
}

/// The full renaming/binding context for rendering one module's body:
/// `subst` covers ordinary whole-identifier renames (nets, vars, params,
/// bus *base* names, ...); `bus_ports` covers bus-typed ports, which need
/// the token-sequence-aware substitution described in this module's doc
/// comment instead.
#[derive(Default, Clone)]
struct Scope {
    subst: HashMap<String, String>,
    bus_ports: HashMap<Name, BTreeMap<i32, String>>,
}

/// Tries to constant-fold a `[msb:lsb]` instance-array range, mirroring
/// `hir_def::item_tree::lower::fold_width_range` (private to that crate).
fn fold_width_range(range: &ast::Range) -> Option<(i32, i32)> {
    let msb = range.start()?.as_constexprval()?;
    let lsb = range.end()?.as_constexprval()?;
    match (msb, lsb) {
        (ConstExprValue::Int(msb), ConstExprValue::Int(lsb)) => Some((msb, lsb)),
        _ => None,
    }
}

fn is_trivia(kind: TokenKind) -> bool {
    matches!(kind, TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment { .. })
}

/// Scans `text` for `ident '[' int_literal ']'` token sequences where
/// `ident` names a bus port in `bus_ports`, producing one hole per match
/// that replaces the *entire* sequence with the resolved per-bit text (see
/// this module's doc comment for why a bus port can't use plain
/// whole-identifier substitution). A bus port reference with no matching
/// bit entry, or not immediately followed by a bit-select, is left alone
/// (degrading to a plain, unresolved identifier -- the same graceful
/// "downstream diagnostic instead of a crash" fallback used elsewhere in
/// this pass).
fn find_bus_port_holes(
    text: &str,
    bus_ports: &HashMap<Name, BTreeMap<i32, String>>,
) -> Vec<(Range<usize>, String)> {
    if bus_ports.is_empty() {
        return Vec::new();
    }
    let mut spans = Vec::new();
    let mut pos = 0usize;
    for tok in lexer::tokenize(text) {
        let start = pos;
        let end = pos + usize::from(tok.len);
        pos = end;
        spans.push((start, end, tok.kind));
    }

    let mut holes = Vec::new();
    let mut i = 0usize;
    while i < spans.len() {
        let (start, end, kind) = spans[i];
        if kind == TokenKind::SimpleIdent {
            if let Some(bits) = bus_ports.get(&Name::resolve(&text[start..end])) {
                let mut j = i + 1;
                while j < spans.len() && is_trivia(spans[j].2) {
                    j += 1;
                }
                if j < spans.len() && spans[j].2 == TokenKind::OpenBracket {
                    let mut k = j + 1;
                    while k < spans.len() && is_trivia(spans[k].2) {
                        k += 1;
                    }
                    if let Some(&(lit_start, lit_end, lit_kind)) = spans.get(k) {
                        if matches!(lit_kind, TokenKind::Literal { .. }) {
                            if let Ok(bit) = text[lit_start..lit_end].parse::<i32>() {
                                let mut m = k + 1;
                                while m < spans.len() && is_trivia(spans[m].2) {
                                    m += 1;
                                }
                                if let Some(&(
                                    bracket_start,
                                    bracket_end,
                                    TokenKind::CloseBracket,
                                )) = spans.get(m)
                                {
                                    let _ = bracket_start;
                                    if let Some(replacement) = bits.get(&bit) {
                                        holes.push((start..bracket_end, replacement.clone()));
                                        i = m + 1;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        i += 1;
    }
    holes
}

/// Rewrites `text`'s `SimpleIdent` tokens using `scope.subst` (exact
/// whole-token match only), while replacing each byte range in `holes`
/// (given relative to the start of `text`; combined with `scope`'s own
/// bus-port holes and sorted internally) with its associated *already
/// fully-resolved* replacement text verbatim -- tokens inside a hole are
/// never individually inspected/renamed, which is what makes composing
/// renamed scopes (an already-flattened nested instance's text, or a
/// parent-scope override expression) correct: opaque foreign text is never
/// accidentally re-renamed using the wrong scope's `subst`.
fn render_with_holes(text: &str, holes: &[(Range<usize>, String)], scope: &Scope) -> String {
    let mut all_holes = find_bus_port_holes(text, &scope.bus_ports);
    all_holes.extend(holes.iter().cloned());
    all_holes.sort_by_key(|(r, _)| r.start);

    let tokens = lexer::tokenize(text);
    let mut out = String::with_capacity(text.len());
    let mut pos = 0usize;
    let mut holes = all_holes.iter().peekable();

    for tok in tokens {
        let start = pos;
        let end = pos + usize::from(tok.len);
        pos = end;

        if let Some((range, replacement)) = holes.peek() {
            if start >= range.start && start < range.end {
                if start == range.start {
                    out.push_str(replacement);
                }
                if end >= range.end {
                    holes.next();
                }
                continue;
            }
        }

        let raw = &text[start..end];
        if tok.kind == TokenKind::SimpleIdent {
            if let Some(replacement) = scope.subst.get(raw) {
                out.push_str(replacement);
                continue;
            }
        }
        out.push_str(raw);
    }
    out
}

fn apply_rename(text: &str, scope: &Scope) -> String {
    render_with_holes(text, &[], scope)
}

fn rel_range(base: TextSize, range: TextRange) -> Range<usize> {
    let base: u32 = base.into();
    let start: u32 = range.start().into();
    let end: u32 = range.end().into();
    (start - base) as usize..(end - base) as usize
}

/// Finds a bus (net or variable array) declared in `scope` named exactly
/// `text` (trimmed) with exactly `width` bits -- the "is this port/array
/// actual meant to be sliced" check described in this module's doc
/// comment. Requiring an exact width match (rather than "wide enough")
/// keeps the heuristic conservative: a plain scalar net, or a bus of the
/// wrong width, is left alone (bound/broadcast verbatim) rather than
/// guessed at.
fn find_matching_caller_bus<'a>(
    scope: &'a TreeModule,
    text: &str,
    width: usize,
) -> Option<&'a BusDecl> {
    let name = Name::resolve(text.trim());
    scope.buses.iter().chain(scope.var_arrays.iter()).find(|b| {
        b.base_name == name && {
            let (lo, hi) = b.min_max();
            (hi - lo + 1) as usize == width
        }
    })
}

/// Evaluate integer-only slice bounds without invoking model-body lowering.
/// Named parameter bounds are not yet resolved by this text-level elaborator.
fn fold_slice_bound(expr: &ast::Expr) -> Option<i32> {
    use ast::{BinaryOp, UnaryOp};
    if let Some(ConstExprValue::Int(value)) = expr.as_constexprval() {
        return Some(value);
    }
    match expr {
        ast::Expr::ParenExpr(expr) => fold_slice_bound(&expr.expr()?),
        ast::Expr::PrefixExpr(expr) => {
            let value = fold_slice_bound(&expr.expr()?)?;
            match expr.op_kind()? {
                UnaryOp::Neg => value.checked_neg(),
                UnaryOp::Identity => Some(value),
                UnaryOp::BitNegate => Some(!value),
                UnaryOp::Not => Some(i32::from(value == 0)),
            }
        }
        ast::Expr::BinExpr(expr) => {
            let lhs = fold_slice_bound(&expr.lhs()?)?;
            let rhs = fold_slice_bound(&expr.rhs()?)?;
            match expr.op_kind()? {
                BinaryOp::Addition => lhs.checked_add(rhs),
                BinaryOp::Subtraction => lhs.checked_sub(rhs),
                BinaryOp::Multiplication => lhs.checked_mul(rhs),
                BinaryOp::Division => lhs.checked_div(rhs),
                BinaryOp::Remainder => lhs.checked_rem(rhs),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Enumerate a range in its declared order, including descending ranges.
fn ordered_bits(first: i32, last: i32) -> impl Iterator<Item = i32> {
    let step = if first <= last { 1 } else { -1 };
    (0..=i64::from(first).abs_diff(i64::from(last)))
        .map(move |offset| (i64::from(first) + offset as i64 * step) as i32)
}

/// Bind bus ports to scalar identities before applying the caller's scope.
/// In particular `bus[2:3]` is two nodes, never a scalar string to broadcast.
fn bind_port(
    result: &mut HashMap<Name, PortBinding>,
    target: &TreeModule,
    caller: &TreeModule,
    port_name: &Name,
    net: &ast::Expr,
) -> anyhow::Result<()> {
    let text = net.syntax().text().to_string();
    let target_bus = target.buses.iter().find(|b| &b.base_name == port_name);
    let selected = match net {
        ast::Expr::PartSelectExpr(slice) => {
            let base = slice
                .base()
                .map(|p| p.syntax().text().to_string())
                .ok_or_else(|| anyhow::anyhow!("invalid bus slice '{text}'"))?;
            let range = slice
                .range()
                .and_then(|r| Some((fold_slice_bound(&r.start()?)?, fold_slice_bound(&r.end()?)?)))
                .ok_or_else(|| anyhow::anyhow!("bus slice '{text}' requires constant integer bounds"))?;
            let bus = caller
                .buses
                .iter()
                .find(|b| b.base_name == Name::resolve(&base))
                .ok_or_else(|| anyhow::anyhow!("bus slice '{text}' does not name a bus"))?;
            if !bus.contains_bit(range.0) || !bus.contains_bit(range.1) {
                anyhow::bail!("bus slice '{text}' is outside the declared range of '{base}'");
            }
            Some((base, range.0, range.1))
        }
        ast::Expr::PathExpr(_) => caller
            .buses
            .iter()
            .find(|b| b.base_name == Name::resolve(text.trim()))
            .map(|b| (text.clone(), b.msb, b.lsb)),
        _ => None,
    };
    let Some(bus) = target_bus else {
        if selected.is_some() {
            // Whole-bus scalar actuals are handled per instance-array element
            // by expand_instantiation. An explicit multi-bit slice is not scalar.
            if let ast::Expr::PartSelectExpr(_) = net {
                let (base, first, last) = selected.unwrap();
                if first != last {
                    anyhow::bail!("bus slice '{text}' cannot connect to scalar port '{port_name}'");
                }
                result.insert(port_name.clone(), PortBinding::Scalar(format!("{base}[{first}]")));
                return Ok(());
            }
        }
        result.insert(port_name.clone(), PortBinding::Scalar(text));
        return Ok(());
    };
    let Some((base, first, last)) = selected else {
        // Preserve the existing scalar-to-bus broadcast behavior.
        result.insert(
            port_name.clone(),
            PortBinding::Bus(ordered_bits(bus.msb, bus.lsb).map(|bit| (bit, text.clone())).collect()),
        );
        return Ok(());
    };
    if i64::from(bus.msb).abs_diff(i64::from(bus.lsb)) != i64::from(first).abs_diff(i64::from(last)) {
        anyhow::bail!("width mismatch connecting '{text}' to bus port '{port_name}'");
    }
    let bits = ordered_bits(bus.msb, bus.lsb)
        .zip(ordered_bits(first, last))
        .map(|(formal, actual)| (formal, format!("{base}[{actual}]")))
        .collect();
    result.insert(port_name.clone(), PortBinding::Bus(bits));
    Ok(())
}

/// The module's syntactic port list, in true header-declaration order
/// (`module foo(p, n, bus);`), used for positional port-connection
/// matching. Reading this from the AST header (rather than reconstructing
/// order from `Module::nodes`) is necessary because a vectored port's
/// extra bits (beyond its first) are appended to `nodes` wherever their
/// `[msb:lsb]` width clause happens to be declared in the module body,
/// not kept adjacent to the port's original header position.
fn target_port_names(module_ast: &ast::ModuleDecl) -> Vec<Name> {
    let Some(ports) = module_ast.module_ports() else { return Vec::new() };
    ports
        .ports()
        .flat_map(|port| match port.kind() {
            ast::ModulePortKind::Name(name) => vec![name.as_name()],
            ast::ModulePortKind::PortDecl(decl) => decl.names().map(|n| n.as_name()).collect(),
        })
        .collect()
}

/// Runs `apply_rename` over every raw (unrenamed) text held in a
/// `PortBinding`/plain-`String` map, producing the fully-resolved form the
/// callee expects to receive (see `render_with_holes`'s "resolve, then
/// recurse" doc comment).
fn resolve_port_bindings(
    raw: HashMap<Name, PortBinding>,
    scope: &Scope,
) -> HashMap<Name, PortBinding> {
    raw.into_iter()
        .map(|(k, v)| {
            let v = match v {
                PortBinding::Scalar(text) => PortBinding::Scalar(apply_rename(&text, scope)),
                PortBinding::Bus(bits) => PortBinding::Bus(
                    bits.into_iter().map(|(bit, text)| (bit, apply_rename(&text, scope))).collect(),
                ),
            };
            (k, v)
        })
        .collect()
}

impl ElabCtx<'_> {
    fn module_ast(&self, ast_id: AstId<ast::ModuleDecl>) -> ast::ModuleDecl {
        self.ast_id_map.get(ast_id).to_node(self.parse.tree().syntax())
    }

    /// Resolves an instantiation's port-connection list against the target
    /// module's declared ports, returning *raw, un-renamed* source text
    /// (the caller is responsible for running it through its own `Scope`
    /// before handing it further down -- see `resolve_port_bindings`).
    fn raw_port_bindings(
        &mut self,
        caller: &TreeModule,
        target: &TreeModule,
        target_ast: &ast::ModuleDecl,
        unit: &ast::InstanceUnit,
    ) -> HashMap<Name, PortBinding> {
        let mut result = HashMap::new();
        let Some(port_conns) = unit.port_conns() else { return result };
        let conns: Vec<_> = port_conns.port_conns().collect();
        let port_names = target_port_names(target_ast);

        if conns.iter().all(|c| c.name().is_none()) {
            for (name, conn) in port_names.iter().zip(conns.iter()) {
                if let Some(net) = conn.net() {
                    if let Err(error) = bind_port(&mut result, target, caller, name, &net) {
                        self.errors.push(error.to_string());
                    }
                }
            }
        } else {
            for conn in &conns {
                if let (Some(name), Some(net)) = (conn.name(), conn.net()) {
                    if let Err(error) = bind_port(&mut result, target, caller, &name.as_name(), &net) {
                        self.errors.push(error.to_string());
                    }
                }
            }
        }
        result
    }

    /// Same as `raw_port_bindings` but for `#(...)` parameter overrides.
    fn resolve_param_bindings(
        &self,
        target: &TreeModule,
        overrides: Option<ast::ParamOverrides>,
    ) -> HashMap<Name, String> {
        let mut result = HashMap::new();
        let Some(overrides) = overrides else { return result };
        let assigns: Vec<_> = overrides.param_assigns().collect();
        let param_names: Vec<Name> = target
            .items
            .iter()
            .filter_map(|it| match it {
                ModuleItem::Parameter(p) => Some(self.tree[*p].name.clone()),
                _ => None,
            })
            .collect();

        if assigns.iter().all(|a| a.name().is_none()) {
            for (name, assign) in param_names.iter().zip(assigns.iter()) {
                if let Some(val) = assign.val() {
                    result.insert(name.clone(), val.syntax().text().to_string());
                }
            }
        } else {
            for assign in &assigns {
                if let (Some(name), Some(val)) = (assign.name(), assign.val()) {
                    result.insert(name.as_name(), val.syntax().text().to_string());
                }
            }
        }
        result
    }

    /// Builds the "flatten this module's own declarations, in order,
    /// expanding any nested instantiations" text shared by both top-level
    /// modules (`scope` empty, so nothing is renamed and nothing is
    /// overridden -- everything just passes through) and inlined instances
    /// (`scope` maps every locally-declared name to its prefixed/bound
    /// form).
    fn render_items(
        &mut self,
        target_id: ItemTreeId<TreeModule>,
        scope: &Scope,
        param_binding: &HashMap<Name, String>,
        port_names: &HashSet<Name>,
        prefix: &str,
    ) -> String {
        let target_ast = self.module_ast(self.tree[target_id].ast_id);
        let mut out = String::new();

        for item in target_ast.module_items() {
            match item {
                // A body port-direction declaration (`inout p, n;`) only
                // ever names ports; when inlining an instance its ports are
                // bound to already-declared outer identities (or a fresh
                // internal net), so re-declaring them as ports here would
                // collide with that outer declaration -- drop entirely.
                ast::ModuleItem::BodyPortDecl(_) if !port_names.is_empty() => continue,
                ast::ModuleItem::Instantiation(nested) => {
                    out.push_str(&self.expand_instantiation(target_id, &nested, scope, prefix));
                }
                ast::ModuleItem::ParamDecl(decl) => {
                    let base = decl.syntax().text_range().start();
                    let mut holes = Vec::new();
                    for param in decl.paras() {
                        let (Some(name), Some(default)) = (param.name(), param.default()) else {
                            continue;
                        };
                        if let Some(bound) = param_binding.get(&name.as_name()) {
                            holes.push((
                                rel_range(base, default.syntax().text_range()),
                                bound.clone(),
                            ));
                        }
                    }
                    out.push_str(&render_with_holes(
                        &decl.syntax().text().to_string(),
                        &holes,
                        scope,
                    ));
                }
                // A net/discipline declaration (`electrical p, n;`, or a
                // vectored `electrical [3:0] p, bus;`) may name a mix of
                // ports and ordinary internal nets/buses (both share this
                // syntax); same reasoning as `BodyPortDecl` above, but only
                // the port *names* need dropping from the list, not
                // necessarily the whole statement -- a bus-typed port is
                // dropped exactly like a scalar one (it's fully handled by
                // `render_instance_content`'s per-bit port binding; its own
                // `[msb:lsb]` declaration would just redeclare an identity
                // that already belongs to an outer/bound net).
                ast::ModuleItem::NetDecl(decl) if !port_names.is_empty() => {
                    let kept: Vec<String> = decl
                        .names()
                        .filter_map(|n| {
                            let name = n.as_name();
                            if port_names.contains(&name) {
                                None
                            } else {
                                let key = name.to_string();
                                Some(scope.subst.get(&key).cloned().unwrap_or(key))
                            }
                        })
                        .collect();
                    if !kept.is_empty() {
                        let discipline = decl
                            .discipline()
                            .map(|d| d.syntax().text().to_string())
                            .unwrap_or_default();
                        let width = decl
                            .width()
                            .map(|w| format!("{} ", w.syntax().text()))
                            .unwrap_or_default();
                        out.push_str(&format!("{discipline} {width}{};", kept.join(", ")));
                    }
                }
                other => out.push_str(&apply_rename(&other.syntax().text().to_string(), scope)),
            }
            out.push('\n');
        }
        out
    }

    /// Expands one instantiation statement (all of its comma-separated
    /// `InstanceUnit`s, each possibly further expanded into several array
    /// elements) into final, ready-to-splice text. `parent_id` is the
    /// module the instantiation statement itself lives in -- needed both
    /// to resolve its own `buses`/`var_arrays` for the port-slicing
    /// heuristic (see this module's doc comment) and, for an instance
    /// array, to additionally slice a matching-width bus port actual
    /// per array element rather than broadcasting it to every element.
    fn expand_instantiation(
        &mut self,
        parent_id: ItemTreeId<TreeModule>,
        inst: &ast::Instantiation,
        scope: &Scope,
        prefix: &str,
    ) -> String {
        let Some(module_name) = inst.module().map(|n| n.as_name()) else { return String::new() };
        let Some(&target_id) = self.by_name.get(&module_name) else { return String::new() };
        let target = self.tree[target_id].clone();
        let target_ast = self.module_ast(target.ast_id);
        let parent = self.tree[parent_id].clone();

        let param_raw = self.resolve_param_bindings(&target, inst.param_overrides());
        let param_binding: HashMap<Name, String> =
            param_raw.into_iter().map(|(k, v)| (k, apply_rename(&v, scope))).collect();

        let mut out = String::new();
        for unit in inst.instance_units() {
            let Some(unit_name) = unit.name() else { continue };
            let base_name = unit_name.as_name();

            let port_raw = self.raw_port_bindings(&parent, &target, &target_ast, &unit);

            let indices: Vec<Option<i32>> = match unit.width().and_then(|r| fold_width_range(&r)) {
                Some((msb, lsb)) => {
                    let (lo, hi) = if msb <= lsb { (msb, lsb) } else { (lsb, msb) };
                    (lo..=hi).map(Some).collect()
                }
                None => vec![None],
            };

            for (elem_pos, idx) in indices.iter().enumerate() {
                // For an instance array, a *scalar* port bound to a bare
                // identifier naming a matching-width bus in the parent's
                // scope is sliced per array element (`p[elem_pos]`)
                // instead of broadcasting the same connection to every
                // element -- the array-equivalent of `bind_port`'s
                // per-bit slicing. Bus-typed ports (already resolved as
                // `PortBinding::Bus`) are left as-is; combining a bus port
                // with an instance array simultaneously is out of scope.
                let mut port_raw_elem = port_raw.clone();
                if indices.len() > 1 {
                    for (port_name, binding) in port_raw.iter() {
                        let PortBinding::Scalar(text) = binding else { continue };
                        if let Some(caller_bus) =
                            find_matching_caller_bus(&parent, text, indices.len())
                        {
                            let (caller_lo, _) = caller_bus.min_max();
                            let bit = caller_lo + elem_pos as i32;
                            port_raw_elem.insert(
                                port_name.clone(),
                                PortBinding::Scalar(format!("{text}[{bit}]")),
                            );
                        }
                    }
                }
                let port_binding = resolve_port_bindings(port_raw_elem, scope);

                let child_prefix = match idx {
                    Some(i) => format!("{prefix}{base_name}_{i}__"),
                    None => format!("{prefix}{base_name}__"),
                };
                out.push_str(&self.render_instance_content(
                    target_id,
                    &child_prefix,
                    &port_binding,
                    &param_binding,
                ));
                out.push('\n');
            }
        }
        out
    }

    /// Renders one instance's flattened body: a `Scope` covering every
    /// name the target module itself declares (ports bound to the caller's
    /// net, or a fresh internal net if left open; everything else
    /// prefixed) plus any fresh open-port net declarations, followed by
    /// the target's own (recursively expanded) items.
    fn render_instance_content(
        &mut self,
        target_id: ItemTreeId<TreeModule>,
        prefix: &str,
        port_binding: &HashMap<Name, PortBinding>,
        param_binding: &HashMap<Name, String>,
    ) -> String {
        let target = self.tree[target_id].clone();
        let mut scope = Scope::default();
        let mut extra_decls = Vec::new();
        // NOTE: a vectored port's bits beyond the first are appended to
        // `nodes` wherever their `[msb:lsb]` clause is declared in the
        // module body (see `target_port_names`'s doc comment), so `nodes`
        // is *not* cleanly partitioned into "first `num_ports` entries are
        // ports"; `node.is_port` (set correctly on every bit) is the only
        // reliable per-node test. `port_names` holds *base* names (a bus
        // port's `p[2]` node contributes `p`, matching what `decl.names()`
        // yields for the source-level `electrical [1:0] p;` declaration,
        // and what a bus's own `BusDecl::base_name` is) so every "is this
        // name a port" check below compares at the same granularity.
        let port_names: HashSet<Name> = target
            .nodes
            .iter()
            .filter(|n| n.is_port)
            .map(|n| {
                let s = n.name.to_string();
                match s.find('[') {
                    Some(i) => Name::resolve(&s[..i]),
                    None => n.name.clone(),
                }
            })
            .collect();

        for node in target.nodes.iter() {
            if !node.is_port {
                if !node.name.to_string().contains('[') {
                    // internal bus/array bits are renamed via their base name
                    // below (`buses`/`var_arrays`); only insert a direct entry
                    // here for genuinely scalar internal nets.
                    scope.subst.insert(node.name.to_string(), format!("{prefix}{}", node.name));
                }
                continue;
            }
            // A bus port's bits are grouped by base name below (in one
            // `scope.bus_ports` entry per base), so only scalar ports are
            // handled per-node here.
            if node.name.to_string().contains('[') {
                continue;
            }
            let bound = match port_binding.get(&node.name) {
                Some(PortBinding::Scalar(text)) => text.clone(),
                _ => {
                    let fresh = format!("{prefix}open__{}", node.name);
                    let discipline = node
                        .discipline(self.tree)
                        .map(|d| d.to_string())
                        .unwrap_or_else(|| "electrical".to_owned());
                    extra_decls.push(format!("{discipline} {fresh};"));
                    fresh
                }
            };
            scope.subst.insert(node.name.to_string(), bound);
        }

        // Bus ports: one `scope.bus_ports` entry per base name, filling in
        // a fresh net (declaring it) for any bit left unbound.
        for bus in target.buses.iter().chain(target.var_arrays.iter()) {
            if !port_names.contains(&bus.base_name) {
                continue;
            }
            if scope.bus_ports.contains_key(&bus.base_name) {
                continue;
            }
            let (lo, hi) = bus.min_max();
            let bound_bits = match port_binding.get(&bus.base_name) {
                Some(PortBinding::Bus(bits)) => bits.clone(),
                _ => BTreeMap::new(),
            };
            let mut bits = BTreeMap::new();
            for bit in lo..=hi {
                let text = bound_bits.get(&bit).cloned().unwrap_or_else(|| {
                    let bit_name = bus_bit_name(&bus.base_name, bit);
                    let fresh =
                        format!("{prefix}open__{}", bit_name.to_string().replace(['[', ']'], "_"));
                    let discipline = target
                        .nodes
                        .iter()
                        .find(|n| n.name == bit_name)
                        .and_then(|n| n.discipline(self.tree))
                        .map(|d| d.to_string())
                        .unwrap_or_else(|| "electrical".to_owned());
                    extra_decls.push(format!("{discipline} {fresh};"));
                    fresh
                });
                bits.insert(bit, text);
            }
            scope.bus_ports.insert(bus.base_name.clone(), bits);
        }

        // Bus *ports* are entirely handled above (per-bit) -- the bare
        // base name of a bus port never legally appears standalone in
        // Verilog-A (every use requires a bit-select), so it must not get
        // its own `scope.subst` entry.
        for bus in target.buses.iter().chain(target.var_arrays.iter()) {
            if port_names.contains(&bus.base_name) {
                continue;
            }
            scope
                .subst
                .entry(bus.base_name.to_string())
                .or_insert_with(|| format!("{prefix}{}", bus.base_name));
        }
        for item in &target.items {
            let renamed = match *item {
                ModuleItem::Variable(id) => Some(self.tree[id].name.clone()),
                ModuleItem::Parameter(id) => Some(self.tree[id].name.clone()),
                ModuleItem::Branch(id) => Some(self.tree[id].name.clone()),
                ModuleItem::Function(id) => Some(self.tree[id].name.clone()),
                ModuleItem::AliasParameter(id) => Some(self.tree[id].name.clone()),
                _ => None,
            };
            if let Some(name) = renamed {
                scope.subst.insert(name.to_string(), format!("{prefix}{name}"));
            }
        }

        let body = self.render_items(target_id, &scope, param_binding, &port_names, prefix);
        let mut out = extra_decls.join("\n");
        if !out.is_empty() {
            out.push('\n');
        }
        out.push_str(&body);
        out
    }

    /// Top-level entry for one module declared directly in the source
    /// file: keeps its header/`endmodule` footer byte-for-byte, only
    /// replacing the item-list region when the module directly contains at
    /// least one instantiation (a module with none is returned verbatim,
    /// unchanged, to keep this pass a no-op for the common case).
    fn flatten_top_level_module(
        &mut self,
        module_id: ItemTreeId<TreeModule>,
        module_ast: &ast::ModuleDecl,
    ) -> String {
        let module = &self.tree[module_id];
        let has_instantiation =
            module.items.iter().any(|it| matches!(it, ModuleItem::Instantiation(_)));
        if !has_instantiation {
            return module_ast.syntax().text().to_string();
        }

        let items: Vec<_> = module_ast.module_items().collect();
        let base = module_ast.syntax().text_range().start();
        let full = module_ast.syntax().text().to_string();
        let rel_start = rel_range(base, items.first().unwrap().syntax().text_range()).start;
        let rel_end = rel_range(base, items.last().unwrap().syntax().text_range()).end;

        let body = self.render_items(
            module_id,
            &Scope::default(),
            &HashMap::new(),
            &Default::default(),
            "",
        );
        format!("{}{}{}", &full[..rel_start], body, &full[rel_end..])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source(actual: &str, formal: &str) -> String {
        format!(r#"
`include "disciplines.vams"
module pair(p);
    inout [{formal}] p;
    electrical [{formal}] p;
    analog begin
        I(p[0]) <+ V(p[0]);
        I(p[1]) <+ 2 * V(p[1]);
    end
endmodule
module top(a);
    inout [0:3] a;
    electrical [0:3] a;
    pair child({actual});
endmodule
"#)
    }

    fn flattened(source: &str) -> String {
        let db = CompilationDB::new_virtual(source).unwrap();
        assert_eq!(db.compilation_unit().test_diagnostics(&db), "");
        db.parse(db.compilation_unit().root_file()).tree().syntax().text().to_string()
    }

    #[test]
    fn unresolved_child_module_keeps_its_diagnostic() {
        let source = r#"
`include "disciplines.vams"
module top(a);
    inout [0:3] a;
    electrical [0:3] a;
    missing child(a[0:1]);
endmodule
"#;
        let db = CompilationDB::new_virtual(source).unwrap();
        let diagnostics = db.compilation_unit().test_diagnostics(&db);
        assert!(diagnostics.contains("unknown module 'missing'"), "{diagnostics}");
        let text = db.parse(db.compilation_unit().root_file()).tree().syntax().text().to_string();
        assert!(text.contains("missing child(a[0:1]);"), "{text}");
    }

    #[test]
    fn positional_and_named_slices_preserve_bit_identity() {
        for actual in ["a[2:3]", ".p(a[2:3])", "a[1+1:3]"] {
            let out = flattened(&source(actual, "0:1"));
            assert!(out.contains("I(a[2]) <+ V(a[2])"), "{out}");
            assert!(out.contains("I(a[3]) <+ 2 * V(a[3])"), "{out}");
        }
    }

    #[test]
    fn opposite_range_directions_map_in_declaration_order() {
        let out = flattened(&source("a[3:2]", "0:1"));
        assert!(out.contains("I(a[3]) <+ V(a[3])"), "{out}");
        assert!(out.contains("I(a[2]) <+ 2 * V(a[2])"), "{out}");
        let out = flattened(&source("a[2:3]", "1:0"));
        assert!(out.contains("I(a[3]) <+ V(a[3])"), "{out}");
        assert!(out.contains("I(a[2]) <+ 2 * V(a[2])"), "{out}");
    }

    #[test]
    fn nested_slices_resolve_through_parent_bus_bindings() {
        let source = source("a[2:3]", "0:1").replace(
            "pair child(a[2:3]);",
            "wrapper child(a);",
        ) + r#"
module wrapper(b);
    inout [0:3] b;
    electrical [0:3] b;
    pair inner(.p(b[2:3]));
endmodule
"#;
        let out = flattened(&source);
        assert!(out.contains("I(a[2]) <+ V(a[2])"), "{out}");
        assert!(out.contains("I(a[3]) <+ 2 * V(a[3])"), "{out}");
    }

    #[test]
    fn single_bit_slice_connects_to_scalar_port() {
        let source = r#"
`include "disciplines.vams"
module scalar(p);
    inout p;
    electrical p;
    analog I(p) <+ V(p);
endmodule
module top(a);
    inout [0:3] a;
    electrical [0:3] a;
    scalar child(a[2:2]);
endmodule
"#;
        let out = flattened(source);
        assert!(out.contains("I(a[2]) <+ V(a[2])"), "{out}");
        assert!(CompilationDB::new_virtual(&source.replace("a[2:2]", "a[2:3]")).is_err());
    }

    #[test]
    fn whole_buses_follow_declaration_order() {
        let out = flattened(&source("a", "0:1").replace("[0:3] a", "[3:2] a"));
        assert!(out.contains("I(a[3]) <+ V(a[3])"), "{out}");
        assert!(out.contains("I(a[2]) <+ 2 * V(a[2])"), "{out}");
    }

    #[test]
    fn slices_support_arbitrary_widths_and_nonzero_formal_indices() {
        for width in [1, 3, 7, 17, 64] {
            for descending in [false, true] {
                let last = 100 + width - 1;
                let actual = if descending { format!("{last}:100") } else { format!("100:{last}") };
                let contributions: String = (0..width)
                    .map(|i| format!("I(p[{}]) <+ {} * V(p[{}]);\n", 8 + i, i + 1, 8 + i))
                    .collect();
                let source = format!(r#"
`include "disciplines.vams"
module child(p);
    inout [8:{}] p;
    electrical [8:{}] p;
    analog begin
        {contributions}
    end
endmodule
module top(a);
    inout [100:200] a;
    electrical [100:200] a;
    child c(.p(a[{actual}]));
endmodule
"#, 8 + width - 1, 8 + width - 1);
                let out = flattened(&source);
                for i in 0..width {
                    let actual_bit = if descending { last - i } else { 100 + i };
                    let expected = format!("I(a[{actual_bit}]) <+ {} * V(a[{actual_bit}])", i + 1);
                    assert!(out.contains(&expected), "width={width}, descending={descending}: {out}");
                }
            }
        }
    }

    #[test]
    fn invalid_slices_report_errors_instead_of_broadcasting() {
        for (actual, message) in [
            ("a[0:2]", "width mismatch"),
            ("a[3:4]", "outside the declared range"),
            ("a[0:x]", "constant integer bounds"),
            ("a[0:1/0]", "constant integer bounds"),
            ("missing[0:1]", "does not name a bus"),
            ("a", "width mismatch"),
        ] {
            let error = match CompilationDB::new_virtual(&source(actual, "0:1")) {
                Ok(_) => panic!("accepted invalid slice {actual}"),
                Err(error) => error.to_string(),
            };
            assert!(error.contains(message), "{error}");
        }
    }
}
