use ordered_float::OrderedFloat;
use std::mem;
use std::sync::Arc;

use arena::IdxRange;
use basedb::{AstId, AstIdMap, ErasedAstId, FileId};
use syntax::ast::{self, ParamRef, PathSegmentKind};
use syntax::name::{kw, AsIdent, AsName, Name};
use syntax::{match_ast, AstNode, ConstExprValue, WalkEvent};
use typed_index_collections::TiVec;

use super::{
    Block, Branch, BranchKind, BusDecl, Discipline, DisciplineAttr, DisciplineAttrKind, Domain,
    Function, FunctionArg, FunctionItem, ItemTree, ItemTreeDiagnostic, ItemTreeId, Module,
    ModuleItem, Nature, NatureAttr, NatureRef, NatureRefKind, Net, Node, Param, Port, RootItem,
    Var,
};
// use tracing::trace;
use crate::db::HirDefDB;
use crate::item_tree::AliasParam;
use crate::types::AsType;
use crate::{LocalFunctionArgId, LocalNodeId, Path, Type};

/// Tries to constant-fold a `[msb:lsb]` width clause into two integers.
/// Only literal integers (optionally unary-negated) are supported, matching
/// `ast::Expr::as_constexprval`. Returns `None` if either bound is missing or
/// not a constant integer.
fn fold_width_range(range: &ast::Range) -> Option<(i32, i32)> {
    let msb = range.start()?.as_constexprval()?;
    let lsb = range.end()?.as_constexprval()?;
    match (msb, lsb) {
        (ConstExprValue::Int(msb), ConstExprValue::Int(lsb)) => Some((msb, lsb)),
        _ => None,
    }
}

/// Parses a synthesized bus-bit name like `"bus[3]"` back into `("bus", 3)`.
/// Used only for diagnosing out-of-range branch-endpoint bit-selects after the
/// fact (the index was already validated to be a constant integer at the
/// point the name was synthesized).
fn parse_synthesized_bit_name(name: &Name) -> Option<(Name, i32)> {
    let s: &str = name;
    let open = s.rfind('[')?;
    if !s.ends_with(']') {
        return None;
    }
    let idx_str = &s[open + 1..s.len() - 1];
    let idx: i32 = idx_str.parse().ok()?;
    Some((Name::resolve(&s[..open]), idx))
}

fn is_input(direction: &Option<ast::Direction>) -> bool {
    direction.as_ref().map_or(false, |it| it.input_token().is_some() || it.inout_token().is_some())
}

fn is_output(direction: &Option<ast::Direction>) -> bool {
    direction.as_ref().map_or(false, |it| it.output_token().is_some() || it.inout_token().is_some())
}

pub(super) struct Ctx {
    tree: ItemTree,
    source_ast_id_map: Arc<AstIdMap>,
}

impl Ctx {
    pub(super) fn new(db: &dyn HirDefDB, file: FileId) -> Self {
        Self { tree: ItemTree::default(), source_ast_id_map: db.ast_id_map(file) }
    }

    pub(super) fn lower_root_items(mut self, file: &ast::SourceFile) -> ItemTree {
        self.tree.top_level = file.items().filter_map(|it| self.lower_root_item(it)).collect();
        self.tree
    }

    fn lower_root_item(&mut self, item: ast::Item) -> Option<RootItem> {
        let item = match item {
            ast::Item::DisciplineDecl(discipline) => self.lower_discipline(discipline)?.into(),
            ast::Item::NatureDecl(nature) => self.lower_nature(nature)?.into(),
            ast::Item::ModuleDecl(module) => self.lower_module(module)?.into(),
        };
        Some(item)
    }

    fn lower_discipline(&mut self, decl: ast::DisciplineDecl) -> Option<ItemTreeId<Discipline>> {
        use kw::raw as kw;
        let name = decl.name()?.as_name();
        let ast_id = self.source_ast_id_map.ast_id(&decl);

        let mut potential = None;
        let mut flow = None;
        let mut domain = None;
        let attr_start = self.tree.data.discipline_attrs.next_key();
        for (id, attr) in decl.discipline_attrs().enumerate() {
            if let Some(name) = attr.name() {
                let kind = if let Some(qual) = name.qualifier() {
                    let qual = qual.segment_token();
                    match qual.as_ref().map(|t| t.text()) {
                        Some(kw::potential) => DisciplineAttrKind::PotentialOverwrite,
                        Some(kw::flow) => DisciplineAttrKind::FlowOverwrite,
                        _ => continue,
                    }
                } else {
                    DisciplineAttrKind::UserDefined
                };

                if let Some(name) = name.segment_token().map(|t| t.as_name()) {
                    let ast_id = self.source_ast_id_map.ast_id(&attr);

                    let mut evaluated: Option<ConstExprValue> = None;
                    match &*name {
                        kw::potential if potential.is_none() => {
                            if let Some(name) = attr.val().and_then(Self::lower_nature_expr) {
                                evaluated = Some(ConstExprValue::String(name.name.to_string()));
                                potential = Some((name, id.into()));
                            }
                        }
                        kw::flow if flow.is_none() => {
                            if let Some(name) = attr.val().and_then(Self::lower_nature_expr) {
                                evaluated = Some(ConstExprValue::String(name.name.to_string()));
                                flow = Some((name, id.into()))
                            }
                        }
                        kw::domain if domain.is_none() => {
                            match attr.val().and_then(|e| e.as_ident()).as_deref() {
                                Some(kw::continuous) => {
                                    evaluated =
                                        Some(ConstExprValue::String(kw::continuous.to_string()));
                                    domain = Some((Domain::Continuous, id.into()));
                                }
                                Some(kw::discrete) => {
                                    evaluated =
                                        Some(ConstExprValue::String(kw::discrete.to_string()));
                                    domain = Some((Domain::Discrete, id.into()));
                                }
                                _ => {
                                    // All other attributes - evaluate ast expression
                                    evaluated = attr.val().and_then(|v| v.as_constexprval());
                                }
                            }
                        }

                        _ => (),
                    };

                    self.tree.data.discipline_attrs.push(DisciplineAttr {
                        name: name.clone(),
                        kind,
                        ast_id,
                        value: evaluated,
                    });
                }
            }
        }
        let attr_end = self.tree.data.discipline_attrs.next_key();
        let res = Discipline {
            ast_id,
            name,
            potential,
            flow,
            extra_attrs: IdxRange::new(attr_start..attr_end),
            domain,
        };
        Some(self.tree.data.disciplines.push_and_get_key(res))
    }

    fn lower_nature_path(decl: &ast::Path) -> Option<NatureRef> {
        let mut name = decl.segment_token()?.as_name();

        let kind = match &*name {
            kw::raw::potential => NatureRefKind::DisciplinePotential,
            kw::raw::flow => NatureRefKind::DisciplineFlow,
            _ if decl.qualifier().is_none() && decl.segment_kind()? == PathSegmentKind::Name => {
                NatureRefKind::Nature
            }
            _ => return None,
        };

        if matches!(kind, NatureRefKind::DisciplineFlow | NatureRefKind::DisciplinePotential) {
            let qual = decl.qualifier()?;
            let segment = qual.segment()?;
            if segment.kind == PathSegmentKind::Root || qual.qualifier().is_some() {
                return None;
            }
            name = segment.syntax.as_name();
        }

        Some(NatureRef { name, kind })
    }

    fn lower_nature_expr(decl: ast::Expr) -> Option<NatureRef> {
        if let ast::Expr::PathExpr(path) = decl {
            Self::lower_nature_path(&path.path()?)
        } else {
            None
        }
    }

    fn lower_nature(&mut self, decl: ast::NatureDecl) -> Option<ItemTreeId<Nature>> {
        let name = decl.name()?.as_name();

        let parent = decl.parent().and_then(|it| Self::lower_nature_path(&it));
        let attr_start = self.tree.data.nature_attrs.next_key();

        let mut access = None;
        let mut ddt_nature = None;
        let mut idt_nature = None;
        let mut units = None;
        let mut abstol = None;

        for (id, attr) in decl.nature_attrs().enumerate() {
            if let Some(name) = attr.name().map(|name| name.as_name()) {
                use kw::raw as kw;

                let ast_id = self.source_ast_id_map.ast_id(&attr);
                let mut evaluated: Option<ConstExprValue> = None;
                match &*name {
                    kw::access if access.is_none() => {
                        if let Some(name) = attr.val().and_then(|e| e.as_ident()) {
                            evaluated = Some(ConstExprValue::String(name.to_string()));
                            access = Some((name, id.into()));
                        }
                    }
                    kw::ddt_nature if ddt_nature.is_none() => {
                        if let Some(name) = attr.val().and_then(Self::lower_nature_expr) {
                            evaluated = Some(ConstExprValue::String(name.name.to_string()));
                            ddt_nature = Some((name, id.into()));
                        }
                    }
                    kw::idt_nature if idt_nature.is_none() => {
                        if let Some(name) = attr.val().and_then(Self::lower_nature_expr) {
                            evaluated = Some(ConstExprValue::String(name.name.to_string()));
                            idt_nature = Some((name, id.into()));
                        }
                    }

                    kw::units if units.is_none() => {
                        if let Some(ast::LiteralKind::String(lit)) =
                            attr.val().and_then(|e| e.as_literal())
                        {
                            let a = attr.val().unwrap();
                            let b = a.as_literal();
                            let s = lit.unescaped_value();
                            evaluated = Some(ConstExprValue::String(s.clone()));
                            units = Some((s, id.into()));
                        }
                    }

                    kw::abstol if abstol.is_none() => {
                        let v1 =
                            attr.val().and_then(|v| v.as_constexprval()).and_then(|v| v.as_real());
                        if let Some(v) = v1 {
                            abstol = Some((OrderedFloat(v), id.into()));
                            evaluated = Some(ConstExprValue::Float(v.into()));
                        }
                    }
                    _ => {
                        // All other attributes - evaluate ast expression
                        evaluated = attr.val().and_then(|v| v.as_constexprval());
                    }
                };

                self.tree.data.nature_attrs.push(NatureAttr { name, ast_id, value: evaluated });
            }
        }

        let attr_end = self.tree.data.nature_attrs.next_key();
        let ast_id = self.source_ast_id_map.ast_id(&decl);

        let res = Nature {
            ast_id,
            name,
            parent,
            access,
            ddt_nature,
            idt_nature,
            abstol,
            units,
            attrs: IdxRange::new(attr_start..attr_end),
        };
        Some(self.tree.data.natures.push_and_get_key(res))
    }

    fn lower_module(&mut self, decl: ast::ModuleDecl) -> Option<ItemTreeId<Module>> {
        let name = decl.name()?.as_name();
        let ast_id = self.source_ast_id_map.ast_id(&decl);

        let mut nodes = TiVec::new();
        let mut items = Vec::new();
        let mut buses = Vec::new();
        if let Some(ports) = decl.module_ports() {
            self.lower_module_ports(ports, &mut nodes, &mut items, &mut buses);
        }

        let num_ports = nodes.len() as u32;
        self.lower_module_items(decl.module_items(), &mut nodes, &mut items, &mut buses);

        self.check_branch_bus_refs(&items, &buses);

        let res = Module { name, nodes, items, ast_id, num_ports, buses };
        Some(self.tree.data.modules.push_and_get_key(res))
    }

    fn lower_module_items(
        &mut self,
        items: ast::AstChildren<ast::ModuleItem>,
        nodes: &mut TiVec<LocalNodeId, Node>,
        dst: &mut Vec<ModuleItem>,
        buses: &mut Vec<BusDecl>,
    ) {
        for item in items {
            match item {
                ast::ModuleItem::BodyPortDecl(decl) => {
                    if let Some(decl) = decl.port_decl() {
                        self.lower_port_decl(decl, nodes, dst, buses);
                    }
                }
                ast::ModuleItem::NetDecl(decl) => {
                    self.lower_net_decl(decl, nodes, dst, buses);
                }
                ast::ModuleItem::AnalogBehaviour(behaviour) => {
                    if let Some(stmt) = behaviour.stmt() {
                        self.lower_stmt(stmt, dst);
                    }
                }
                ast::ModuleItem::VarDecl(var) => {
                    self.lower_var(var, dst);
                }
                ast::ModuleItem::ParamDecl(param) => {
                    self.lower_param(param, dst);
                }
                ast::ModuleItem::Function(fun) => {
                    self.lower_fun(fun, dst);
                }
                ast::ModuleItem::BranchDecl(branch) => self.lower_branch(branch, dst),
                ast::ModuleItem::AliasParam(alias) => self.lower_alias_param(alias, dst),
            };
        }
    }

    fn lower_fun(&mut self, fun: ast::Function, dst: &mut Vec<ModuleItem>) {
        let mut items = Vec::new();
        let mut args: TiVec<LocalFunctionArgId, FunctionArg> = TiVec::new();
        for item in fun.function_items() {
            match item {
                ast::FunctionItem::ParamDecl(decl) => self.lower_param(decl, &mut items),
                ast::FunctionItem::VarDecl(decl) => self.lower_var(decl, &mut items),
                ast::FunctionItem::FunctionArg(arg) => {
                    let ast_id = self.source_ast_id_map.ast_id(&arg);
                    let is_input = is_input(&arg.direction());
                    let is_output = is_output(&arg.direction());
                    for (name_idx, name) in arg.names().enumerate() {
                        let name = name.as_name();
                        if let Some(arg) = args.iter_mut().find(|arg| arg.name == name) {
                            // TODO validation
                            arg.ast_ids.push(ast_id)
                        }
                        let arg = args.push_and_get_key(FunctionArg {
                            name,
                            name_idx,
                            is_input,
                            is_output,
                            declarations: Vec::new(),
                            ast_ids: vec![ast_id],
                        });
                        items.push(arg.into());
                    }
                }
                ast::FunctionItem::Stmt(stmt) => self.lower_stmt(stmt, &mut items),
            }
        }

        items.retain(|decl| {
            if let FunctionItem::Variable(var) = decl {
                if let Some(arg) = args.iter_mut().find(|arg| arg.name == self.tree[*var].name) {
                    // TODO validation
                    arg.declarations.push(*var);
                    return false;
                }
            };
            true
        });

        if let Some(name) = fun.name() {
            let fun = Function {
                name: name.as_name(),
                ty: fun.ty().map_or(Type::Real, |ty| ty.as_type()),
                args,
                items,
                ast_id: self.source_ast_id_map.ast_id(&fun),
            };
            let fun = self.tree.data.functions.push_and_get_key(fun);
            dst.push(fun.into())
        }
    }

    /// Resolves a branch endpoint to a `Path`: a plain endpoint resolves its `ast::Path`
    /// normally (a bare reference to a bus base name is detected and diagnosed by the
    /// `finalize_branch_buses` post-pass once all of the module's buses are known); a
    /// bit-select endpoint (`bus[2]`) constant-folds the index and synthesizes the same
    /// `"bus[2]"` path the bus's expanded scalar `Node` was declared under (see
    /// `expand_bus_names`). A non-constant index is diagnosed and fails to resolve (the
    /// branch becomes `BranchKind::Missing`).
    fn resolve_branch_endpoint(
        &mut self,
        endpoint: ast::BranchEndpoint,
        ast_id: ErasedAstId,
    ) -> Option<Path> {
        match endpoint {
            ast::BranchEndpoint::Plain(path) => Path::resolve(path),
            ast::BranchEndpoint::BitSelect(base, index) => {
                let base_name = Path::resolve(base)?.as_ident()?;
                let idx = match index.as_constexprval() {
                    Some(ConstExprValue::Int(i)) => i,
                    _ => {
                        self.tree
                            .diagnostics
                            .push(ItemTreeDiagnostic::NonConstantBranchBitSelect { ast_id });
                        return None;
                    }
                };
                Some(Path::new_ident(super::bus_bit_name(&base_name, idx)))
            }
        }
    }

    fn lower_branch(&mut self, decl: ast::BranchDecl, dst: &mut Vec<ModuleItem>) {
        let ast_id = self.source_ast_id_map.ast_id(&decl);
        let kind = decl
            .branch_kind()
            .and_then(|kind| {
                let res = match kind {
                    ast::BranchKind::PortFlow(flow) => {
                        BranchKind::PortFlow(Path::resolve(flow.port()?)?)
                    }
                    ast::BranchKind::NodeGnd(node) => {
                        BranchKind::NodeGnd(self.resolve_branch_endpoint(node, ast_id.into())?)
                    }
                    ast::BranchKind::Nodes(hi, lo) => BranchKind::Nodes(
                        self.resolve_branch_endpoint(hi, ast_id.into())?,
                        self.resolve_branch_endpoint(lo, ast_id.into())?,
                    ),
                };
                Some(res)
            })
            .unwrap_or(BranchKind::Missing);
        for (name_idx, name) in decl.names().enumerate() {
            let branch = Branch { name: name.as_name(), kind: kind.clone(), ast_id, name_idx };
            let id = self.tree.data.branches.push_and_get_key(branch);
            dst.push(id.into());
        }
    }

    /// Post-pass run once a module's `buses` registry is fully known: diagnoses branch
    /// endpoints that referenced a bus by its bare base name with no bit-select (which
    /// `resolve_branch_endpoint` would otherwise have resolved as an ordinary, and
    /// nonexistent, node path, only to fail name resolution later with a confusing
    /// "not found" error).
    fn check_branch_bus_refs(&mut self, dst: &[ModuleItem], buses: &[BusDecl]) {
        if buses.is_empty() {
            return;
        }
        for item in dst {
            if let ModuleItem::Branch(id) = item {
                let branch = &self.tree.data.branches[*id];
                let ast_id = branch.ast_id.into();
                let endpoints: Vec<&Path> = match &branch.kind {
                    BranchKind::PortFlow(p) | BranchKind::NodeGnd(p) => vec![p],
                    BranchKind::Nodes(p1, p2) => vec![p1, p2],
                    BranchKind::Missing => vec![],
                };
                for path in endpoints {
                    let Some(ident) = path.as_ident() else { continue };
                    if let Some(bus) = buses.iter().find(|b| b.base_name == ident) {
                        // bare reference to a bus base name with no bit-select
                        self.tree.diagnostics.push(ItemTreeDiagnostic::BareBusReferenceInBranch {
                            ast_id,
                            bus_name: bus.base_name.clone(),
                        });
                        continue;
                    }
                    // a synthesized "base[idx]" bit-select path: range-check it against
                    // the bus's declared width, if its base matches a known bus.
                    if let Some((base, idx)) = parse_synthesized_bit_name(&ident) {
                        if let Some(bus) = buses.iter().find(|b| b.base_name == base) {
                            if !bus.contains_bit(idx) {
                                self.tree.diagnostics.push(
                                    ItemTreeDiagnostic::BranchBitSelectOutOfRange {
                                        ast_id,
                                        bus_name: bus.base_name.clone(),
                                        index: idx,
                                        msb: bus.msb,
                                        lsb: bus.lsb,
                                    },
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    fn lower_module_ports(
        &mut self,
        ports: ast::ModulePorts,
        nodes: &mut TiVec<LocalNodeId, Node>,
        dst: &mut Vec<ModuleItem>,
        buses: &mut Vec<BusDecl>,
    ) {
        for port in ports.ports() {
            let ast_id = self.source_ast_id_map.ast_id(&port);
            match port.kind() {
                ast::ModulePortKind::Name(name) => {
                    let name = name.as_name();
                    if nodes.iter().all(|node| node.name != name) {
                        let node = nodes.push_and_get_key(Node {
                            name,
                            is_port: true,
                            ast_id: ast_id.into(),
                            decls: Vec::new(),
                        });
                        dst.push(node.into())
                    }
                }
                ast::ModulePortKind::PortDecl(decl) => {
                    self.lower_port_decl(decl, nodes, dst, buses);
                }
            }
        }
    }

    /// Expands a (possibly vectored) declaration's name list into the list of
    /// scalar names to actually declare, registering a `BusDecl` (and
    /// diagnosing non-constant widths) as needed. Each entry is
    /// `(name, name_idx)` where `name_idx` mirrors the original `enumerate()`
    /// index of the *declared* (un-expanded) name, matching existing
    /// multi-declaration semantics.
    /// Like the result of expansion, but additionally marks the *first* synthesized bit of
    /// each bus with the original (un-expanded) base name. This lets callers merge a bus's
    /// first bit into a pre-existing module-head port placeholder declared under the bare
    /// base name (e.g. `module m(in, out); output [3:0] out;` — the header's bare `out`
    /// placeholder has to become `out[0]`, not be left dangling), without disturbing the
    /// stable `LocalNodeId` indices any other declaration may already reference.
    fn expand_bus_names(
        &mut self,
        width: Option<ast::Range>,
        names: ast::AstChildren<ast::Name>,
        ast_id: ErasedAstId,
        buses: &mut Vec<BusDecl>,
    ) -> Vec<(Name, usize, Option<Name>)> {
        let Some(width) = width else {
            return names.enumerate().map(|(idx, name)| (name.as_name(), idx, None)).collect();
        };

        let mut res = Vec::new();
        for (name_idx, name) in names.enumerate() {
            let base_name = name.as_name();
            match fold_width_range(&width) {
                Some((msb, lsb)) => {
                    buses.push(BusDecl { base_name: base_name.clone(), msb, lsb, ast_id });
                    let (lo, hi) = if msb >= lsb { (lsb, msb) } else { (msb, lsb) };
                    // declare from lsb to msb (ascending), matching natural bit order;
                    // direction of the original [msb:lsb] only affects range checks
                    for bit in lo..=hi {
                        let merge_base = if bit == lo { Some(base_name.clone()) } else { None };
                        res.push((super::bus_bit_name(&base_name, bit), name_idx, merge_base));
                    }
                }
                None => {
                    self.tree
                        .diagnostics
                        .push(ItemTreeDiagnostic::NonConstantBusWidth { ast_id });
                    // fall back to a scalar declaration so compilation proceeds
                    res.push((base_name, name_idx, None));
                }
            }
        }
        res
    }

    /// Finds the node a declared name should attach to: an exact match, or (for the first bit
    /// of a bus) a still-unresolved module-head port placeholder declared under the bus's bare
    /// base name.
    fn find_node_for_decl<'n>(
        nodes: &'n mut TiVec<LocalNodeId, Node>,
        name: &Name,
        merge_base: &Option<Name>,
    ) -> Option<&'n mut Node> {
        if nodes.iter().any(|node| &node.name == name) {
            return nodes.iter_mut().find(|node| &node.name == name);
        }
        let base = merge_base.as_ref()?;
        let node = nodes.iter_mut().find(|node| &node.name == base && node.decls.is_empty())?;
        node.name = name.clone();
        Some(node)
    }

    fn lower_port_decl(
        &mut self,
        decl: ast::PortDecl,
        nodes: &mut TiVec<LocalNodeId, Node>,
        dst: &mut Vec<ModuleItem>,
        buses: &mut Vec<BusDecl>,
    ) {
        let discipline = decl.discipline().map(|it| it.as_name());
        let direction = decl.direction();

        let is_gnd = decl.net_type_token().map_or(false, |it| it.text() == kw::raw::ground);
        let ast_id = self.source_ast_id_map.ast_id(&decl);
        let names = self.expand_bus_names(decl.width(), decl.names(), ast_id.into(), buses);
        for (name, name_idx, merge_base) in names {
            let id = self.tree.data.ports.push_and_get_key(Port {
                name: name.clone(),
                discipline: discipline.clone(),
                is_input: is_input(&direction),
                is_output: is_output(&direction),
                ast_id,
                name_idx,
                is_gnd,
            });

            match Self::find_node_for_decl(nodes, &name, &merge_base) {
                Some(node) => node.decls.push(id.into()),
                None => {
                    let node = nodes.push_and_get_key(Node {
                        name,
                        is_port: true,
                        ast_id: ast_id.into(),
                        decls: vec![id.into()],
                    });
                    dst.push(node.into())
                }
            }
        }
    }

    fn lower_net_decl(
        &mut self,
        decl: ast::NetDecl,
        nodes: &mut TiVec<LocalNodeId, Node>,
        dst: &mut Vec<ModuleItem>,
        buses: &mut Vec<BusDecl>,
    ) {
        let discipline = decl.discipline().map(|it| it.as_name());
        let ast_id = self.source_ast_id_map.ast_id(&decl);

        let is_gnd = decl.net_type_token().map_or(false, |it| it.text() == kw::raw::ground);
        let names = self.expand_bus_names(decl.width(), decl.names(), ast_id.into(), buses);
        for (name, name_idx, merge_base) in names {
            let id = self.tree.data.nets.push_and_get_key(Net {
                name: name.clone(),
                discipline: discipline.clone(),
                ast_id,
                is_gnd,
                name_idx,
            });

            match Self::find_node_for_decl(nodes, &name, &merge_base) {
                Some(node) => node.decls.push(id.into()),
                None => {
                    let node = nodes.push_and_get_key(Node {
                        name,
                        is_port: false,
                        ast_id: ast_id.into(),
                        decls: vec![id.into()],
                    });
                    dst.push(node.into());
                }
            }
        }
    }

    fn lower_stmt<
        T: From<ItemTreeId<Param>> + From<ItemTreeId<Var>> + From<AstId<ast::BlockStmt>>,
    >(
        &mut self,
        stmt: ast::Stmt,
        parent_scope: &mut Vec<T>,
    ) {
        let mut block_stack = Vec::new();
        let mut block_scope_stack = Vec::new();
        let mut blocks = mem::take(&mut self.tree.blocks);

        for event in stmt.syntax().preorder() {
            match event {
                WalkEvent::Enter(node) => {
                    match_ast! {
                        match node {
                            ast::BlockStmt(block) => {
                                let ast_id = self.source_ast_id_map.ast_id(&block);
                                let name = block.block_scope().and_then(|it| Some(it.name()?.as_name()));
                                let block_info = Block { name, scope_items: Vec::new()};
                                if block.block_scope().is_some() {
                                    match block_scope_stack.last() {
                                        Some(block) => {
                                            let block = blocks.get_mut(block).unwrap();
                                             block.scope_items.push(ast_id.into());
                                        }
                                        None =>  parent_scope.push(ast_id.into()),
                                    };

                                    block_scope_stack.push(ast_id);
                                }

                                blocks.insert(ast_id, block_info);
                                block_stack.push(ast_id);
                            },
                            ast::VarDecl(var) => {
                              match block_stack.last() {
                                    Some(block) => {
                                        let block = blocks.get_mut(block).unwrap();
                                        self.lower_var(var, &mut block.scope_items)
                                    }
                                    None => self.lower_var(var, parent_scope),
                                }
                            },
                            ast::ParamDecl(param) => {
                              match block_stack.last() {
                                    Some(block) => {
                                        let block = blocks.get_mut(block).unwrap();
                                        self.lower_param(param, &mut block.scope_items)
                                    }
                                 None => self.lower_param(param, parent_scope),
                                }
                            },
                            _ => ()
                        }
                    }
                }
                WalkEvent::Leave(node) => {
                    if let Some(block) = ast::BlockStmt::cast(node) {
                        block_stack.pop();
                        if block.block_scope().is_some() {
                            block_scope_stack.pop();
                        }
                    }
                }
            }
        }

        self.tree.blocks = blocks;
    }

    fn lower_var<T: From<ItemTreeId<Var>>>(&mut self, decl: ast::VarDecl, dst: &mut Vec<T>) {
        let ty = decl.ty().as_type();
        for var in decl.vars() {
            if let Some(name) = var.name() {
                let var = Var {
                    name: name.as_name(),
                    ast_id: self.source_ast_id_map.ast_id(&var),
                    ty: ty.clone(),
                };
                let id = self.tree.data.variables.push_and_get_key(var);
                dst.push(id.into())
            }
        }
    }

    fn lower_param<T: From<ItemTreeId<Param>>>(&mut self, decl: ast::ParamDecl, dst: &mut Vec<T>) {
        let ty = decl.ty().map(|ty| ty.as_type());
        for param in decl.paras() {
            if let Some(name) = param.name() {
                let ast_id = self.source_ast_id_map.ast_id(&param);
                let param = Param {
                    name: name.as_name(),
                    is_local: decl.localparam_token().is_some(),
                    ty: ty.clone(),
                    ast_id,
                };
                let id = self.tree.data.parameters.push_and_get_key(param);
                dst.push(id.into())
            }
        }
    }

    fn lower_alias_param<T: From<ItemTreeId<AliasParam>>>(
        &mut self,
        decl: ast::AliasParam,
        dst: &mut Vec<T>,
    ) {
        let name = decl.name();
        let src = decl.src();

        if let (Some(name), Some(src)) = (name, src) {
            let src = match src {
                ParamRef::Path(path) => Path::resolve(path),
                ParamRef::SysFun(fun) => Some(Path::new_ident(fun.as_name())),
            };
            let param = AliasParam {
                name: name.as_name(),
                src,
                ast_id: self.source_ast_id_map.ast_id(&decl),
            };
            let param = self.tree.data.alias_parameters.push_and_get_key(param);
            dst.push(param.into())
        }
    }
}
