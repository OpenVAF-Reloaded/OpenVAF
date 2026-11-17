use std::iter::once;

use basedb::{AstId, ErasedAstId, FileId};
use hir_def::nameres::diagnostics::PathResolveError;
use hir_def::nameres::{DefMap, ScopeDefItem};
use hir_def::{
    AliasParamId, Branch, BranchId, BranchKind, DisciplineAttr, DisciplineId, DisciplineSlot,
    Domain, ItemLoc, ItemTree, ItemTreeId, LocalDisciplineAttrId, LocalNatureAttrId, Lookup,
    ModuleId, ModuleLoc, NatureAttr, NatureId, NodeId, NodeTypeDecl, Path, ScopeId,
};
use syntax::ast::ArgListOwner;
use syntax::name::Name;
use syntax::{ast, AstNode, SyntaxNodePtr};
use typed_index_collections::TiSlice;

use crate::db::HirTyDB;
use crate::lower::{lookup_nature, parent_of, DisciplineTy, NatureKey, NatureTy};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct DuplicateItem<Item, Def> {
    pub src: Def,
    pub first: Item,
    pub subsequent: Vec<Item>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum TypeValidationDiagnostic {
    PathError { err: PathResolveError, src: SyntaxNodePtr },
    DuplicateDisciplineAttr(DuplicateItem<LocalDisciplineAttrId, DisciplineId>),
    DuplicateNatureAttr(DuplicateItem<LocalNatureAttrId, NatureId>),
    MultipleDirections(DuplicateItem<AstId<ast::PortDecl>, NodeId>),
    MultipleDisciplines(DuplicateItem<ErasedAstId, NodeId>),
    MultipleGnds(DuplicateItem<ErasedAstId, NodeId>),
    PortWithoutDirection { decl: ErasedAstId, name: Name },
    NodeWithoutDiscipline { decl: ErasedAstId, name: Name },
    ExpectedPort { node: NodeId, src: ErasedAstId },
    IncompatibleBranch { branch: BranchId, node1: NodeId, node2: NodeId },
    NatureDiscipline { kind: NatureDisciplineError, src: ErasedAstId },
}

/// Errors in nature and discipline declarations
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum NatureDisciplineError {
    /// unresolved parent, ddt_nature, idt_nature or bound nature
    Unresolved { err: PathResolveError },
    /// a parent nature declared after the nature
    ParentDeclaredLater { nature: Name, parent: Name },
    /// the parent chain reaches the nature again
    ParentCycle { nature: Name },
    /// units / access set by a derived nature or a discipline override
    IllegalOverride { attr: &'static str, owner: String },
    /// a base nature without units / access / abstol
    MissingAttr { nature: Name, attr: &'static str },
    /// ddt_nature / idt_nature override that does not share a base nature with the parent's value
    UnrelatedDtNature { attr: &'static str, value: String, parent: String, parent_value: String },
    /// potential and flow natures of a discipline have the same access function
    SameAccess { discipline: Name, access: String },
    /// a discrete discipline with nature bindings
    DiscreteWithNatures { discipline: Name },
}

impl TypeValidationDiagnostic {
    pub fn collect(db: &dyn HirTyDB, root_file: FileId) -> Vec<TypeValidationDiagnostic> {
        let mut res = Vec::new();

        let def_map = db.def_map(root_file);
        let tree = db.item_tree(root_file);
        TypeValidationCtx { db, dst: &mut res, def_map: &def_map, tree: &tree, root_file }
            .validate();

        res
    }
}

struct TypeValidationCtx<'a> {
    db: &'a dyn HirTyDB,
    dst: &'a mut Vec<TypeValidationDiagnostic>,
    def_map: &'a DefMap,
    tree: &'a ItemTree,
    root_file: FileId,
}

impl TypeValidationCtx<'_> {
    fn validate(&mut self) {
        let root = &self.def_map[self.def_map.root()];
        for def in root.declarations.values() {
            match *def {
                ScopeDefItem::NatureId(nature) => self.verify_nature(nature),
                ScopeDefItem::DisciplineId(discipline) => self.verify_discipline(discipline),
                ScopeDefItem::ModuleId(module) => self.verify_module(module),
                _ => (),
            }
        }
    }

    fn verify_module(&mut self, module: ModuleId) {
        let loc = module.lookup(self.db.upcast());
        let scope = loc.scope.local_scope;
        for item in self.def_map[scope].declarations.values() {
            match item {
                ScopeDefItem::NodeId(node) => self.verify_node(*node, loc),
                ScopeDefItem::BranchId(branch) => self.verify_branch(*branch),
                ScopeDefItem::AliasParamId(alias) => self.verify_alias(*alias),
                _ => (),
            }
        }
    }

    fn resolve_node(
        &mut self,
        node: &Path,
        scope: ScopeId,
        branch: &ItemLoc<Branch>,
    ) -> Option<NodeId> {
        let node = scope.resolve_item_path::<NodeId>(self.db.upcast(), node);
        match node {
            Ok(node) => Some(node),
            Err(err) => {
                let src = SyntaxNodePtr::new(
                    branch
                        .source(self.db.upcast())
                        .arg_list()
                        .unwrap()
                        .args()
                        .next()
                        .unwrap()
                        .syntax(),
                );
                self.report(TypeValidationDiagnostic::PathError { err, src });
                None
            }
        }
    }

    fn verify_alias(&mut self, alias: AliasParamId) {
        if self.db.resolve_alias(alias).is_none() {
            let loc = alias.lookup(self.db.upcast());
            let data = self.db.alias_data(alias);
            if let Some(path) = data.src.as_ref() {
                match loc.scope.resolve_path(self.db.upcast(), path) {
                    // TODO: better errors for cycels
                    Ok(found) => {
                        let src = SyntaxNodePtr::new(
                            loc.source(self.db.upcast()).src().unwrap().syntax(),
                        );
                        self.report(TypeValidationDiagnostic::PathError {
                            err: PathResolveError::ExpectedItemKind {
                                name: path.segments.last().unwrap().clone(),
                                expected: "parameter",
                                found,
                            },
                            src,
                        })
                    }
                    Err(err) => {
                        let src = SyntaxNodePtr::new(
                            loc.source(self.db.upcast()).src().unwrap().syntax(),
                        );
                        self.report(TypeValidationDiagnostic::PathError { err, src })
                    }
                }
            }
        }
    }

    fn report(&mut self, diag: impl Into<TypeValidationDiagnostic>) {
        self.dst.push(diag.into())
    }

    fn verify_branch(&mut self, branch_: BranchId) {
        let branch_data = self.db.branch_data(branch_);
        let kind = &branch_data.kind;
        let branch = branch_.lookup(self.db.upcast());
        let scope = branch.scope;
        match kind {
            BranchKind::PortFlow(port) => {
                if let Some(node) = self.resolve_node(port, scope, &branch) {
                    let node_ = self.db.node_data(node);
                    if !node_.is_input && !node_.is_output {
                        let src = branch.ast_id(self.db.upcast()).into();
                        self.report(TypeValidationDiagnostic::ExpectedPort { node, src });
                    }
                }
            }
            BranchKind::NodeGnd(node) => {
                self.resolve_node(node, scope, &branch);
            }
            BranchKind::Nodes(node1, node2) => {
                let node1 = self.resolve_node(node1, scope, &branch);
                let node2 = self.resolve_node(node2, scope, &branch);
                let (node1, node2) = if let (Some(node1), Some(node2)) = (node1, node2) {
                    (node1, node2)
                } else {
                    return;
                };

                let discipline1 = self.db.node_discipline(node1);
                let discipline2 = self.db.node_discipline(node2);
                // fast path
                if discipline1 == discipline2 {
                    return;
                }

                let (discipline1, discipline2) =
                    if let (Some(d1), Some(d2)) = (discipline1, discipline2) {
                        (d1, d2)
                    } else {
                        return;
                    };

                if !DisciplineTy::compatible(self.db, discipline1, discipline2) {
                    self.report(TypeValidationDiagnostic::IncompatibleBranch {
                        branch: branch_,
                        node1,
                        node2,
                    })
                }
            }
            BranchKind::Missing => (),
        };
    }

    fn verify_node(&mut self, node: NodeId, module: ModuleLoc) {
        let loc = node.lookup(self.db.upcast());
        let node_ = &self.tree[module.id].nodes[loc.id];
        if node_.decls.is_empty() {
            self.report(TypeValidationDiagnostic::PortWithoutDirection {
                decl: node_.ast_id,
                name: node_.name.clone(),
            });
            self.report(TypeValidationDiagnostic::NodeWithoutDiscipline {
                decl: node_.ast_id,
                name: node_.name.clone(),
            });
            return; // Do not print other diagnostics here would just lead to duplications
        }
        let mut directions = node_.decls.iter().filter_map(|decl| {
            if let NodeTypeDecl::Port(p) = decl {
                Some(self.tree[*p].ast_id)
            } else {
                None
            }
        });
        if let Some(first) = directions.next() {
            let duplicates: Vec<_> = directions.collect();
            if !duplicates.is_empty() {
                self.report(TypeValidationDiagnostic::MultipleDirections(DuplicateItem {
                    src: node,
                    first,
                    subsequent: duplicates,
                }))
            }
        } else if node_.decls[0].ast_id(self.tree) != node_.ast_id {
            self.report(TypeValidationDiagnostic::PortWithoutDirection {
                decl: node_.ast_id,
                name: node_.name.clone(),
            })
        }

        let mut disciplines = node_
            .decls
            .iter()
            .filter_map(|it| it.discipline(self.tree).as_ref().map(|discipline| (it, discipline)));

        if let Some((decl, discipline)) = disciplines.next() {
            for (decl, discipline) in once((decl, discipline)).chain(disciplines.clone()) {
                if let Err(err) = self
                    .def_map
                    .resolve_local_item_in_scope::<DisciplineId>(self.def_map.root(), discipline)
                {
                    self.report(TypeValidationDiagnostic::PathError {
                        err,
                        src: SyntaxNodePtr::new(
                            decl.discipline_src(self.db.upcast(), self.root_file).unwrap().syntax(),
                        ),
                    })
                }
            }

            let duplicates: Vec<_> = disciplines.map(|(decl, _)| decl.ast_id(self.tree)).collect();
            if !duplicates.is_empty() {
                self.report(TypeValidationDiagnostic::MultipleDisciplines(DuplicateItem {
                    src: node,
                    first: decl.ast_id(self.tree),
                    subsequent: duplicates,
                }))
            }
        } else {
            self.report(TypeValidationDiagnostic::NodeWithoutDiscipline {
                decl: node_.ast_id,
                name: node_.name.clone(),
            });
        }

        let mut gnd_declarations = node_.decls.iter().filter(|it| it.is_gnd(self.tree));

        if let Some(first) = gnd_declarations.next() {
            let duplicates: Vec<_> = gnd_declarations.map(|it| it.ast_id(self.tree)).collect();
            if !duplicates.is_empty() {
                self.report(TypeValidationDiagnostic::MultipleDisciplines(DuplicateItem {
                    src: node,
                    first: first.ast_id(self.tree),
                    subsequent: duplicates,
                }))
            }
        }
    }

    fn report_nd(&mut self, kind: NatureDisciplineError, src: impl Into<ErasedAstId>) {
        self.report(TypeValidationDiagnostic::NatureDiscipline { kind, src: src.into() })
    }

    /// Name of a nature as seen by the simulator (`d.potential` / `d.flow` for hidden natures)
    fn nature_key_name(&self, nature: NatureKey) -> String {
        match nature {
            NatureKey::Decl(nature) => self.db.nature_data(nature).name.to_string(),
            NatureKey::Slot(discipline, slot) => {
                format!("{}.{}", self.db.discipline_data(discipline).name, slot.name())
            }
        }
    }

    /// Checks that an override of ddt_nature / idt_nature (in a derived nature or a discipline)
    /// shares a base nature with the parent's value.
    fn verify_dt_override(
        &mut self,
        attr: &'static str,
        value: NatureKey,
        parent: NatureKey,
        src: ErasedAstId,
    ) {
        let parent_info = self.db.nature_info(parent);
        let parent_val =
            if attr == "ddt_nature" { parent_info.ddt_nature } else { parent_info.idt_nature };
        if !NatureTy::related(self.db, value, parent_val) {
            let kind = NatureDisciplineError::UnrelatedDtNature {
                attr,
                value: self.nature_key_name(value),
                parent: self.nature_key_name(parent),
                parent_value: self.nature_key_name(parent_val),
            };
            self.report_nd(kind, src)
        }
    }

    fn verify_discipline(&mut self, discipline: DisciplineId) {
        let data = self.db.discipline_data(discipline);
        self.verify_unique_attributes(
            &data.attrs,
            discipline,
            TypeValidationDiagnostic::DuplicateDisciplineAttr,
        );

        let loc = discipline.lookup(self.db.upcast());
        let decl = &self.tree[loc.id];
        let info = self.db.discipline_info(discipline);
        let tree = self.tree;
        let attr_src = |attr: LocalDisciplineAttrId| -> ErasedAstId {
            let id = usize::from(decl.extra_attrs.start()) + usize::from(attr);
            tree[ItemTreeId::<DisciplineAttr>::from(id)].ast_id.into()
        };

        // bound natures must be declared natures
        let bindings =
            [(DisciplineSlot::Potential, &decl.potential), (DisciplineSlot::Flow, &decl.flow)];
        for (slot, binding) in bindings {
            if let Some((nature_ref, attr)) = binding {
                if info.slot(slot).is_none() {
                    let err = match lookup_nature(self.def_map, nature_ref, self.db) {
                        Err(err) => err,
                        // a discipline slot is not a nature identifier (syntax error)
                        Ok(_) => continue,
                    };
                    let src = attr_src(*attr);
                    self.report_nd(NatureDisciplineError::Unresolved { err }, src);
                }
            }
        }

        // potential and flow must not share an access function
        if let (Some(potential), Some(flow)) = (info.potential, info.flow) {
            if NatureTy::related(self.db, NatureKey::Decl(potential), NatureKey::Decl(flow)) {
                let access = self.db.nature_info(NatureKey::Decl(flow)).access.clone();
                let src = attr_src(decl.flow.as_ref().unwrap().1);
                let kind = NatureDisciplineError::SameAccess {
                    discipline: data.name.clone(),
                    access: access.map(|it| it.to_string()).unwrap_or_default(),
                };
                self.report_nd(kind, src);
            }
        }

        // discrete disciplines can't have natures
        if let Some((Domain::Discrete, attr)) = decl.domain {
            if decl.potential.is_some() || decl.flow.is_some() {
                let kind =
                    NatureDisciplineError::DiscreteWithNatures { discipline: data.name.clone() };
                self.report_nd(kind, attr_src(attr));
            }
        }

        // overrides
        let attrs: Vec<&DisciplineAttr> = decl.extra_attrs.clone().map(|id| &tree[id]).collect();
        for (i, attr) in attrs.iter().enumerate() {
            let Some(slot) = attr.kind.slot() else { continue };
            let src: ErasedAstId = attr.ast_id.into();
            match &*attr.name {
                "units" | "access" => {
                    let kind = NatureDisciplineError::IllegalOverride {
                        attr: if &*attr.name == "units" { "units" } else { "access" },
                        owner: format!("{}.{}", data.name, slot.name()),
                    };
                    self.report_nd(kind, src)
                }
                name @ ("ddt_nature" | "idt_nature") => {
                    let Some(nature_ref) = &attr.nature else { continue };
                    // only the first override is used, duplicates are reported separately
                    let first =
                        attrs.iter().position(|it| it.kind == attr.kind && it.name == attr.name);
                    if first != Some(i) {
                        continue;
                    }
                    let attr_name = if name == "ddt_nature" { "ddt_nature" } else { "idt_nature" };
                    match lookup_nature(self.def_map, nature_ref, self.db) {
                        Ok(value) => {
                            if let Some(bound) = info.slot(slot) {
                                self.verify_dt_override(
                                    attr_name,
                                    value,
                                    NatureKey::Decl(bound),
                                    src,
                                )
                            }
                        }
                        Err(err) => self.report_nd(NatureDisciplineError::Unresolved { err }, src),
                    }
                }
                _ => (),
            }
        }
    }

    fn verify_nature(&mut self, nature: NatureId) {
        let data = self.db.nature_data(nature);

        self.verify_unique_attributes(
            &data.attrs,
            nature,
            TypeValidationDiagnostic::DuplicateNatureAttr,
        );

        let loc = nature.lookup(self.db.upcast());
        let decl = &self.tree[loc.id];
        let decl_src: ErasedAstId = decl.ast_id.into();
        let tree = self.tree;
        let attr_src = |attr: LocalNatureAttrId| -> ErasedAstId {
            let id = usize::from(decl.attrs.start()) + usize::from(attr);
            tree[ItemTreeId::<NatureAttr>::from(id)].ast_id.into()
        };
        let name = data.name.clone();

        let parent = match &decl.parent {
            None => {
                // base nature: units, access and abstol are required
                let missing = [
                    ("units", decl.units.is_none()),
                    ("access", decl.access.is_none()),
                    ("abstol", decl.abstol.is_none()),
                ];
                for (attr, missing) in missing {
                    if missing {
                        let kind =
                            NatureDisciplineError::MissingAttr { nature: name.clone(), attr };
                        self.report_nd(kind, decl_src);
                    }
                }
                None
            }
            Some(parent_ref) => {
                // derived nature: units and access are inherited
                let overrides = [
                    ("units", decl.units.as_ref().map(|it| it.1)),
                    ("access", decl.access.as_ref().map(|it| it.1)),
                ];
                for (attr, src) in overrides {
                    if let Some(src) = src {
                        let kind = NatureDisciplineError::IllegalOverride {
                            attr,
                            owner: name.to_string(),
                        };
                        self.report_nd(kind, attr_src(src));
                    }
                }

                match lookup_nature(self.def_map, parent_ref, self.db) {
                    Ok(parent) => {
                        // a parent nature must be declared before the nature
                        if let NatureKey::Decl(parent_nature) = parent {
                            if parent_nature.lookup(self.db.upcast()).id >= loc.id {
                                let kind = NatureDisciplineError::ParentDeclaredLater {
                                    nature: name.clone(),
                                    parent: self.db.nature_data(parent_nature).name.clone(),
                                };
                                self.report_nd(kind, decl_src);
                            }
                        }
                        Some(parent)
                    }
                    Err(err) => {
                        self.report_nd(NatureDisciplineError::Unresolved { err }, decl_src);
                        None
                    }
                }
            }
        };

        // parent cycles: report at every nature on the cycle
        let start = NatureKey::Decl(nature);
        let mut visited = vec![start];
        let mut curr = start;
        while let Some(next) = parent_of(self.db, curr) {
            if next == start {
                self.report_nd(
                    NatureDisciplineError::ParentCycle { nature: name.clone() },
                    decl_src,
                );
                break;
            }
            if visited.contains(&next) {
                break;
            }
            visited.push(next);
            curr = next;
        }

        // ddt_nature / idt_nature
        let dt_attrs = [("ddt_nature", &decl.ddt_nature), ("idt_nature", &decl.idt_nature)];
        for (attr, value) in dt_attrs {
            let Some((nature_ref, attr_id)) = value else { continue };
            let src = attr_src(*attr_id);
            match lookup_nature(self.def_map, nature_ref, self.db) {
                Ok(value) => {
                    if let Some(parent) = parent {
                        self.verify_dt_override(attr, value, parent, src)
                    }
                }
                Err(err) => self.report_nd(NatureDisciplineError::Unresolved { err }, src),
            }
        }
    }

    fn verify_unique_attributes<Attr: From<usize> + PartialEq, Def: Copy>(
        &mut self,
        attrs: &TiSlice<Attr, impl PartialEq>,
        def: Def,
        wrap_err: impl Fn(DuplicateItem<Attr, Def>) -> TypeValidationDiagnostic,
    ) {
        // This is quadratic (actually its n(n+1)/2). But disciplines and nature usually only have very few (below 5)
        // attributes so this is probably faster than allocating a HashMap. If this ever becomes a
        // problem just use a HashMap instead
        for (id, attr) in attrs.iter_enumerated() {
            let mut duplicates =
                attrs.iter_enumerated().filter_map(
                    |it| {
                        if it.1 == attr {
                            Some(it.0)
                        } else {
                            None
                        }
                    },
                );

            if duplicates.next().unwrap() != id {
                continue;
            }

            let duplicates: Vec<_> = duplicates.collect();

            if !duplicates.is_empty() {
                let err = DuplicateItem { src: def, first: id, subsequent: duplicates };
                self.report(wrap_err(err))
            }
        }
    }
}
