use std::collections::HashSet;
use std::sync::Arc;

use arena::Arena;
use basedb::{AstId, ErasedAstId, FileId};
use indexmap::IndexMap;
use syntax::name::{AsName, Name};
use syntax::{ast, AstNode};

use super::diagnostics::DefDiagnostic;
use super::{DefMap, DefMapSource, LocalScopeId, Scope, ScopeDefItem, ScopeOrigin};
use crate::builtin::insert_module_builtin_scope;
use crate::db::HirDefDB;
use crate::item_tree::{
    BlockScopeItem, Function, FunctionItem, Instantiation, ItemTree, ItemTreeId, ItemTreeNode,
    Module, ModuleItem, RootItem,
};
use crate::{
    BlockId, BlockLoc, DisciplineLoc, FunctionArgLoc, FunctionId, FunctionLoc, Intern, ItemLoc,
    Lookup, ModuleId, ModuleLoc, NatureAttrLoc, NatureLoc, NodeLoc, ScopeId,
};

/// The public `.name` every built-in ngspice device (`SPICEdev::DEVpublic`)
/// registers itself under -- i.e. exactly the set of strings that make a
/// same-named (case-insensitive) OSDI module's `.model` line ambiguous.
/// Collected from `.name = "..."` in every `src/spicelib/devices/*/*.c` in
/// this repo's `ngspice-46/` (see `check_reserved_module_name`); XSPICE
/// code-model names aren't included since those are opt-in and namespaced
/// differently. Deliberately best-effort, not derived at build time from
/// the actual ngspice source -- a missed/renamed entry just means no
/// warning for that one name, not a false positive.
const RESERVED_NGSPICE_DEVICE_NAMES: &[&str] = &[
    "ASRC",
    "B3SOIDD",
    "B3SOIFD",
    "B3SOIPD",
    "B4SOI",
    "BJT",
    "BSIM1",
    "BSIM2",
    "BSIM3",
    "BSIM3v0",
    "BSIM3v1",
    "BSIM3v32",
    "BSIM4",
    "BSIM4v5",
    "BSIM4v6",
    "BSIM4v7",
    "CCCS",
    "CCVS",
    "Capacitor",
    "CplLines",
    "CSwitch",
    "Diode",
    "HFET1",
    "HFET2",
    "HiSIM2",
    "HiSIMHV1",
    "HiSIMHV2",
    "Inductor",
    "Isource",
    "JFET",
    "JFET2",
    "LTRA",
    "MES",
    "MESA",
    "Mos1",
    "Mos2",
    "Mos3",
    "Mos6",
    "Mos9",
    "NBJT",
    "NBJT2",
    "NDEV",
    "NUMD",
    "NUMD2",
    "NUMOS",
    "Resistor",
    "SOI3",
    "Switch",
    "Tranline",
    "TransLine",
    "URC",
    "VBIC",
    "VCCS",
    "VCVS",
    "VDMOS",
    "Vsource",
    "hicum2",
    "mutual",
];

pub fn collect_root_def_map(db: &dyn HirDefDB, root_file: FileId) -> Arc<DefMap> {
    let tree = &db.item_tree(root_file);
    let scope_cnt = tree.data.natures.len() + tree.data.disciplines.len() + tree.data.modules.len();

    let mut collector = DefCollector {
        map: DefMap {
            scopes: Arena::with_capacity(scope_cnt),
            // nodes: Arena::with_capacity(tree.data.nets.len()),
            root_scope: LocalScopeId::from(0u32),
            src: DefMapSource::Root,
            diagnostics: Vec::new(),
        },
        tree,
        db,
        root_file,
    };

    collector.collect_root_map();

    Arc::new(collector.map)
}

pub fn collect_function_map(db: &dyn HirDefDB, function: FunctionId) -> Arc<DefMap> {
    let FunctionLoc { scope: ScopeId { root_file, local_scope, .. }, id } = function.lookup(db);
    let tree = &db.item_tree(root_file);

    let mut collector = DefCollector {
        map: DefMap {
            scopes: Arena::with_capacity(tree.data.modules.len() + 1),
            // nodes: Arena::with_capacity(tree.data.nets.len()),
            src: DefMapSource::Function(function),
            root_scope: LocalScopeId::from(0u32), // This will be changed once the scope has been created
            diagnostics: Vec::new(),
        },
        tree,
        db,
        root_file,
    };

    collector.collect_function_map(id, local_scope, function);

    Arc::new(collector.map)
}

pub fn collect_block_map(db: &dyn HirDefDB, block: BlockId) -> Option<Arc<DefMap>> {
    let BlockLoc { ast, parent } = block.lookup(db);

    let tree = &db.item_tree(parent.root_file);
    let items = &tree.block_scope(ast).scope_items;

    if items.is_empty() {
        return None;
    }

    let mut collector = DefCollector {
        map: DefMap {
            scopes: Arena::with_capacity(1),
            src: DefMapSource::Block(block),
            root_scope: LocalScopeId::from(0u32),
            diagnostics: Vec::new(),
        },
        tree,
        db,
        root_file: parent.root_file,
    };

    collector.collect_block_map(block, items);

    Some(Arc::new(collector.map))
}

struct DefCollector<'a> {
    map: DefMap,
    tree: &'a ItemTree,
    db: &'a dyn HirDefDB,
    root_file: FileId,
}

impl DefCollector<'_> {
    fn collect_function_map(
        &mut self,
        item_tree: ItemTreeId<Function>,
        parent_module: LocalScopeId,
        id: FunctionId,
    ) {
        debug_assert_eq!(self.map.src, DefMapSource::Function(id));

        let root_def_map = self.db.def_map(self.root_file);

        // parent is a placeholder here...
        let scope = self.new_scope(ScopeOrigin::Function(id), LocalScopeId::from(0u32));
        assert_eq!(scope, self.map.entry());

        self.map[scope]
            .declarations
            .insert(self.tree[item_tree].name.clone(), ScopeDefItem::FunctionReturn(id));

        for item in &self.tree[item_tree].items {
            match *item {
                FunctionItem::Scope(ast) => self.collect_block_scope(scope, ast),

                FunctionItem::Parameter(id) => {
                    self.insert_item_decl(scope, self.tree[id].name.clone(), id)
                }
                FunctionItem::Variable(id) => {
                    self.insert_item_decl(scope, self.tree[id].name.clone(), id)
                }
                FunctionItem::FunctionArg(arg) => {
                    let id = FunctionArgLoc { fun: id, id: arg }.intern(self.db);
                    self.insert_decl(scope, self.tree[item_tree].args[arg].name.clone(), id)
                }
            }
        }

        let root = self.new_root_scope(ScopeOrigin::Root);
        self.map.root_scope = root;
        debug_assert_eq!(self.map.root(), root);

        // Copy the modules and their parameters since these are the only declarations outside
        // of the function itself that are accessible insdie an analog function
        let main_root_scope = &root_def_map.scopes[root_def_map.root()];

        let mut parent_module_ = None;

        for (module_name, scope_id) in main_root_scope.children.iter() {
            let scope = &root_def_map[*scope_id];

            if let ScopeOrigin::Module(module) = scope.origin {
                let declarations = scope
                    .declarations
                    .iter()
                    .filter_map(|(name, decl)| {
                        matches!(decl, ScopeDefItem::ParamId(_) | ScopeDefItem::FunctionId(_))
                            .then(|| (name.clone(), *decl))
                    })
                    .collect();

                debug_assert_eq!(scope.parent, Some(root_def_map.root()));

                let scope = Scope {
                    origin: scope.origin,
                    parent: Some(root),
                    children: IndexMap::default(),
                    declarations,
                };

                debug_assert_eq!(scope.parent, Some(root));
                let scope = self.map.scopes.push_and_get_key(scope);

                if *scope_id == parent_module {
                    parent_module_ = Some(scope);
                }

                self.map.scopes[root].children.insert(module_name.clone(), scope);
                self.map.scopes[root].declarations.insert(module_name.clone(), module.into());
            }
        }

        assert!(parent_module_.is_some(), "parent module was not among the root modules");
        self.map[scope].parent = parent_module_;
    }

    fn collect_block_map(&mut self, id: BlockId, items: &[BlockScopeItem]) {
        let scope = self.new_root_scope(id.into());
        debug_assert_eq!(scope, self.map.entry());
        for item in items {
            match *item {
                BlockScopeItem::Scope(ast) => {
                    if let Some(name) = &self.tree.block_scope(ast).name {
                        let loc = BlockLoc {
                            ast,
                            parent: ScopeId {
                                root_file: self.root_file,
                                local_scope: scope,
                                src: self.map.src,
                            },
                        };
                        let id = loc.intern(self.db);
                        self.insert_decl(scope, name.clone(), id);
                    } else {
                        debug_assert!(false)
                    }
                }
                BlockScopeItem::Parameter(id) => {
                    self.insert_item_decl(scope, self.tree[id].name.clone(), id)
                }
                BlockScopeItem::Variable(id) => {
                    self.insert_item_decl(scope, self.tree[id].name.clone(), id)
                }
            }
        }
    }

    // Verilog-ams standard does not specify any way to access user-defined discipline attributes
    // I am guessing this is an oversight but until this is clarified we are not adding this
    // TODO talk to committee about discipline attributes

    fn collect_root_map(&mut self) {
        let root_scope = self.new_root_scope(ScopeOrigin::Root);

        debug_assert_eq!(root_scope, self.map.entry());
        debug_assert_eq!(root_scope, self.map.root());

        // Pass 1: predeclare every module's name (and open its scope)
        // before looking at any module's internal items, so a module
        // instantiation can forward-reference a module declared later in
        // the same file (module declaration order is not significant in
        // Verilog-A, unlike this collector's original single forward pass).
        let mut modules = Vec::new();
        for item in &*self.tree.top_level {
            match *item {
                RootItem::Module(module) => {
                    let (module_id, scope) = self.predeclare_module(module, root_scope);
                    modules.push((module, module_id, scope));
                }
                RootItem::Nature(nature) => {
                    let id = NatureLoc { root_file: self.root_file, id: nature }.intern(self.db);
                    self.insert_decl(root_scope, self.tree[nature].name.clone(), id);
                    if let Some((name, attr)) = self.tree[nature].access.clone() {
                        self.insert_decl(
                            root_scope,
                            name,
                            ScopeDefItem::NatureAccess(
                                NatureAttrLoc { nature: id, id: attr }.intern(self.db).into(),
                            ),
                        )
                    }
                }
                RootItem::Discipline(discipline) => {
                    self.insert_decl(
                        root_scope,
                        self.tree[discipline].name.clone(),
                        DisciplineLoc { root_file: self.root_file, id: discipline }.intern(self.db),
                    );
                }
            }
        }

        // Pass 2: now that every module name in the file is resolvable,
        // check for instantiation cycles and collect each module's
        // internal items (including resolving/diagnosing its
        // instantiations).
        self.check_instantiation_cycles(&modules);
        for &(item_tree, module_id, scope) in &modules {
            self.collect_module_items(item_tree, module_id, scope, root_scope);
        }
    }

    fn predeclare_module(
        &mut self,
        item_tree: ItemTreeId<Module>,
        parent_scope: LocalScopeId,
    ) -> (crate::ModuleId, LocalScopeId) {
        let module_id = ModuleLoc { id: item_tree, scope: self.next_scope() }.intern(self.db);
        let scope = self.new_scope(ScopeOrigin::Module(module_id), parent_scope);
        let module = &self.tree[item_tree];
        self.insert_scope(parent_scope, scope, module.name.clone(), module_id);
        insert_module_builtin_scope(&mut self.map.scopes[scope].declarations);
        self.check_reserved_module_name(module);
        (module_id, scope)
    }

    /// Warns (via the `reserved_module_name` lint, off by default, enabled
    /// with `--warn reserved_module_name`) when a
    /// module's name collides case-insensitively with one of ngspice's
    /// built-in native SPICE device type names -- `.model <name>
    /// <this module>` in a netlist then silently binds to ngspice's
    /// built-in device instead of the OSDI one, a real (and otherwise
    /// silent) footgun. See `RESERVED_NGSPICE_DEVICE_NAMES`'s doc comment
    /// for how this list was derived.
    fn check_reserved_module_name(&mut self, module: &Module) {
        let name = module.name.to_string();
        if let Some(&builtin) =
            RESERVED_NGSPICE_DEVICE_NAMES.iter().find(|b| b.eq_ignore_ascii_case(&name))
        {
            self.map.diagnostics.push(DefDiagnostic::ReservedModuleName {
                ast_id: module.ast_id.into(),
                module: module.name.clone(),
                builtin,
            });
        }
    }

    /// DFS over the file's module-instantiation graph, diagnosing any cycle
    /// (a module directly or transitively instantiating itself) instead of
    /// letting the elaboration pass recurse forever trying to flatten it.
    fn check_instantiation_cycles(
        &mut self,
        modules: &[(ItemTreeId<Module>, ModuleId, LocalScopeId)],
    ) {
        #[derive(Clone, Copy, PartialEq)]
        enum Color {
            White,
            Gray,
            Black,
        }

        let mut color: std::collections::HashMap<ItemTreeId<Module>, Color> =
            modules.iter().map(|&(id, ..)| (id, Color::White)).collect();
        let by_name: std::collections::HashMap<Name, ItemTreeId<Module>> =
            modules.iter().map(|&(id, ..)| (self.tree[id].name.clone(), id)).collect();

        fn instantiated_modules<'a>(
            tree: &'a ItemTree,
            module: ItemTreeId<Module>,
            by_name: &'a std::collections::HashMap<Name, ItemTreeId<Module>>,
        ) -> impl Iterator<Item = (ItemTreeId<Module>, ErasedAstId)> + 'a {
            tree[module].items.iter().filter_map(move |item| match *item {
                ModuleItem::Instantiation(id) => {
                    let inst = &tree[id];
                    by_name.get(&inst.module).map(|&target| (target, inst.ast_id.into()))
                }
                _ => None,
            })
        }

        fn visit(
            tree: &ItemTree,
            module: ItemTreeId<Module>,
            by_name: &std::collections::HashMap<Name, ItemTreeId<Module>>,
            color: &mut std::collections::HashMap<ItemTreeId<Module>, Color>,
            diagnostics: &mut Vec<DefDiagnostic>,
        ) {
            color.insert(module, Color::Gray);
            for (target, ast_id) in instantiated_modules(tree, module, by_name) {
                match color.get(&target).copied().unwrap_or(Color::Black) {
                    Color::Gray => diagnostics.push(DefDiagnostic::CyclicInstantiation {
                        ast_id,
                        module: tree[target].name.clone(),
                    }),
                    Color::White => visit(tree, target, by_name, color, diagnostics),
                    Color::Black => (),
                }
            }
            color.insert(module, Color::Black);
        }

        for &(id, ..) in modules {
            if color.get(&id).copied() == Some(Color::White) {
                visit(self.tree, id, &by_name, &mut color, &mut self.map.diagnostics);
            }
        }
    }

    fn collect_module_items(
        &mut self,
        item_tree: ItemTreeId<Module>,
        module_id: crate::ModuleId,
        scope: LocalScopeId,
        root_scope: LocalScopeId,
    ) {
        let module = &self.tree[item_tree];
        let mut seen_instantiations = HashSet::new();

        for item in &module.items {
            match *item {
                ModuleItem::Scope(ast) => self.collect_block_scope(scope, ast),

                ModuleItem::Node(id) => self.insert_decl(
                    scope,
                    module.nodes[id].name.clone(),
                    NodeLoc { module: module_id, id }.intern(self.db),
                ),
                ModuleItem::Branch(id) => {
                    self.insert_item_decl(scope, self.tree[id].name.clone(), id)
                }
                ModuleItem::Parameter(id) => {
                    self.insert_item_decl(scope, self.tree[id].name.clone(), id)
                }
                ModuleItem::Variable(id) => {
                    self.insert_item_decl(scope, self.tree[id].name.clone(), id)
                }
                ModuleItem::Function(id) => {
                    self.insert_item_decl(scope, self.tree[id].name.clone(), id)
                }
                ModuleItem::AliasParameter(id) => {
                    self.insert_item_decl(scope, self.tree[id].name.clone(), id)
                }
                ModuleItem::Instantiation(id) => {
                    let inst = &self.tree[id];
                    // Every array element of the same `InstanceUnit` shares
                    // one AST node; only cross-check it against the target
                    // module once (still declare each element's name).
                    let first_for_unit = seen_instantiations.insert((inst.ast_id, inst.unit_idx));
                    self.collect_instantiation(id, scope, root_scope, first_for_unit);
                }
            }
        }
    }

    fn collect_instantiation(
        &mut self,
        id: ItemTreeId<Instantiation>,
        scope: LocalScopeId,
        root_scope: LocalScopeId,
        check_against_target: bool,
    ) {
        let inst = self.tree[id].clone();
        let ast_id: ErasedAstId = inst.ast_id.into();

        // Insert the instance name into the module's own scope so
        // "duplicate declaration" diagnostics fire consistently with other
        // item kinds; hierarchical dot-access into an instance is not
        // supported.
        self.insert_item_decl(scope, inst.name.clone(), id);

        let target = match self.map.scopes[root_scope].declarations.get(&inst.module) {
            Some(ScopeDefItem::ModuleId(target)) => *target,
            _ => {
                self.map.diagnostics.push(DefDiagnostic::UnknownInstantiatedModule {
                    ast_id,
                    module: inst.module.clone(),
                });
                return;
            }
        };

        if !check_against_target {
            return;
        }

        let target_tree_id = target.lookup(self.db).id;
        let target_module = &self.tree[target_tree_id];
        let expected_params: Vec<Name> = target_module
            .items
            .iter()
            .filter_map(|item| match item {
                ModuleItem::Parameter(p) => Some(self.tree[*p].name.clone()),
                _ => None,
            })
            .collect();
        let port_names: Vec<Name> = target_module
            .nodes
            .iter()
            .filter(|node| node.is_port)
            .map(|node| node.name.clone())
            .collect();
        let num_ports = target_module.num_ports as usize;

        let ast_id_map = self.db.ast_id_map(self.root_file);
        let ast =
            ast_id_map.get(inst.ast_id).to_node(&self.db.parse(self.root_file).tree().syntax());
        let Some(unit) = ast.instance_units().nth(inst.unit_idx) else { return };

        if let Some(port_conns) = unit.port_conns() {
            let conns: Vec<_> = port_conns.port_conns().collect();
            let all_positional = conns.iter().all(|c| c.name().is_none());
            if all_positional {
                if conns.len() != num_ports {
                    self.map.diagnostics.push(DefDiagnostic::InstancePortCountMismatch {
                        ast_id,
                        instance: inst.name.clone(),
                        module: inst.module.clone(),
                        expected: num_ports,
                        found: conns.len(),
                    });
                }
            } else {
                for conn in &conns {
                    if let Some(name) = conn.name() {
                        let name = name.as_name();
                        if !port_names.contains(&name) {
                            self.map.diagnostics.push(DefDiagnostic::UnknownInstancePort {
                                ast_id,
                                instance: inst.name.clone(),
                                module: inst.module.clone(),
                                port: name,
                            });
                        }
                    }
                }
            }
        }

        if let Some(overrides) = ast.param_overrides() {
            let assigns: Vec<_> = overrides.param_assigns().collect();
            let all_positional = assigns.iter().all(|a| a.name().is_none());
            if all_positional {
                if assigns.len() > expected_params.len() {
                    self.map.diagnostics.push(DefDiagnostic::TooManyInstanceParams {
                        ast_id,
                        instance: inst.name.clone(),
                        module: inst.module.clone(),
                        expected: expected_params.len(),
                        found: assigns.len(),
                    });
                }
            } else {
                for assign in &assigns {
                    if let Some(name) = assign.name() {
                        let name = name.as_name();
                        if !expected_params.contains(&name) {
                            self.map.diagnostics.push(DefDiagnostic::UnknownInstanceParam {
                                ast_id,
                                instance: inst.name.clone(),
                                module: inst.module.clone(),
                                param: name,
                            });
                        }
                    }
                }
            }
        }
    }

    fn collect_block_scope(&mut self, scope: LocalScopeId, ast: AstId<ast::BlockStmt>) {
        let loc = BlockLoc {
            ast,
            parent: ScopeId { root_file: self.root_file, local_scope: scope, src: self.map.src },
        };
        let id = loc.intern(self.db);
        self.insert_decl(
            scope,
            self.tree
                .block_scope(ast)
                .name
                .clone()
                .expect("Item tree must only contain named blocks"),
            id,
        );
    }

    fn next_scope(&self) -> ScopeId {
        ScopeId {
            root_file: self.root_file,
            local_scope: self.map.scopes.next_key(),
            src: self.map.src,
        }
    }

    fn new_scope(&mut self, origin: ScopeOrigin, parent: LocalScopeId) -> LocalScopeId {
        self.map.scopes.push_and_get_key(Scope {
            origin,
            parent: Some(parent),
            children: IndexMap::default(),
            declarations: IndexMap::default(),
        })
    }

    fn new_root_scope(&mut self, origin: ScopeOrigin) -> LocalScopeId {
        self.map.scopes.push_and_get_key(Scope {
            origin,
            parent: None,
            children: IndexMap::default(),
            declarations: IndexMap::default(),
        })
    }

    fn insert_scope(
        &mut self,
        parent: LocalScopeId,
        scope: LocalScopeId,
        name: Name,
        id: impl Into<ScopeDefItem>,
    ) {
        self.insert_decl(parent, name.clone(), id);
        self.map.scopes[parent].children.entry(name).or_insert(scope);
    }

    fn insert_item_decl<N>(&mut self, dst: LocalScopeId, name: Name, item_tree: ItemTreeId<N>)
    where
        N: ItemTreeNode,
        ItemLoc<N>: Intern,
        <ItemLoc<N> as Intern>::ID: Into<ScopeDefItem>,
    {
        let decl = ItemLoc {
            scope: ScopeId { root_file: self.root_file, local_scope: dst, src: self.map.src },
            id: item_tree,
        }
        .intern(self.db);
        self.insert_decl(dst, name, decl)
    }

    fn insert_decl(&mut self, dst: LocalScopeId, name: Name, decl: impl Into<ScopeDefItem>) {
        let decl = decl.into();
        if let Some(old_decl) = self.map.scopes[dst].declarations.insert(name.clone(), decl) {
            self.map.diagnostics.push(DefDiagnostic::AlreadyDeclared {
                new: decl,
                old: old_decl,
                name,
            })
        }
    }
}
