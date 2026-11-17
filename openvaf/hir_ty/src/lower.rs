use std::sync::Arc;

use hir_def::nameres::diagnostics::PathResolveError;
use hir_def::nameres::DefMap;
pub use hir_def::DisciplineSlot;
use hir_def::{
    BranchId, DisciplineId, Domain, Intern, Lookup, NatureAttrId, NatureAttrLoc, NatureId,
    NatureRef, NatureRefKind, NodeId,
};
use syntax::name::{kw, Name};

use crate::db::HirTyDB;

/// Kind of an access function call (potential or flow access)
pub type DisciplineAccess = DisciplineSlot;

/// A nature: either a declared nature or the hidden nature `d.potential` / `d.flow` of a
/// discipline slot. A hidden nature has the slot's bound nature as its parent and holds the
/// discipline's overrides for that slot.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum NatureKey {
    Decl(NatureId),
    Slot(DisciplineId, DisciplineSlot),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NatureTy {
    pub parent: Option<NatureKey>,
    /// The base nature (end of the parent chain), `None` if a hidden nature's bound nature
    /// can't be resolved
    pub base_nature: Option<NatureId>,
    /// Units of the base nature (derived natures can't override units)
    pub units: Option<String>,
    /// Access function of the base nature (derived natures can't override access)
    pub access: Option<Name>,
    /// Effective (inherited) ddt_nature
    pub ddt_nature: NatureKey,
    /// Effective (inherited) idt_nature
    pub idt_nature: NatureKey,
}

impl NatureTy {
    pub fn nature_info_query(db: &dyn HirTyDB, nature: NatureKey) -> Arc<NatureTy> {
        NatureTy::obtain(db, nature, true)
    }

    pub fn obtain(db: &dyn HirTyDB, nature: NatureKey, resolve_parent: bool) -> Arc<NatureTy> {
        let parent = parent_of(db, nature);
        let parent_info = parent.filter(|_| resolve_parent).map(|parent| db.nature_info(parent));

        let base_nature = match (&parent_info, nature, parent) {
            (Some(parent_info), _, _) => parent_info.base_nature,
            (None, NatureKey::Decl(nature), _) => Some(nature),
            // cycle recovery: the bound nature of a slot is its parent
            (None, NatureKey::Slot(..), Some(NatureKey::Decl(parent))) => Some(parent),
            // bound nature can't be resolved (reported elsewhere)
            (None, NatureKey::Slot(..), _) => None,
        };
        let base_data = base_nature.map(|base| db.nature_data(base));

        let (own_ddt, own_idt) = own_ddt_idt(db, nature);
        let inherit = |own: Option<NatureKey>, parent_val: fn(&NatureTy) -> NatureKey| {
            own.or_else(|| {
                let parent_info = parent_info.as_ref()?;
                let parent_val = parent_val(parent_info);
                // a parent that refers to itself: the derived nature refers to itself
                if Some(parent_val) == parent {
                    Some(nature)
                } else {
                    Some(parent_val)
                }
            })
            .unwrap_or(nature)
        };
        let ddt_nature = inherit(own_ddt, |info| info.ddt_nature);
        let idt_nature = inherit(own_idt, |info| info.idt_nature);

        Arc::new(NatureTy {
            parent,
            base_nature,
            units: base_data.as_ref().and_then(|data| data.units.clone()),
            access: base_data.as_ref().and_then(|data| data.access.clone()),
            ddt_nature,
            idt_nature,
        })
    }

    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub(crate) fn nature_info_recover(
        db: &dyn HirTyDB,
        _cycle: &salsa::Cycle,
        nature: &NatureKey,
    ) -> Arc<NatureTy> {
        NatureTy::obtain(db, *nature, false)
    }

    /// Natures are compatible if they have the same units
    pub fn compatible(db: &dyn HirTyDB, nature1: NatureId, nature2: NatureId) -> bool {
        nature1 == nature2
            || db.nature_info(NatureKey::Decl(nature1)).units
                == db.nature_info(NatureKey::Decl(nature2)).units
    }

    /// Natures are related if they share the same base nature
    pub fn related(db: &dyn HirTyDB, nature1: NatureKey, nature2: NatureKey) -> bool {
        let base1 = db.nature_info(nature1).base_nature;
        base1.is_some() && base1 == db.nature_info(nature2).base_nature
    }

    pub fn lookup_attr(
        db: &dyn HirTyDB,
        nature: NatureId,
        name: &Name,
    ) -> Result<NatureAttrId, PathResolveError> {
        fn lookup_attr_inner(
            db: &dyn HirTyDB,
            nature: NatureId,
            name: &Name,
        ) -> Option<NatureAttrId> {
            let mut key = NatureKey::Decl(nature);
            // bounded walk, parent chains may contain cycles (reported elsewhere)
            for _ in 0..64 {
                if let NatureKey::Decl(nature) = key {
                    if let Some((attr, _)) = db
                        .nature_data(nature)
                        .attrs
                        .iter_enumerated()
                        .find(|(_, attr)| &attr.name == name)
                    {
                        return Some(NatureAttrLoc { nature, id: attr }.intern(db.upcast()));
                    }
                }
                key = parent_of(db, key)?;
            }
            None
        }
        lookup_attr_inner(db, nature, name).ok_or_else(|| PathResolveError::NotFoundIn {
            name: name.clone(),
            scope: db.nature_data(nature).name.clone(),
        })
    }
}

/// The parent of a nature (one hop, does not use `nature_info` so it can be used to detect
/// cycles).
pub fn parent_of(db: &dyn HirTyDB, nature: NatureKey) -> Option<NatureKey> {
    match nature {
        NatureKey::Decl(nature) => {
            let data = db.nature_data(nature);
            let def_map = db.def_map(nature.lookup(db.upcast()).root_file);
            lookup_nature(&def_map, data.parent.as_ref()?, db).ok()
        }
        NatureKey::Slot(discipline, slot) => {
            db.discipline_info(discipline).slot(slot).map(NatureKey::Decl)
        }
    }
}

/// The ddt_nature / idt_nature given by a nature itself (not inherited)
fn own_ddt_idt(db: &dyn HirTyDB, nature: NatureKey) -> (Option<NatureKey>, Option<NatureKey>) {
    let (root_file, ddt, idt) = match nature {
        NatureKey::Decl(nature) => {
            let data = db.nature_data(nature);
            (nature.lookup(db.upcast()).root_file, data.ddt_nature.clone(), data.idt_nature.clone())
        }
        NatureKey::Slot(discipline, slot) => {
            let data = db.discipline_data(discipline);
            let overrides = data.overrides(slot);
            (
                discipline.lookup(db.upcast()).root_file,
                overrides.ddt_nature.clone(),
                overrides.idt_nature.clone(),
            )
        }
    };
    let def_map = db.def_map(root_file);
    let lookup = |nature: Option<NatureRef>| lookup_nature(&def_map, nature.as_ref()?, db).ok();
    (lookup(ddt), lookup(idt))
}

/// Resolves a nature reference: a nature identifier or `discipline.potential` /
/// `discipline.flow` (the hidden nature of that slot; the slot must have a nature bound).
pub fn lookup_nature(
    def_map: &DefMap,
    nature_ref: &NatureRef,
    db: &dyn HirTyDB,
) -> Result<NatureKey, PathResolveError> {
    let slot = match nature_ref.kind {
        NatureRefKind::Nature => {
            return def_map
                .resolve_local_item_in_scope(def_map.root(), &nature_ref.name)
                .map(NatureKey::Decl)
        }
        NatureRefKind::DisciplinePotential => DisciplineSlot::Potential,
        NatureRefKind::DisciplineFlow => DisciplineSlot::Flow,
    };
    let discipline: DisciplineId =
        def_map.resolve_local_item_in_scope(def_map.root(), &nature_ref.name)?;
    if db.discipline_info(discipline).slot(slot).is_some() {
        Ok(NatureKey::Slot(discipline, slot))
    } else {
        Err(PathResolveError::NotFoundIn {
            name: if slot == DisciplineSlot::Potential { kw::potential } else { kw::flow },
            scope: nature_ref.name.clone(),
        })
    }
}

/// Resolves a reference that must name a declared nature (discipline bindings)
pub fn lookup_decl_nature(
    def_map: &DefMap,
    nature_ref: &NatureRef,
    db: &dyn HirTyDB,
) -> Option<NatureId> {
    match lookup_nature(def_map, nature_ref, db).ok()? {
        NatureKey::Decl(nature) => Some(nature),
        NatureKey::Slot(..) => None,
    }
}

/// Effective domain of a discipline
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum DisciplineDomain {
    Continuous,
    Discrete,
    /// no domain and no natures: compatible with either domain
    Empty,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DisciplineTy {
    /// bound flow nature (the declared nature, not the hidden nature)
    pub flow: Option<NatureId>,
    /// bound potential nature (the declared nature, not the hidden nature)
    pub potential: Option<NatureId>,
    pub domain: DisciplineDomain,
}

impl DisciplineTy {
    pub fn discipline_info_query(db: &dyn HirTyDB, discipline: DisciplineId) -> Arc<DisciplineTy> {
        let data = db.discipline_data(discipline);
        let def_map = db.def_map(discipline.lookup(db.upcast()).root_file);
        let domain = match data.domain {
            Some(Domain::Continuous) => DisciplineDomain::Continuous,
            Some(Domain::Discrete) => DisciplineDomain::Discrete,
            None if data.potential.is_some() || data.flow.is_some() => DisciplineDomain::Continuous,
            None => DisciplineDomain::Empty,
        };
        Arc::new(DisciplineTy {
            flow: data.flow.as_ref().and_then(|flow| lookup_decl_nature(&def_map, flow, db)),
            potential: data
                .potential
                .as_ref()
                .and_then(|potential| lookup_decl_nature(&def_map, potential, db)),
            domain,
        })
    }

    pub fn slot(&self, slot: DisciplineSlot) -> Option<NatureId> {
        match slot {
            DisciplineSlot::Potential => self.potential,
            DisciplineSlot::Flow => self.flow,
        }
    }

    pub fn is_natureless(&self) -> bool {
        self.potential.is_none() && self.flow.is_none()
    }

    /// The slot whose bound nature has the access function declared by `access_nature`
    /// (access functions are unique per base nature).
    pub fn access(&self, access_nature: NatureId, db: &dyn HirTyDB) -> Option<DisciplineAccess> {
        [DisciplineSlot::Potential, DisciplineSlot::Flow].into_iter().find(|&slot| {
            self.slot(slot).map_or(false, |nature| {
                NatureTy::related(db, NatureKey::Decl(nature), NatureKey::Decl(access_nature))
            })
        })
    }

    pub fn compatible(
        db: &dyn HirTyDB,
        discipline1: DisciplineId,
        discipline2: DisciplineId,
    ) -> bool {
        if discipline1 == discipline2 {
            return true;
        }
        let info1 = db.discipline_info(discipline1);
        let info2 = db.discipline_info(discipline2);
        match (info1.domain, info2.domain) {
            (DisciplineDomain::Empty, _) | (_, DisciplineDomain::Empty) => (),
            (domain1, domain2) if domain1 != domain2 => return false,
            _ => (),
        }
        [DisciplineSlot::Potential, DisciplineSlot::Flow].into_iter().all(|slot| {
            match (info1.slot(slot), info2.slot(slot)) {
                (Some(nature1), Some(nature2)) => NatureTy::compatible(db, nature1, nature2),
                _ => true,
            }
        })
    }
}

/// Disciplines of the nets of a branch that take part in access function checks: nets without
/// a discipline or with a natureless discipline are skipped (only for branches with two nets).
fn access_disciplines(db: &dyn HirTyDB, nets: &[NodeId]) -> Vec<Option<Arc<DisciplineTy>>> {
    let disciplines = nets
        .iter()
        .map(|&net| db.node_discipline(net).map(|discipline| db.discipline_info(discipline)));
    if nets.len() == 1 {
        disciplines.collect()
    } else {
        disciplines.filter(|it| it.as_ref().map_or(false, |it| !it.is_natureless())).collect()
    }
}

/// Resolves the access function declared by `access_nature` on a branch between `nets`.
/// Every (non skipped) net must resolve it to the same slot and at least one net must
/// resolve it.
pub fn nets_access(
    db: &dyn HirTyDB,
    nets: &[NodeId],
    access_nature: NatureId,
) -> Option<DisciplineAccess> {
    let mut res = None;
    for discipline in access_disciplines(db, nets) {
        let slot = discipline?.access(access_nature, db)?;
        if res.map_or(false, |res| res != slot) {
            return None;
        }
        res = Some(slot);
    }
    res
}

/// Checks `potential(...)` / `flow(...)` on a branch between `nets`: every (non skipped) net has
/// a nature in that slot and there is at least one such net.
pub fn nets_slot_ok(db: &dyn HirTyDB, nets: &[NodeId], slot: DisciplineSlot) -> bool {
    let disciplines = access_disciplines(db, nets);
    !disciplines.is_empty()
        && disciplines.iter().all(|it| it.as_ref().map_or(false, |it| it.slot(slot).is_some()))
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BranchKind {
    PortFlow(NodeId),
    NodeGnd(NodeId),
    Nodes(NodeId, NodeId),
}

impl BranchKind {
    pub fn nets(&self) -> Vec<NodeId> {
        match *self {
            BranchKind::PortFlow(node) | BranchKind::NodeGnd(node) => vec![node],
            BranchKind::Nodes(node1, node2) => vec![node1, node2],
        }
    }

    /// The discipline of a branch (used for the natures of the branch's unknowns): the
    /// disciplines of the nodes must be compatible, a discipline with natures is preferred.
    pub fn discipline(&self, db: &dyn HirTyDB) -> Option<DisciplineId> {
        match *self {
            BranchKind::PortFlow(node) | BranchKind::NodeGnd(node) => db.node_discipline(node),
            BranchKind::Nodes(node1, node2) => {
                let discipline1 = db.node_discipline(node1);
                let discipline2 = db.node_discipline(node2);
                // fast path
                if discipline1 == discipline2 {
                    return discipline1;
                }

                let (discipline1, discipline2) = match (discipline1, discipline2) {
                    (None, res) | (res, None) => return res,
                    (Some(d1), Some(d2)) => (d1, d2),
                };

                if !DisciplineTy::compatible(db, discipline1, discipline2) {
                    None
                } else if db.discipline_info(discipline1).is_natureless() {
                    Some(discipline2)
                } else {
                    Some(discipline1)
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BranchTy {
    pub discipline: DisciplineId,
    pub kind: BranchKind,
}
impl BranchTy {
    pub fn branch_info_query(db: &dyn HirTyDB, branch: BranchId) -> Option<Arc<BranchTy>> {
        let kind = &db.branch_data(branch).kind;
        let scope = branch.lookup(db.upcast()).scope;
        let kind = match kind {
            hir_def::BranchKind::PortFlow(port) => {
                BranchKind::PortFlow(scope.resolve_item_path(db.upcast(), port).ok()?)
            }
            hir_def::BranchKind::NodeGnd(node) => {
                BranchKind::NodeGnd(scope.resolve_item_path(db.upcast(), node).ok()?)
            }
            hir_def::BranchKind::Nodes(node1, node2) => {
                let node1 = scope.resolve_item_path(db.upcast(), node1).ok()?;
                let node2 = scope.resolve_item_path(db.upcast(), node2).ok()?;
                BranchKind::Nodes(node1, node2)
            }
            hir_def::BranchKind::Missing => return None,
        };

        Some(Arc::new(BranchTy { discipline: kind.discipline(db)?, kind }))
    }

    pub fn access(&self, nature: NatureId, db: &dyn HirTyDB) -> Option<DisciplineAccess> {
        nets_access(db, &self.kind.nets(), nature)
    }

    pub fn flow_attr(
        db: &dyn HirTyDB,
        branch: BranchId,
        name: &Name,
    ) -> Option<Result<NatureAttrId, PathResolveError>> {
        let discipline = db.branch_info(branch)?.discipline;
        match db.discipline_info(discipline).flow {
            Some(nature) => Some(NatureTy::lookup_attr(db, nature, name)),
            None => Some(Err(PathResolveError::NotFoundIn {
                name: kw::flow,
                scope: db.discipline_data(discipline).name.clone(),
            })),
        }
    }

    pub fn potential_attr(
        db: &dyn HirTyDB,
        branch: BranchId,
        name: &Name,
    ) -> Option<Result<NatureAttrId, PathResolveError>> {
        let discipline = db.branch_info(branch)?.discipline;
        match db.discipline_info(discipline).potential {
            Some(nature) => Some(NatureTy::lookup_attr(db, nature, name)),
            None => Some(Err(PathResolveError::NotFoundIn {
                name: kw::potential,
                scope: db.discipline_data(discipline).name.clone(),
            })),
        }
    }
}
