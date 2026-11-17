// Natues, disciplines, and attributes table

use arena::Idx;
use std::collections::HashMap;
use std::sync::Arc;

use super::{Discipline, DisciplineSlot, ItemTree, Nature};
use crate::db::HirDefDB;
use basedb::FileId;

/// Natures and disciplines as they appear in the OSDI tables.
///
/// The natures table holds the real natures in order of appearance followed by the hidden
/// natures `d.potential` / `d.flow` (one per bound discipline slot) in discipline order of
/// appearance, `d.potential` before `d.flow`. Disciplines are in order of appearance.
#[derive(PartialEq, Eq, Debug)]
pub struct NDATable {
    pub nature_name_map: HashMap<String, Idx<Nature>>,
    pub discipline_name_map: HashMap<String, Idx<Discipline>>,
    /// Number of real natures (index of the first hidden nature)
    pub num_real_natures: u32,
    /// Hidden natures in table order
    pub hidden_natures: Vec<(Idx<Discipline>, DisciplineSlot)>,
    /// Natures table index of a hidden nature
    pub hidden_nature_map: HashMap<(Idx<Discipline>, DisciplineSlot), u32>,
}

impl Default for NDATable {
    fn default() -> Self {
        Self::new()
    }
}

impl NDATable {
    pub fn new() -> Self {
        Self {
            nature_name_map: HashMap::new(),
            discipline_name_map: HashMap::new(),
            num_real_natures: 0,
            hidden_natures: Vec::new(),
            hidden_nature_map: HashMap::new(),
        }
    }
    pub fn nda_table_query(db: &dyn HirDefDB, file: FileId) -> Arc<NDATable> {
        let ctx = NDACtx::new(db, file);
        let mut table = NDATable::new();
        ctx.fill_table(&mut table);
        Arc::new(table)
    }

    /// Natures table index of the hidden nature of a discipline slot
    /// (`None` if the slot has no nature bound).
    pub fn hidden_nature(&self, discipline: Idx<Discipline>, slot: DisciplineSlot) -> Option<u32> {
        self.hidden_nature_map.get(&(discipline, slot)).copied()
    }

    /// Natures table index of a hidden nature given by discipline name
    pub fn hidden_nature_by_name(&self, discipline: &str, slot: DisciplineSlot) -> Option<u32> {
        self.hidden_nature(*self.discipline_name_map.get(discipline)?, slot)
    }
}

pub(super) struct NDACtx {
    tree: Arc<ItemTree>,
}

impl NDACtx {
    pub fn new(db: &dyn HirDefDB, file: FileId) -> Self {
        Self { tree: db.item_tree(file) }
    }

    // Fill it with natures and disciplines
    pub fn fill_table(&self, table: &mut NDATable) {
        // Add natures
        for (idx, nature) in self.tree.data.natures.iter_enumerated() {
            table.nature_name_map.insert(nature.name.to_string(), idx);
        }
        table.num_real_natures = self.tree.data.natures.len() as u32;

        // Add disciplines and their hidden natures
        for (idx, discipline) in self.tree.data.disciplines.iter_enumerated() {
            table.discipline_name_map.insert(discipline.name.to_string(), idx);
            let slots = [
                (DisciplineSlot::Potential, discipline.potential.is_some()),
                (DisciplineSlot::Flow, discipline.flow.is_some()),
            ];
            for (slot, bound) in slots {
                if bound {
                    let pos = table.num_real_natures + table.hidden_natures.len() as u32;
                    table.hidden_natures.push((idx, slot));
                    table.hidden_nature_map.insert((idx, slot), pos);
                }
            }
        }
    }
}
