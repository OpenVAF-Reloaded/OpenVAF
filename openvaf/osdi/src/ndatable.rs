use crate::metadata::osdi_0_5::{
    OsdiAttribute, OsdiAttributeValue, OsdiDiscipline, OsdiNature, ATTR_TYPE_INT, ATTR_TYPE_REAL,
    ATTR_TYPE_STR, DOMAIN_CONTINUOUS, DOMAIN_DISCRETE, DOMAIN_NOT_GIVEN,
};
use hir::CompilationDB;
use hir_def::db::HirDefDB;
use hir_def::item_tree::{
    Discipline, DisciplineAttr, DisciplineAttrKind, DisciplineSlot, Domain, ItemTreeData,
    NatureAttr, NatureRef, NatureRefKind,
};
use hir_def::ndatable::NDATable;
use lasso::Rodeo;
use std::vec::Vec;
use syntax::ConstExprValue;

impl OsdiAttributeValue {
    pub fn new(v: &ConstExprValue, literals: &mut Rodeo) -> OsdiAttributeValue {
        match v {
            ConstExprValue::Float(f) => OsdiAttributeValue::Real(f.into_inner()),
            ConstExprValue::Int(i) => OsdiAttributeValue::Integer(*i),
            ConstExprValue::String(s) => {
                literals.get_or_intern(s.clone());
                OsdiAttributeValue::String(s.clone())
            }
        }
    }
}

trait IsAttribute {
    fn get_name(&self) -> &str;
    fn get_value(&self) -> Option<&ConstExprValue>;
}

impl IsAttribute for NatureAttr {
    fn get_name(&self) -> &str {
        self.name.as_ref()
    }

    fn get_value(&self) -> Option<&ConstExprValue> {
        self.value.as_ref()
    }
}

impl IsAttribute for DisciplineAttr {
    fn get_name(&self) -> &str {
        self.name.as_ref()
    }

    fn get_value(&self) -> Option<&ConstExprValue> {
        self.value.as_ref()
    }
}

impl OsdiAttribute {
    fn new<T: IsAttribute>(attr: &T, literals: &mut Rodeo) -> Option<OsdiAttribute> {
        if let Some(v) = attr.get_value() {
            literals.get_or_intern(attr.get_name());
            Some(OsdiAttribute {
                name: attr.get_name().to_string(),
                value_type: match v {
                    ConstExprValue::Float(_) => ATTR_TYPE_REAL,
                    ConstExprValue::Int(_) => ATTR_TYPE_INT,
                    ConstExprValue::String(_) => ATTR_TYPE_STR,
                },
                value: OsdiAttributeValue::new(v, literals),
            })
        } else {
            None
        }
    }
}

/// Natures table index of a nature reference (`d.potential` / `d.flow` resolve to the hidden
/// nature), `u32::MAX` if not given. Unresolved references are compile errors and can't reach
/// this point.
fn nature_index(nature_ref: Option<&NatureRef>, nda_table: &NDATable) -> u32 {
    let Some(natref) = nature_ref else { return u32::MAX };
    let name = natref.name.to_string();
    let idx = match natref.kind {
        NatureRefKind::Nature => nda_table.nature_name_map.get(&name).map(|idx| idx.into_raw()),
        NatureRefKind::DisciplinePotential => {
            nda_table.hidden_nature_by_name(&name, DisciplineSlot::Potential)
        }
        NatureRefKind::DisciplineFlow => {
            nda_table.hidden_nature_by_name(&name, DisciplineSlot::Flow)
        }
    };
    idx.unwrap_or(u32::MAX)
}

/// Nature reference given by a discipline's `ddt_nature` / `idt_nature` override of a slot
fn discipline_override<'a>(
    discipline: &Discipline,
    it_data: &'a ItemTreeData,
    kind: DisciplineAttrKind,
    name: &str,
) -> Option<&'a NatureRef> {
    discipline.extra_attrs.clone().find_map(|idx| {
        let attr = &it_data.discipline_attrs[idx];
        (attr.kind == kind && &*attr.name == name).then_some(attr.nature.as_ref()).flatten()
    })
}

// Collect disciplie attributes
fn collect_discipline_attrs(
    discipline: &Discipline,
    it_data: &ItemTreeData,
    kind: DisciplineAttrKind,
    attrs: &mut Vec<OsdiAttribute>,
    literals: &mut Rodeo,
) -> (u32, u32) {
    let i1 = attrs.len();
    for idx in discipline.extra_attrs.clone() {
        let attr = &it_data.discipline_attrs[idx];
        if attr.kind != kind {
            continue;
        }
        literals.get_or_intern(attr.name.to_string());
        if let Some(osdi_attr) = OsdiAttribute::new(attr, literals) {
            attrs.push(osdi_attr);
        }
    }
    let i2 = attrs.len();
    (i1 as u32, i2 as u32)
}

// Build natures, disciplines, and attributes array
pub fn nda_arrays(
    db: &CompilationDB,
    literals: &mut Rodeo,
) -> (Vec<OsdiNature>, Vec<OsdiDiscipline>, Vec<OsdiAttribute>) {
    // Retrieve NDATable and root items
    let cu = db.compilation_unit();
    let fileid = cu.root_file();
    let nda_table = db.nda_table(fileid);
    let item_tree = db.item_tree(fileid);

    let mut attr_vec: Vec<OsdiAttribute> = Vec::new();
    let mut nature_vec: Vec<OsdiNature> = Vec::new();
    let mut discipline_vec: Vec<OsdiDiscipline> = Vec::new();

    // Go through natures
    for nature in &item_tree.data.natures {
        // Collect attributes
        let i1 = attr_vec.len();
        for idx in nature.attrs.clone() {
            let attr = &item_tree.data.nature_attrs[idx];
            if let Some(osdi_attr) = OsdiAttribute::new(attr, literals) {
                attr_vec.push(osdi_attr);
            }
        }
        let i2 = attr_vec.len();
        let parent = nature_index(nature.parent.as_ref(), &nda_table);

        // Intern strings
        literals.get_or_intern(nature.name.to_string());
        // Add to vector
        nature_vec.push(OsdiNature {
            name: nature.name.to_string(),
            parent,
            ddt: nature_index(nature.ddt_nature.as_ref().map(|(x, _)| x), &nda_table),
            idt: nature_index(nature.idt_nature.as_ref().map(|(x, _)| x), &nda_table),
            attr_start: i1 as u32,
            num_attr: (i2 - i1) as u32,
        });
    }

    // Hidden natures d.potential / d.flow: the bound nature is the parent, the discipline's
    // overrides of that slot are the attributes
    for &(discipline, slot) in &nda_table.hidden_natures {
        let discipline = &item_tree[discipline];
        let (kind, bound) = match slot {
            DisciplineSlot::Potential => {
                (DisciplineAttrKind::PotentialOverwrite, &discipline.potential)
            }
            DisciplineSlot::Flow => (DisciplineAttrKind::FlowOverwrite, &discipline.flow),
        };
        let (i1, i2) =
            collect_discipline_attrs(discipline, &item_tree.data, kind, &mut attr_vec, literals);
        let parent = nature_index(bound.as_ref().map(|(x, _)| x), &nda_table);
        let ddt = discipline_override(discipline, &item_tree.data, kind, "ddt_nature");
        let idt = discipline_override(discipline, &item_tree.data, kind, "idt_nature");

        let name = format!("{}.{}", discipline.name, slot.name());
        literals.get_or_intern(&name);
        nature_vec.push(OsdiNature {
            name,
            parent,
            ddt: nature_index(ddt, &nda_table),
            idt: nature_index(idt, &nda_table),
            attr_start: i1,
            num_attr: i2 - i1,
        });
    }

    // Go through disciplines
    for (discipline_idx, discipline) in item_tree.data.disciplines.iter_enumerated() {
        // Collect flow and potential overrides
        let (fi1, fi2) = collect_discipline_attrs(
            discipline,
            &item_tree.data,
            DisciplineAttrKind::FlowOverwrite,
            &mut attr_vec,
            literals,
        );
        let (pi1, pi2) = collect_discipline_attrs(
            discipline,
            &item_tree.data,
            DisciplineAttrKind::PotentialOverwrite,
            &mut attr_vec,
            literals,
        );
        // Collect user attributes
        let (i1, i2) = collect_discipline_attrs(
            discipline,
            &item_tree.data,
            DisciplineAttrKind::UserDefined,
            &mut attr_vec,
            literals,
        );
        // Flow and potential nature: the hidden natures
        let hidden = |slot| nda_table.hidden_nature(discipline_idx, slot).unwrap_or(u32::MAX);

        // Intern strings
        literals.get_or_intern(discipline.name.to_string());
        // Add to vector
        discipline_vec.push(OsdiDiscipline {
            name: discipline.name.to_string(),
            flow: hidden(DisciplineSlot::Flow),
            potential: hidden(DisciplineSlot::Potential),
            domain: if let Some((domain, _)) = discipline.domain {
                if domain == Domain::Discrete {
                    DOMAIN_DISCRETE
                } else {
                    DOMAIN_CONTINUOUS
                }
            } else {
                DOMAIN_NOT_GIVEN
            },
            attr_start: fi1,
            num_flow_attr: (fi2 - fi1) as u32,
            num_potential_attr: (pi2 - pi1) as u32,
            num_user_attr: (i2 - i1) as u32,
        });
    }
    (nature_vec, discipline_vec, attr_vec)
}
