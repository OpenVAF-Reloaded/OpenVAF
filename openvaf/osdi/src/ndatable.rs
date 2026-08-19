use crate::metadata::osdi_0_5::{
    OsdiAttribute, OsdiAttributeValue, OsdiDiscipline, OsdiNature, ATTR_TYPE_INT, ATTR_TYPE_REAL,
    ATTR_TYPE_STR, DOMAIN_CONTINUOUS, DOMAIN_DISCRETE, DOMAIN_NOT_GIVEN, NATREF_DISCIPLINE_FLOW,
    NATREF_DISCIPLINE_POTENTIAL, NATREF_NATURE, NATREF_NONE,
};
use hir::CompilationDB;
use hir_def::db::HirDefDB;
use hir_def::item_tree::{
    Discipline, DisciplineAttr, DisciplineAttrKind, Domain, ItemTreeData, NatureAttr, NatureRef,
    NatureRefKind,
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

fn resolve_nature_ref(nature_ref: Option<&NatureRef>, nda_table: &NDATable) -> (u32, u32) {
    if let Some(natref) = nature_ref {
        match natref.kind {
            NatureRefKind::Nature => (
                NATREF_NATURE,
                nda_table.nature_name_map.get(&natref.name.to_string()).unwrap().into_raw(),
            ),
            NatureRefKind::DisciplineFlow => (
                NATREF_DISCIPLINE_FLOW,
                nda_table.discipline_name_map.get(&natref.name.to_string()).unwrap().into_raw(),
            ),
            NatureRefKind::DisciplinePotential => (
                NATREF_DISCIPLINE_POTENTIAL,
                nda_table.discipline_name_map.get(&natref.name.to_string()).unwrap().into_raw(),
            ),
        }
    } else {
        (NATREF_NONE, u32::MAX)
    }
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
        let i2 = attr_vec.len() + 1;
        let (pt, pi) = resolve_nature_ref(nature.parent.as_ref(), &nda_table);
        // Parent type is always a nature for ddt and idt
        let (dt, dni) = resolve_nature_ref(nature.ddt_nature.as_ref().map(|(x, _)| x), &nda_table);
        if dt != NATREF_NATURE && dt != NATREF_NONE {
            panic!("Nature's ddt must be a nature reference.")
        }
        let (it, ini) = resolve_nature_ref(nature.idt_nature.as_ref().map(|(x, _)| x), &nda_table);
        if it != NATREF_NATURE && it != NATREF_NONE {
            panic!("Nature's idt must be a nature reference.")
        }

        // Intern strings
        literals.get_or_intern(nature.name.to_string());
        // Add to vector
        nature_vec.push(OsdiNature {
            name: nature.name.to_string(),
            parent_type: pt,
            parent: pi,
            ddt: dni,
            idt: ini,
            attr_start: i1 as u32,
            num_attr: (i2 - i1) as u32,
        });
    }

    // Go through disciplines
    for discipline in &item_tree.data.disciplines {
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
        // Flow and potential nature
        let (ft, fni) = resolve_nature_ref(discipline.flow.as_ref().map(|(x, _)| x), &nda_table);
        if ft != NATREF_NATURE && ft != NATREF_NONE {
            panic!("Discipline's flow must be a nature reference.")
        }
        let (pt, pni) =
            resolve_nature_ref(discipline.potential.as_ref().map(|(x, _)| x), &nda_table);
        if pt != NATREF_NATURE && pt != NATREF_NONE {
            panic!("Discipline's potential must be a nature reference.")
        }

        // Intern strings
        literals.get_or_intern(discipline.name.to_string());
        // Add to vector
        discipline_vec.push(OsdiDiscipline {
            name: discipline.name.to_string(),
            flow: fni,
            potential: pni,
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
