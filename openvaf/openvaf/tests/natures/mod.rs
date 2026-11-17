//! Natures, disciplines and attributes tables (`OSDI_NATURES`, `OSDI_DISCIPLINES`,
//! `OSDI_ATTRIBUTES`) and the natures of unknowns and residuals

use camino::Utf8PathBuf;
use mini_harness::Result;

use crate::compile_and_load;
use crate::load::{
    load_nda_tables, osdi_str, NdaTables, OsdiAttribute, OsdiNature, ATTR_TYPE_INT, ATTR_TYPE_REAL,
    ATTR_TYPE_STR, DOMAIN_CONTINUOUS, DOMAIN_NOT_GIVEN,
};

const SRC: &str = r#"
nature Volt
    units = "V";
    access = V;
    abstol = 1e-6;
endnature

nature Amp
    units = "A";
    access = I;
    abstol = 1e-12;
    idt_nature = Charge;
endnature

nature Charge
    units = "C";
    access = Q;
    abstol = 1e-14;
    ddt_nature = Amp;
endnature

// parent is the hidden nature elec.flow
nature AmpD : elec.flow
    abstol = 1e-9;
endnature

nature ChargeD : Charge
endnature

discipline elec
    potential Volt;
    flow Amp;
    flow.abstol = 1e-10;
    flow.idt_nature = ChargeD;
    user_attr = 5;
enddiscipline

discipline potonly
    domain continuous;
    potential Volt;
    potential.abstol = 1e-3;
enddiscipline

discipline empty
enddiscipline

module natures(a, b, c);
    inout a, b, c;
    elec a, b;
    potonly c;
    analog I(a, b) <+ V(a, b) / 1k;
endmodule
"#;

const NONE: u32 = u32::MAX;

fn nature_names(tables: &NdaTables) -> Vec<&'static str> {
    // SAFETY: names are valid C strings of the loaded library
    tables.natures.iter().map(|nature| unsafe { osdi_str(nature.name) }).collect()
}

fn attrs(tables: &NdaTables, start: u32, len: u32) -> &'static [OsdiAttribute] {
    &tables.attributes[start as usize..(start + len) as usize]
}

fn nature_attrs(tables: &NdaTables, nature: &OsdiNature) -> &'static [OsdiAttribute] {
    attrs(tables, nature.attr_start, nature.num_attr)
}

/// `name = value` of an attribute (as written)
fn attr_str(attr: &OsdiAttribute) -> String {
    // SAFETY: the value matches value_type, strings are valid C strings
    unsafe {
        let value = match attr.value_type {
            ATTR_TYPE_STR => osdi_str(attr.value.string).to_owned(),
            ATTR_TYPE_INT => attr.value.integer.to_string(),
            ATTR_TYPE_REAL => format!("{:e}", attr.value.real),
            ty => panic!("unknown attribute type {ty}"),
        };
        format!("{} = {value}", osdi_str(attr.name))
    }
}

fn attr_strs(attrs: &[OsdiAttribute]) -> Vec<String> {
    attrs.iter().map(attr_str).collect()
}

/// (parent, ddt, idt)
fn refs(nature: &OsdiNature) -> (u32, u32, u32) {
    (nature.parent, nature.ddt, nature.idt)
}

pub fn tables_test() -> Result<()> {
    let root_file: Utf8PathBuf =
        Utf8PathBuf::try_from(std::env::temp_dir())?.join("openvaf_natures_test.va");
    std::fs::write(&root_file, SRC)?;
    let desc = compile_and_load(&root_file);
    // SAFETY: compiled by OpenVAF above
    let tables = unsafe { load_nda_tables(&root_file.with_extension("osdi"))? };

    // real natures in order of appearance, then the hidden natures in discipline order
    assert_eq!(
        nature_names(&tables),
        [
            "Volt",
            "Amp",
            "Charge",
            "AmpD",
            "ChargeD",
            "elec.potential",
            "elec.flow",
            "potonly.potential"
        ]
    );
    let n = tables.natures;

    // resolved indices, only given values
    assert_eq!(refs(&n[0]), (NONE, NONE, NONE));
    assert_eq!(refs(&n[1]), (NONE, NONE, 2));
    assert_eq!(refs(&n[2]), (NONE, 1, NONE));
    assert_eq!(refs(&n[3]), (6, NONE, NONE));
    assert_eq!(refs(&n[4]), (2, NONE, NONE));
    assert_eq!(refs(&n[5]), (0, NONE, NONE));
    assert_eq!(refs(&n[6]), (1, NONE, 4));
    assert_eq!(refs(&n[7]), (0, NONE, NONE));

    // attributes: only given ones, names as written
    assert_eq!(
        attr_strs(nature_attrs(&tables, &n[0])),
        ["units = V", "access = V", "abstol = 1e-6"]
    );
    assert_eq!(
        attr_strs(nature_attrs(&tables, &n[1])),
        ["units = A", "access = I", "abstol = 1e-12", "idt_nature = Charge"]
    );
    assert_eq!(attr_strs(nature_attrs(&tables, &n[3])), ["abstol = 1e-9"]);
    assert!(nature_attrs(&tables, &n[4]).is_empty());
    assert!(nature_attrs(&tables, &n[5]).is_empty());
    assert_eq!(attr_strs(nature_attrs(&tables, &n[6])), ["abstol = 1e-10", "idt_nature = ChargeD"]);
    assert_eq!(attr_strs(nature_attrs(&tables, &n[7])), ["abstol = 1e-3"]);

    // disciplines in order of appearance, bound natures are the hidden natures
    let d = tables.disciplines;
    assert_eq!(d.len(), 3);
    // SAFETY: names are valid C strings of the loaded library
    let names: Vec<_> = d.iter().map(|it| unsafe { osdi_str(it.name) }).collect();
    assert_eq!(names, ["elec", "potonly", "empty"]);
    assert_eq!((d[0].potential, d[0].flow, d[0].domain), (5, 6, DOMAIN_NOT_GIVEN));
    assert_eq!((d[1].potential, d[1].flow, d[1].domain), (7, NONE, DOMAIN_CONTINUOUS));
    assert_eq!((d[2].potential, d[2].flow, d[2].domain), (NONE, NONE, DOMAIN_NOT_GIVEN));

    // override sections (kept for compatibility) and user attributes
    let elec = &d[0];
    let flow_attrs = attrs(&tables, elec.attr_start, elec.num_flow_attr);
    assert_eq!(attr_strs(flow_attrs), ["abstol = 1e-10", "idt_nature = ChargeD"]);
    assert_eq!(elec.num_potential_attr, 0);
    let user_start = elec.attr_start + elec.num_flow_attr + elec.num_potential_attr;
    assert_eq!(
        attr_strs(attrs(&tables, user_start, elec.num_user_attr)),
        ["potential = Volt", "flow = Amp", "user_attr = 5"]
    );
    let potonly = &d[1];
    let user_start = potonly.attr_start + potonly.num_flow_attr + potonly.num_potential_attr;
    assert_eq!(
        attr_strs(attrs(&tables, user_start, potonly.num_user_attr)),
        ["domain = continuous", "potential = Volt"]
    );

    // natures of unknowns and residuals refer to the hidden natures
    let nodes = desc.nodes();
    for (i, node) in nodes.iter().enumerate() {
        // SAFETY: valid pointers of the loaded descriptor
        let (name, unknown, residual) = unsafe {
            (osdi_str(node.name), *desc.unknown_nature.add(i), *desc.residual_nature.add(i))
        };
        match name {
            "a" | "b" => {
                assert_eq!(unknown, 5, "unknown nature of {name}");
                assert_eq!(residual, 6, "residual nature of {name}");
            }
            "c" => assert_eq!(unknown, 7, "unknown nature of {name}"),
            _ => (),
        }
    }
    Ok(())
}
