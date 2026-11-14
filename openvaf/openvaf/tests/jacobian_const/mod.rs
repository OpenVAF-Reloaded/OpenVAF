//! Constness flags of Jacobian entries (`JACOBIAN_ENTRY_*_CONST` and
//! `JACOBIAN_ENTRY_*_OPTIME_CONST`)

use camino::Utf8PathBuf;
use mini_harness::Result;

use crate::compile_and_load;
use crate::load::{
    osdi_str, OsdiDescriptor, JACOBIAN_ENTRY_REACT, JACOBIAN_ENTRY_REACT_CONST,
    JACOBIAN_ENTRY_REACT_OPTIME_CONST, JACOBIAN_ENTRY_RESIST, JACOBIAN_ENTRY_RESIST_CONST,
    JACOBIAN_ENTRY_RESIST_OPTIME_CONST,
};

const SRC: &str = r#"`include "disciplines.vams"
module jacobian_const(a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, a7, b7, a8, b8, a9, b9);
    inout a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, a7, b7, a8, b8, a9, b9;
    electrical a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, a7, b7, a8, b8, a9, b9;
    parameter real r = 1.0;
    parameter real c = 1e-12;
    parameter integer n = 3;
    real g, h;
    integer i;

    analog begin
        // linear resistor and capacitor
        I(a1, b1) <+ V(a1, b1) / r + c * ddt(V(a1, b1));
        // diode
        I(a2, b2) <+ 1e-14 * (exp(V(a2, b2) / 0.025) - 1);
        // time dependent conductance
        I(a3, b3) <+ V(a3, b3) * (1 + $abstime);
        // simulator parameter dependent conductance
        I(a4, b4) <+ V(a4, b4) * $simparam("gmin", 1e-12) * 1e12;
        // analysis dependent conductance
        I(a5, b5) <+ (analysis("tran") ? 1.0 : 2.0) * V(a5, b5);
        // conductance selected by an operating point dependent branch
        if (V(a6, b6) > 0)
            g = 1.0;
        else
            g = 2.0;
        I(a6, b6) <+ g * V(a6, b6);
        // operating point dependence carried by a loop
        g = 1.0;
        for (i = 0; i < n; i = i + 1)
            if (V(a7, b7) > i)
                g = g + 1.0;
        I(a7, b7) <+ g * V(a7, b7);
        // loop that depends only on parameters
        h = 0.0;
        for (i = 0; i < n; i = i + 1)
            h = h + r;
        I(a8, b8) <+ h * V(a8, b8);
        // temperature dependent conductance
        I(a9, b9) <+ V(a9, b9) * $temperature / 300.0;
    end
endmodule
"#;

const RESIST_FLAGS: u32 = JACOBIAN_ENTRY_RESIST_CONST | JACOBIAN_ENTRY_RESIST_OPTIME_CONST;
const REACT_FLAGS: u32 = JACOBIAN_ENTRY_REACT_CONST | JACOBIAN_ENTRY_REACT_OPTIME_CONST;

/// Flags of the Jacobian entry (`row`, `col`)
fn flags(desc: &OsdiDescriptor, row: &str, col: &str) -> u32 {
    let nodes = desc.nodes();
    desc.matrix_entries()
        .iter()
        .find(|entry| {
            // SAFETY: node names are valid C strings of the loaded descriptor
            unsafe {
                osdi_str(nodes[entry.nodes.node_1 as usize].name) == row
                    && osdi_str(nodes[entry.nodes.node_2 as usize].name) == col
            }
        })
        .unwrap_or_else(|| panic!("no Jacobian entry ({row}, {col})"))
        .flags
}

/// Checks the constness flags of the diagonal entry of node `node`
fn check(desc: &OsdiDescriptor, node: &str, resist: u32, react: u32) {
    let flags = flags(desc, node, node);
    assert_eq!(flags & RESIST_FLAGS, resist, "resistive constness of ({node}, {node})");
    assert_eq!(flags & REACT_FLAGS, react, "reactive constness of ({node}, {node})");
}

pub fn flags_test() -> Result<()> {
    let root_file: Utf8PathBuf =
        Utf8PathBuf::try_from(std::env::temp_dir())?.join("openvaf_jacobian_const_test.va");
    std::fs::write(&root_file, SRC)?;
    let desc = compile_and_load(&root_file);

    // linear resistor and capacitor: both parts constant
    let a1 = flags(desc, "a1", "a1");
    assert_ne!(a1 & JACOBIAN_ENTRY_RESIST, 0);
    assert_ne!(a1 & JACOBIAN_ENTRY_REACT, 0);
    check(desc, "a1", RESIST_FLAGS, REACT_FLAGS);
    // absent reactive parts are constant
    check(desc, "a2", 0, REACT_FLAGS);
    check(desc, "a3", 0, REACT_FLAGS);
    // $simparam and analysis() do not affect OPTIME_CONST
    check(desc, "a4", JACOBIAN_ENTRY_RESIST_OPTIME_CONST, REACT_FLAGS);
    check(desc, "a5", JACOBIAN_ENTRY_RESIST_OPTIME_CONST, REACT_FLAGS);
    // operating point dependent control flow
    check(desc, "a6", 0, REACT_FLAGS);
    check(desc, "a7", 0, REACT_FLAGS);
    // parameter dependent loop is computed during instance setup
    check(desc, "a8", RESIST_FLAGS, REACT_FLAGS);
    // temperature is allowed
    check(desc, "a9", RESIST_FLAGS, REACT_FLAGS);
    Ok(())
}
