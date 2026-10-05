use hir::diagnostics::sink::Buffer;
use hir::diagnostics::ConsoleSink;
use hir::CompilationDB;
use indoc::indoc;

#[test]
fn invalid_attr() {
    let src = indoc! {r#"
        module test;
            (* units=1, desc=xx, group=foo*bar, type=2  *) parameter real foo=2.0, bar=3.0;
            (* type="foo"  *) parameter real test=1.0;
            (* units=1, desc=xx *) real init;
            aliasparam alias=foo;
        endmodule
    "#};
    let db = CompilationDB::new_virtual(src).unwrap();
    let mut buf = Buffer::no_color();
    {
        let mut sink = ConsoleSink::buffer(&db, &mut buf);
        sink.annonymize_paths();
        super::collect_modules(&db, false, &mut sink);
    }
    expect_test::expect![[r#"
        error: illegal expression supplied to 'units' attribute; expected a string literal
          --> /root.va:2:8
          |
        2 |     (* units=1, desc=xx, group=foo*bar, type=2  *) parameter real foo=2.0, bar=3.0;
          |        ^^^^^^^ expected a string literal

        error: illegal expression supplied to 'desc' attribute; expected a string literal
          --> /root.va:2:17
          |
        2 |     (* units=1, desc=xx, group=foo*bar, type=2  *) parameter real foo=2.0, bar=3.0;
          |                 ^^^^^^^ expected a string literal

        error: illegal expression supplied to 'group' attribute; expected a string literal
          --> /root.va:2:26
          |
        2 |     (* units=1, desc=xx, group=foo*bar, type=2  *) parameter real foo=2.0, bar=3.0;
          |                          ^^^^^^^^^^^^^ expected a string literal

        error: illegal expression supplied to 'type' attribute; expected a string literal
          --> /root.va:2:41
          |
        2 |     (* units=1, desc=xx, group=foo*bar, type=2  *) parameter real foo=2.0, bar=3.0;
          |                                         ^^^^^^ expected a string literal

        warning: unknown type "foo" expected "model" or "instance"
          --> /root.va:3:8
          |
        3 |     (* type="foo"  *) parameter real test=1.0;
          |        ^^^^^^^^^^ unknown type

        error: illegal expression supplied to 'units' attribute; expected a string literal
          --> /root.va:4:8
          |
        4 |     (* units=1, desc=xx *) real init;
          |        ^^^^^^^ expected a string literal

        error: illegal expression supplied to 'desc' attribute; expected a string literal
          --> /root.va:4:17
          |
        4 |     (* units=1, desc=xx *) real init;
          |                 ^^^^^^^ expected a string literal

        error: could not compile `root.va` due to 6 previous errors; 1 warning emitted

    "#]]
    .assert_eq(&String::from_utf8(buf.into_inner()).unwrap());
}

#[test]
fn parameters() {
    let src = indoc! {r#"
        module test;
            (* units="m", desc="hmm", group="foo", type="instance" *) parameter real foo=2.0, bar=3.0;
            aliasparam alias=foo;
            (* type="model" *) parameter real module_param=3.0;
        endmodule
    "#};
    let db = CompilationDB::new_virtual(src).unwrap();
    let modules = super::collect_modules(&db, false, &mut ConsoleSink::new(&db)).unwrap();
    assert_eq!(modules.len(), 1);
    let params: Vec<_> = modules[0].params.iter().map(|(k, v)| (k.name(&db), v)).collect();
    expect_test::expect![[r#"
        [
            (
                "foo",
                ParamInfo {
                    name: "foo",
                    alias: [
                        "alias",
                    ],
                    unit: "m",
                    description: "hmm",
                    group: "foo",
                    is_instance: true,
                },
            ),
            (
                "bar",
                ParamInfo {
                    name: "bar",
                    alias: [],
                    unit: "m",
                    description: "hmm",
                    group: "foo",
                    is_instance: true,
                },
            ),
            (
                "module_param",
                ParamInfo {
                    name: "module_param",
                    alias: [],
                    unit: "",
                    description: "",
                    group: "",
                    is_instance: false,
                },
            ),
        ]
    "#]]
    .assert_debug_eq(&params);
}

#[test]
fn opvars() {
    let src = indoc! {r#"
        module test;
            (* units="m", desc="hmm" *) real both1, both2=3.0;
            (* units="m" *) real units_;
            (* desc="hmm" *) real desc_;
        endmodule
    "#};
    let db = CompilationDB::new_virtual(src).unwrap();
    let modules = super::collect_modules(&db, false, &mut ConsoleSink::new(&db)).unwrap();
    assert_eq!(modules.len(), 1);
    let params: Vec<_> = modules[0].op_vars.iter().map(|(k, v)| (k.name(&db), v)).collect();
    expect_test::expect![[r#"
        [
            (
                "both1",
                OpVar {
                    unit: "m",
                    description: "hmm",
                },
            ),
            (
                "both2",
                OpVar {
                    unit: "m",
                    description: "hmm",
                },
            ),
            (
                "units_",
                OpVar {
                    unit: "m",
                    description: "",
                },
            ),
            (
                "desc_",
                OpVar {
                    unit: "",
                    description: "hmm",
                },
            ),
        ]
    "#]]
    .assert_debug_eq(&params);
}

#[test]
fn bus_port_order() {
    let src = indoc! {r#"
        `include "disciplines.vams"
        module nonansi(d, out, e);
            input [0:3] d;
            output out;
            inout [2:1] e;
            electrical [0:3] d;
            electrical out;
            electrical [2:1] e;
            analog V(out) <+ V(d[0]) + V(d[3]) + V(e[1], e[2]);
        endmodule
    "#};
    let db = CompilationDB::new_virtual(src).unwrap();
    let modules = super::collect_modules(&db, false, &mut ConsoleSink::new(&db)).unwrap();
    let ports: Vec<_> =
        modules[0].module.ports(&db).into_iter().map(|port| port.name(&db).to_string()).collect();
    expect_test::expect![[r#"
        [
            "d[0]",
            "d[1]",
            "d[2]",
            "d[3]",
            "out",
            "e[1]",
            "e[2]",
        ]
    "#]]
    .assert_debug_eq(&ports);
}

#[test]
fn bus_port_classification() {
    // Every bit of a bus port must be a port and every bit of an internal bus an internal
    // node, independent of the order of the direction and discipline declarations.
    let cases = [
        "module m(d, out); electrical [0:3] d; electrical out; input [0:3] d; output out;
            electrical x; analog begin V(out) <+ V(d[3]); I(x) <+ V(x); end endmodule",
        "(*openvaf_allow=\"port_without_direction\"*) module m(d, out); electrical [0:3] d;
            electrical out; electrical x; analog begin V(out) <+ V(d[3]); I(x) <+ V(x); end endmodule",
        "module m(d, out); electrical [1:0] x; electrical [0:3] d; electrical out; input [0:3] d;
            output out; analog begin V(out) <+ V(d[3]); I(x[0]) <+ V(x[1]); end endmodule",
        "module m(a, out, b); electrical [0:1] a; electrical [0:2] b; electrical out;
            inout [0:2] b; output out; input [0:1] a; electrical y;
            analog begin V(out) <+ V(a[1]) + V(b[2]); I(y) <+ V(y); end endmodule",
    ];
    let mut res = String::new();
    for body in cases {
        let src = format!("`include \"disciplines.vams\"\n{body}\n");
        let db = CompilationDB::new_virtual(&src).unwrap();
        let modules = super::collect_modules(&db, false, &mut ConsoleSink::new(&db)).unwrap();
        let module = modules[0].module;
        let names = |nodes: Vec<hir::Node>| {
            nodes.into_iter().map(|node| node.name(&db).to_string()).collect::<Vec<_>>().join(" ")
        };
        res += &format!(
            "ports: {}; internal: {}\n",
            names(module.ports(&db)),
            names(module.internal_nodes(&db))
        );
    }
    expect_test::expect![[r#"
        ports: d[0] d[1] d[2] d[3] out; internal: x
        ports: d[0] d[1] d[2] d[3] out; internal: x
        ports: d[0] d[1] d[2] d[3] out; internal: x[0] x[1]
        ports: a[0] a[1] out b[0] b[1] b[2]; internal: y
    "#]]
    .assert_eq(&res);
}

#[test]
fn tmp_explore() {
    let a = "analog begin V(out) <+ 0.0; end";
    let cases = [
        ("ansi1 bus first", format!("module m(input electrical [0:3] d, output electrical out); {a} endmodule")),
        ("ansi2 bus last", format!("module m(output electrical out, input electrical [0:3] d); {a} endmodule")),
        ("ansi3 bus middle", format!("module m(output electrical out, input electrical [0:1] d, inout electrical y); {a} endmodule")),
        ("ansi4 desc range", format!("module m(input electrical [3:0] d, output electrical out); {a} endmodule")),
        ("ansi5 two names one decl", format!("module m(input electrical [0:1] a, b, output electrical out); {a} endmodule")),
        ("ansi6 dir only, discipline in body", format!("module m(input [0:3] d, output out); electrical [0:3] d; electrical out; {a} endmodule")),
        ("ansi7 single bit [0:0]", format!("module m(input electrical [0:0] d, output electrical out); {a} endmodule")),
        ("ansi8 negative range", format!("module m(input electrical [-1:1] d, output electrical out); {a} endmodule")),
        ("ansi9 two adjacent buses", format!("module m(input electrical [0:1] a, input electrical [2:0] b, output electrical out); {a} endmodule")),
        ("ansi10 param width", format!("module m(input electrical [W-1:0] d, output electrical out); parameter integer W = 3; {a} endmodule")),
        ("ansi11 localparam width", format!("module m(input electrical [3:0] d, output electrical out); localparam integer W = 3; {a} endmodule")),
        ("nonansi1 bus last", format!("module m(out, d); output out; input [0:3] d; electrical out; electrical [0:3] d; {a} endmodule")),
        ("nonansi2 two names one decl", format!("module m(a, out, b); input [0:1] a, b; output out; electrical [0:1] a, b; electrical out; {a} endmodule")),
        ("nonansi3 combined dir+discipline", format!("module m(d, out); input electrical [0:3] d; output electrical out; {a} endmodule")),
        ("nonansi4 single bit", format!("module m(d, out); input [0:0] d; output out; electrical [0:0] d; electrical out; {a} endmodule")),
        ("nonansi5 negative", format!("module m(d, out); input [-1:1] d; output out; electrical [-1:1] d; electrical out; {a} endmodule")),
        ("nonansi6 width mismatch", format!("module m(d, out); input [0:3] d; output out; electrical [0:1] d; electrical out; {a} endmodule")),
        ("nonansi7 discipline scalar", format!("module m(d, out); input [0:3] d; output out; electrical d; electrical out; {a} endmodule")),
        ("nonansi8 dir scalar discipline bus", format!("module m(d, out); input d; output out; electrical [0:3] d; electrical out; {a} endmodule")),
        ("nonansi9 output bus driven", "module m(d, q); input d; output [1:0] q; electrical d; electrical [1:0] q; analog begin V(q[0]) <+ V(d); V(q[1]) <+ 2*V(d); end endmodule".to_string()),
        ("nonansi10 bus port + internal bus same width", format!("module m(d, out); input [0:1] d; output out; electrical [0:1] d, x; electrical out; {a} endmodule")),
        ("nonansi11 param width", format!("module m(d, out); parameter integer W = 3; input [W-1:0] d; output out; electrical [W-1:0] d; electrical out; {a} endmodule")),
        ("nonansi12 bus not in header", format!("module m(out); output out; input [0:1] d; electrical [0:1] d; electrical out; {a} endmodule")),
        ("nonansi13 header bit-select", format!("module m(d[0], out); input [0:1] d; output out; electrical [0:1] d; electrical out; {a} endmodule")),
    ];
    for (name, body) in cases {
        let src = format!("`include \"disciplines.vams\"\n{body}\n");
        let db = CompilationDB::new_virtual(&src).unwrap();
        let mut buf = Buffer::no_color();
        let modules = {
            let mut sink = ConsoleSink::buffer(&db, &mut buf);
            sink.annonymize_paths();
            super::collect_modules(&db, false, &mut sink)
        };
        let diag = String::from_utf8_lossy(buf.as_slice()).lines().filter(|l| l.starts_with("error") || l.starts_with("warning")).collect::<Vec<_>>().join(" | ");
        match modules {
            Some(modules) => {
                let m = modules[0].module;
                let p: Vec<_> = m.ports(&db).into_iter().map(|n| format!("{}{}", n.name(&db), if n.is_port(&db) {""} else {"(!)"})).collect();
                let i: Vec<_> = m.internal_nodes(&db).into_iter().map(|n| format!("{}{}", n.name(&db), if n.is_port(&db) {"(!)"} else {""})).collect();
                println!("{name}: ports={} internal={} {diag}", p.join(" "), i.join(" "));
            }
            None => println!("{name}: ERROR {diag}"),
        }
    }
}
