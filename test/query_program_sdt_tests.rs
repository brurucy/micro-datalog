use std::collections::HashSet;

use datalog_rule_macro::program;
use datalog_syntax::*;
use micro_datalog::{convert_fact, engine::datalog::MicroRuntime};

#[test]
fn test_sdt_basic_ancestor_bf() {
    let program = program! {
        ancestor(?x, ?y) <- [parent(?x, ?y)],
        ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
    };

    let mut runtime = MicroRuntime::new(program.clone());
    runtime.insert("parent", vec!["john", "bob"]);
    runtime.insert("parent", vec!["bob", "mary"]);

    let query = build_query!(ancestor("john", _));
    let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "SDT"));

    let expected: HashSet<_> = vec![("john", "bob"), ("john", "mary")]
        .into_iter()
        .collect();

    assert_eq!(expected, results);
}

#[test]
fn test_sdt_ancestor_ff() {
    let program = program! {
        ancestor(?x, ?y) <- [parent(?x, ?y)],
        ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
    };

    let mut runtime = MicroRuntime::new(program.clone());
    runtime.insert("parent", vec!["john", "bob"]);
    runtime.insert("parent", vec!["bob", "mary"]);

    let query = build_query!(ancestor(_, _));
    let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "SDT"));

    let expected: HashSet<_> = vec![("john", "bob"), ("bob", "mary"), ("john", "mary")]
        .into_iter()
        .collect();

    assert_eq!(expected, results);
}

#[test]
fn test_sdt_parity_with_bottom_up_ancestor() {
    let program = program! {
        ancestor(?x, ?y) <- [parent(?x, ?y)],
        ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
    };

    let mut runtime_bu = MicroRuntime::new(program.clone());
    let mut runtime_sdt = MicroRuntime::new(program.clone());

    let facts = vec![
        vec!["john", "bob"],
        vec!["bob", "mary"],
        vec!["mary", "sue"],
    ];
    for f in &facts {
        runtime_bu.insert("parent", f.clone());
        runtime_sdt.insert("parent", f.clone());
    }

    let query = build_query!(ancestor("john", _));

    let results_bu: HashSet<_> =
        convert_fact!(runtime_bu.query_program(&query, program.clone(), "Bottom-up"));
    let results_sdt: HashSet<_> =
        convert_fact!(runtime_sdt.query_program(&query, program, "SDT"));

    assert_eq!(results_bu, results_sdt, "SDT must produce same results as Bottom-up (MST)");
}

#[test]
fn test_sdt_parity_with_bottom_up_tc() {
    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
    };

    let mut runtime_bu = MicroRuntime::new(program.clone());
    let mut runtime_sdt = MicroRuntime::new(program.clone());

    let facts = vec![("a", "b"), ("b", "c"), ("c", "d"), ("d", "e")];
    for f in &facts {
        runtime_bu.insert("e", *f);
        runtime_sdt.insert("e", *f);
    }

    let query = build_query!(tc("a", _));

    let results_bu: HashSet<_> =
        convert_fact!(runtime_bu.query_program(&query, program.clone(), "Bottom-up"));
    let results_sdt: HashSet<_> =
        convert_fact!(runtime_sdt.query_program(&query, program, "SDT"));

    assert_eq!(results_bu, results_sdt, "SDT must produce same results as Bottom-up for TC");
    assert_eq!(results_sdt.len(), 4); // a->b, a->c, a->d, a->e
}

#[test]
fn test_sdt_same_generation() {
    let program = program! {
        sg(?x, ?y) <- [flat(?x, ?y)],
        sg(?y, ?x) <- [sg(?x, ?y)],
        sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
        sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
    };

    let mut runtime = MicroRuntime::new(program.clone());
    runtime.insert("up", ("b1", "a1"));
    runtime.insert("up", ("b2", "a1"));
    runtime.insert("up", ("b3", "a2"));
    runtime.insert("up", ("b4", "a2"));
    runtime.insert("flat", ("a1", "a2"));
    runtime.insert("down", ("a1", "b1"));
    runtime.insert("down", ("a1", "b2"));
    runtime.insert("down", ("a2", "b3"));
    runtime.insert("down", ("a2", "b4"));

    let query = build_query!(sg("b1", _));
    let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "SDT"));

    let expected: HashSet<_> = vec![
        ("b1", "b2"),
        ("b1", "b3"),
        ("b1", "b4"),
        ("b1", "b1"),
    ]
    .into_iter()
    .collect();

    assert_eq!(expected, results);
}
