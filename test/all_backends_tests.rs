/// Run all datalog engine and program transformation tests over BOTH backends
/// (SPJ and Free Join) to prove they produce identical results.
use std::collections::HashSet;

use datalog_rule_macro::program;
use datalog_syntax::*;
use micro_datalog::{convert_fact, engine::datalog::MicroRuntime};

/// Run the same test logic with both SPJ and Free Join backends.
fn run_on_both_engines<F>(test_fn: F)
where
    F: Fn(fn(Program) -> MicroRuntime),
{
    // SPJ backend
    test_fn(MicroRuntime::new);
    // Free Join backend
    test_fn(MicroRuntime::new_free_join);
}

// ============================================================================
// Datalog engine tests (from engine/datalog.rs)
// ============================================================================

#[test]
fn both_engines_insertions_and_query() {
    run_on_both_engines(|make_runtime| {
        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };

        let mut runtime = make_runtime(tc_program);
        vec![("a", "b"), ("b", "c"), ("c", "d")]
            .into_iter()
            .for_each(|xy| { runtime.insert("e", xy); });

        runtime.poll();

        let all = build_query!(tc(_, _));
        let all_from_a = build_query!(tc("a", _));

        let actual_all: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all));
        let expected_all: HashSet<(&str, &str)> = vec![
            ("a", "b"), ("b", "c"), ("c", "d"),
            ("a", "c"), ("b", "d"), ("a", "d"),
        ].into_iter().collect();
        assert_eq!(expected_all, actual_all);

        let actual_from_a: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all_from_a));
        let expected_from_a: HashSet<(&str, &str)> = vec![("a", "b"), ("a", "c"), ("a", "d")]
            .into_iter().collect();
        assert_eq!(expected_from_a, actual_from_a);

        expected_all.iter().for_each(|fact| {
            assert!(runtime.contains("tc", *fact).unwrap());
        });
    });
}

#[test]
fn both_engines_incremental_update() {
    run_on_both_engines(|make_runtime| {
        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };

        let mut runtime = make_runtime(tc_program);
        vec![("a", "b"), ("b", "c"), ("c", "d")]
            .into_iter()
            .for_each(|xy| { runtime.insert("e", xy); });
        runtime.poll();

        // Update
        runtime.insert("e", ("d", "e"));
        assert!(!runtime.safe());
        runtime.poll();
        assert!(runtime.safe());

        let all = build_query!(tc(_, _));
        let actual: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all));
        let expected: HashSet<(&str, &str)> = vec![
            ("a", "b"), ("b", "c"), ("c", "d"),
            ("a", "c"), ("b", "d"), ("a", "d"),
            ("d", "e"), ("c", "e"), ("b", "e"), ("a", "e"),
        ].into_iter().collect();
        assert_eq!(expected, actual);
    });
}

#[test]
fn both_engines_left_linear_tc() {
    run_on_both_engines(|make_runtime| {
        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), e(?y, ?z)]
        };

        let mut runtime = make_runtime(tc_program);
        vec![("a", "b"), ("b", "c"), ("c", "d")]
            .into_iter()
            .for_each(|xy| { runtime.insert("e", xy); });
        runtime.poll();

        let all = build_query!(tc(_, _));
        let actual: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all));
        assert_eq!(actual.len(), 6);
    });
}

#[test]
fn both_engines_stratified() {
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            base(?x, ?y) <- [edge(?x, ?y)],
            derived(?x, ?y) <- [base(?x, ?y)],
            derived(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)],
            top(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)]
        };

        let mut runtime = make_runtime(prog);
        vec![("a", "b"), ("b", "c")].into_iter().for_each(|edge| {
            runtime.insert("edge", edge);
        });
        runtime.poll();

        let base_q = build_query!(base(_, _));
        let base: HashSet<(&str, &str)> = convert_fact!(runtime.query(&base_q));
        assert_eq!(base, vec![("a", "b"), ("b", "c")].into_iter().collect());

        let derived_q = build_query!(derived(_, _));
        let derived: HashSet<(&str, &str)> = convert_fact!(runtime.query(&derived_q));
        assert_eq!(derived, vec![("a", "b"), ("b", "c"), ("a", "c")].into_iter().collect());

        let top_q = build_query!(top(_, _));
        let top: HashSet<(&str, &str)> = convert_fact!(runtime.query(&top_q));
        assert_eq!(top, vec![("a", "c")].into_iter().collect());
    });
}

// ============================================================================
// MST (Bottom-up) query_program tests
// ============================================================================

#[test]
fn both_engines_mst_ancestor_bf() {
    run_on_both_engines(|make_runtime| {
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        let mut runtime = make_runtime(program.clone());
        runtime.insert("parent", vec!["john", "bob"]);
        runtime.insert("parent", vec!["bob", "mary"]);

        let query = build_query!(ancestor("john", _));
        let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "Bottom-up"));
        let expected: HashSet<_> = vec![("john", "bob"), ("john", "mary")].into_iter().collect();
        assert_eq!(expected, results);
    });
}

#[test]
fn both_engines_mst_ancestor_ff() {
    run_on_both_engines(|make_runtime| {
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        let mut runtime = make_runtime(program.clone());
        runtime.insert("parent", vec!["john", "bob"]);
        runtime.insert("parent", vec!["bob", "mary"]);

        let query = build_query!(ancestor(_, _));
        let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "Bottom-up"));
        let expected: HashSet<_> = vec![("john", "bob"), ("bob", "mary"), ("john", "mary")]
            .into_iter().collect();
        assert_eq!(expected, results);
    });
}

#[test]
fn both_engines_mst_same_generation() {
    run_on_both_engines(|make_runtime| {
        let program = program! {
            sg(?x, ?y) <- [flat(?x, ?y)],
            sg(?y, ?x) <- [sg(?x, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
        };

        let mut runtime = make_runtime(program.clone());
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
        let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "Bottom-up"));
        let expected: HashSet<_> = vec![
            ("b1", "b2"), ("b1", "b3"), ("b1", "b4"), ("b1", "b1"),
        ].into_iter().collect();
        assert_eq!(expected, results);
    });
}

// ============================================================================
// SDT query_program tests
// ============================================================================

#[test]
fn both_engines_sdt_ancestor_bf() {
    run_on_both_engines(|make_runtime| {
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        let mut runtime = make_runtime(program.clone());
        runtime.insert("parent", vec!["john", "bob"]);
        runtime.insert("parent", vec!["bob", "mary"]);
        runtime.insert("parent", vec!["mary", "sue"]);

        let query = build_query!(ancestor("john", _));
        let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "SDT"));
        let expected: HashSet<_> = vec![("john", "bob"), ("john", "mary"), ("john", "sue")]
            .into_iter().collect();
        assert_eq!(expected, results);
    });
}

#[test]
fn both_engines_sdt_tc_bf() {
    run_on_both_engines(|make_runtime| {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };

        let mut runtime = make_runtime(program.clone());
        for (s, d) in [("a","b"),("b","c"),("c","d"),("d","e")] {
            runtime.insert("e", (s, d));
        }

        let query = build_query!(tc("a", _));
        let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "SDT"));
        assert_eq!(results.len(), 4);
    });
}

#[test]
fn both_engines_sdt_ancestor_ff() {
    run_on_both_engines(|make_runtime| {
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        let mut runtime = make_runtime(program.clone());
        runtime.insert("parent", vec!["john", "bob"]);
        runtime.insert("parent", vec!["bob", "mary"]);

        let query = build_query!(ancestor(_, _));
        let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "SDT"));
        let expected: HashSet<_> = vec![("john", "bob"), ("bob", "mary"), ("john", "mary")]
            .into_iter().collect();
        assert_eq!(expected, results);
    });
}

// ============================================================================
// Cyclic graph (stress for both engines)
// ============================================================================

#[test]
fn both_engines_cyclic_graph() {
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };

        let mut runtime = make_runtime(prog);
        for (s, d) in [("a","b"),("b","c"),("c","d"),("d","e"),("e","f"),("f","a")] {
            runtime.insert("e", (s, d));
        }
        runtime.poll();

        let all = build_query!(tc(_, _));
        let results: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all));
        assert_eq!(results.len(), 36); // 6×6 full closure
    });
}

// ============================================================================
// Nonlinear TC (self-join)
// ============================================================================

#[test]
fn both_engines_nonlinear_tc() {
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
        };

        let mut runtime = make_runtime(prog);
        for (s, d) in [("a","b"),("b","c"),("c","d")] {
            runtime.insert("e", (s, d));
        }
        runtime.poll();

        let all = build_query!(tc(_, _));
        let results: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all));
        assert_eq!(results.len(), 6);
    });
}

// ============================================================================
// The two bugs Free Join was supposed to fix
// ============================================================================

#[test]
fn free_join_fixes_fb_linear_tc() {
    let prog = program! { tc(?x, ?y) <- [e(?x, ?y)], tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)] };
    let mut rt = MicroRuntime::new_free_join(prog);
    for (s, d) in [("a","b"),("b","c"),("c","d"),("d","e"),("e","f"),("f","a")] {
        rt.insert("e", (s, d));
    }
    rt.poll();
    // fb query: who reaches "a"?
    let q = build_query!(tc(_, "a"));
    let results: HashSet<(&str, &str)> = convert_fact!(rt.query(&q));
    assert_eq!(results.len(), 6, "Free Join fb: all 6 nodes should reach 'a' in cycle");
}

#[test]
fn free_join_fixes_bb_multi_hop_ancestor() {
    let prog = program! {
        ancestor(?x, ?y) <- [parent(?x, ?y)],
        ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
    };
    let mut rt = MicroRuntime::new_free_join(prog);
    rt.insert("parent", ("alice", "carol"));
    rt.insert("parent", ("carol", "frank"));
    rt.insert("parent", ("frank", "ivy"));
    rt.poll();
    // bb query: 3-hop path
    let q = build_query!(ancestor("alice", "ivy"));
    let results: HashSet<(&str, &str)> = convert_fact!(rt.query(&q));
    assert_eq!(results.len(), 1, "Free Join bb: alice->carol->frank->ivy should be found");
}

// ============================================================================
// Systematic correctness audit: every strategy × pattern × program
// against naive (poll+query) ground truth
// ============================================================================

fn naive_ground_truth(
    make_runtime: fn(Program) -> MicroRuntime,
    program: &Program,
    facts: &[(&str, Vec<&str>)],
    query: &Query,
) -> HashSet<Vec<String>> {
    let mut rt = make_runtime(program.clone());
    for (rel, fact) in facts { rt.insert(rel, fact.clone()); }
    rt.poll();
    rt.query(query).unwrap()
        .map(|a| a.into_iter().map(|tv| match tv {
            TypedValue::Str(s) => s, TypedValue::Int(i) => i.to_string(),
            TypedValue::Bool(b) => b.to_string(),
        }).collect()).collect()
}

fn strategy_result(
    make_runtime: fn(Program) -> MicroRuntime,
    program: &Program,
    facts: &[(&str, Vec<&str>)],
    query: &Query,
    strategy: &str,
) -> HashSet<Vec<String>> {
    let mut rt = make_runtime(program.clone());
    for (rel, fact) in facts { rt.insert(rel, fact.clone()); }
    rt.query_program(query, program.clone(), strategy).unwrap()
        .map(|a| a.into_iter().map(|tv| match tv {
            TypedValue::Str(s) => s, TypedValue::Int(i) => i.to_string(),
            TypedValue::Bool(b) => b.to_string(),
        }).collect()).collect()
}

fn check_correctness(
    label: &str,
    program: &Program,
    facts: &[(&str, Vec<&str>)],
    query: &Query,
) -> Vec<String> {
    let mut failures = Vec::new();

    let spj_truth = naive_ground_truth(MicroRuntime::new, program, facts, query);
    let fj_truth = naive_ground_truth(MicroRuntime::new_free_join, program, facts, query);

    if spj_truth != fj_truth {
        failures.push(format!("{}: Naive+SPJ ({}) != Naive+FJ ({})", label, spj_truth.len(), fj_truth.len()));
    }

    let truth = &fj_truth;

    // Check each (strategy, backend) combination
    let combos: Vec<(&str, &str, fn(Program) -> MicroRuntime)> = vec![
        ("Bottom-up", "SPJ", MicroRuntime::new),
        ("Bottom-up", "FJ", MicroRuntime::new_free_join),
        ("SDT", "SPJ", MicroRuntime::new),
        ("SDT", "FJ", MicroRuntime::new_free_join),
    ];

    for (strategy, backend, make_rt) in combos {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            strategy_result(make_rt, program, facts, query, strategy)
        }));
        match result {
            Ok(r) => {
                if &r != truth {
                    failures.push(format!("{}: {}+{} got {} facts, expected {}",
                        label, strategy, backend, r.len(), truth.len()));
                }
            }
            Err(_) => {
                failures.push(format!("{}: {}+{} PANICKED", label, strategy, backend));
            }
        }
    }

    failures
}

#[test]
fn correctness_audit() {
    let linear_tc = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
    };
    let left_tc = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [tc(?x, ?y), e(?y, ?z)]
    };
    let ancestor = program! {
        ancestor(?x, ?y) <- [parent(?x, ?y)],
        ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
    };
    let same_gen = program! {
        sg(?x, ?y) <- [flat(?x, ?y)],
        sg(?y, ?x) <- [sg(?x, ?y)],
        sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
        sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
    };
    let two_hop = program! {
        hop2(?x, ?z) <- [e(?x, ?y), e(?y, ?z)]
    };

    let cycle6: Vec<(&str, Vec<&str>)> = vec![
        ("e", vec!["a","b"]), ("e", vec!["b","c"]), ("e", vec!["c","d"]),
        ("e", vec!["d","e"]), ("e", vec!["e","f"]), ("e", vec!["f","a"]),
    ];
    let chain4: Vec<(&str, Vec<&str>)> = vec![
        ("e", vec!["a","b"]), ("e", vec!["b","c"]), ("e", vec!["c","d"]),
    ];
    let family: Vec<(&str, Vec<&str>)> = vec![
        ("parent", vec!["alice","carol"]), ("parent", vec!["alice","dave"]),
        ("parent", vec!["bob","eve"]), ("parent", vec!["carol","frank"]),
        ("parent", vec!["dave","grace"]), ("parent", vec!["eve","henry"]),
        ("parent", vec!["frank","ivy"]), ("parent", vec!["grace","jack"]),
    ];
    let sg_data: Vec<(&str, Vec<&str>)> = vec![
        ("flat", vec!["r1","r2"]),
        ("up", vec!["m1","r1"]), ("up", vec!["m2","r1"]),
        ("up", vec!["m3","r2"]), ("up", vec!["m4","r2"]),
        ("down", vec!["r1","m1"]), ("down", vec!["r1","m2"]),
        ("down", vec!["r2","m3"]), ("down", vec!["r2","m4"]),
        ("up", vec!["l1","m1"]), ("up", vec!["l2","m1"]),
        ("up", vec!["l3","m2"]), ("up", vec!["l4","m2"]),
        ("down", vec!["m1","l1"]), ("down", vec!["m1","l2"]),
        ("down", vec!["m2","l3"]), ("down", vec!["m2","l4"]),
    ];
    let chain5: Vec<(&str, Vec<&str>)> = vec![
        ("e", vec!["a","b"]), ("e", vec!["b","c"]),
        ("e", vec!["c","d"]), ("e", vec!["d","e"]), ("e", vec!["b","d"]),
    ];

    struct TestCase<'a> {
        label: &'a str,
        program: &'a Program,
        facts: &'a [(&'a str, Vec<&'a str>)],
        query: Query<'a>,
    }

    let cases = vec![
        // Linear TC × 4 patterns
        TestCase { label: "linTC bf", program: &linear_tc, facts: &cycle6, query: build_query!(tc("a", _)) },
        TestCase { label: "linTC fb", program: &linear_tc, facts: &cycle6, query: build_query!(tc(_, "a")) },
        TestCase { label: "linTC bb", program: &linear_tc, facts: &cycle6, query: build_query!(tc("a", "d")) },
        TestCase { label: "linTC ff", program: &linear_tc, facts: &cycle6, query: build_query!(tc(_, _)) },
        // Left-linear TC × 4 patterns
        TestCase { label: "leftTC bf", program: &left_tc, facts: &cycle6, query: build_query!(tc("a", _)) },
        TestCase { label: "leftTC fb", program: &left_tc, facts: &cycle6, query: build_query!(tc(_, "a")) },
        TestCase { label: "leftTC bb", program: &left_tc, facts: &cycle6, query: build_query!(tc("a", "d")) },
        TestCase { label: "leftTC ff", program: &left_tc, facts: &cycle6, query: build_query!(tc(_, _)) },
        // Ancestor × 4 patterns
        TestCase { label: "anc bf", program: &ancestor, facts: &family, query: build_query!(ancestor("alice", _)) },
        TestCase { label: "anc fb", program: &ancestor, facts: &family, query: build_query!(ancestor(_, "ivy")) },
        TestCase { label: "anc bb+", program: &ancestor, facts: &family, query: build_query!(ancestor("alice", "ivy")) },
        TestCase { label: "anc bb-", program: &ancestor, facts: &family, query: build_query!(ancestor("alice", "henry")) },
        TestCase { label: "anc ff", program: &ancestor, facts: &family, query: build_query!(ancestor(_, _)) },
        // Same-gen × 4 patterns
        TestCase { label: "sg bf", program: &same_gen, facts: &sg_data, query: build_query!(sg("l1", _)) },
        TestCase { label: "sg fb", program: &same_gen, facts: &sg_data, query: build_query!(sg(_, "l1")) },
        TestCase { label: "sg bb", program: &same_gen, facts: &sg_data, query: build_query!(sg("l1", "l3")) },
        TestCase { label: "sg ff", program: &same_gen, facts: &sg_data, query: build_query!(sg(_, _)) },
        // 2-hop × 4 patterns
        TestCase { label: "hop2 bf", program: &two_hop, facts: &chain5, query: build_query!(hop2("a", _)) },
        TestCase { label: "hop2 fb", program: &two_hop, facts: &chain5, query: build_query!(hop2(_, "e")) },
        TestCase { label: "hop2 bb", program: &two_hop, facts: &chain5, query: build_query!(hop2("a", "c")) },
        TestCase { label: "hop2 ff", program: &two_hop, facts: &chain5, query: build_query!(hop2(_, _)) },
    ];

    let mut all_failures = Vec::new();
    for case in &cases {
        let failures = check_correctness(case.label, case.program, case.facts, &case.query);
        all_failures.extend(failures);
    }

    if !all_failures.is_empty() {
        eprintln!("\n=== CORRECTNESS AUDIT FAILURES ({}) ===", all_failures.len());
        for f in &all_failures {
            eprintln!("  FAIL: {}", f);
        }
        eprintln!("=== END FAILURES ===\n");
    }

    // Report all failures at once instead of failing on the first
    assert!(all_failures.is_empty(),
        "\n{} correctness failures found:\n{}", all_failures.len(),
        all_failures.iter().map(|f| format!("  - {}", f)).collect::<Vec<_>>().join("\n"));
}

// ============================================================================
// Nonlinear TC correctness: SDT must match semi-naive on all patterns
// ============================================================================

#[test]
fn both_engines_nonlinear_tc_all_patterns() {
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
        };

        let mut rt = make_runtime(prog.clone());
        for (s, d) in [("a","b"),("b","c"),("c","d"),("d","e"),("e","f"),("f","a")] {
            rt.insert("e", (s, d));
        }
        rt.poll();

        // Ground truth
        let all_ff = build_query!(tc(_, _));
        let all: HashSet<(&str, &str)> = convert_fact!(rt.query(&all_ff));
        assert_eq!(all.len(), 36, "Full cycle: 6x6=36");

        // BF via SDT
        let bf_q = build_query!(tc("a", _));
        let sdt_bf: HashSet<_> = convert_fact!(rt.query_program(&bf_q, prog.clone(), "SDT"));
        assert_eq!(sdt_bf.len(), 6, "SDT BF on nonlinear TC");

        // FF via SDT
        let sdt_ff: HashSet<_> = convert_fact!(rt.query_program(&all_ff, prog.clone(), "SDT"));
        assert_eq!(sdt_ff.len(), 36, "SDT FF on nonlinear TC");

        // BF via MST
        let mst_bf: HashSet<_> = convert_fact!(rt.query_program(&bf_q, prog.clone(), "Bottom-up"));
        assert_eq!(mst_bf.len(), 6, "MST BF on nonlinear TC");
    });
}

// ============================================================================
// Audit-recommended tests (from audit_sdt_compliance.md)
// ============================================================================

// Gap 1: Exact transformation output for paper's running example
#[test]
fn sdt_running_example_exact_rules() {
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            rel(?x, ?y) <- [imm(?x, ?y)],
            rel(?x, ?y) <- [imm(?u, ?v), rel(?u, ?x), rel(?v, ?y)]
        };
        let mut rt = make_runtime(prog.clone());
        rt.insert("imm", ("a", "b"));
        rt.insert("imm", ("b", "c"));
        rt.insert("imm", ("c", "d"));

        let query = build_query!(rel("a", _));
        let sdt: HashSet<_> = convert_fact!(rt.query_program(&query, prog.clone(), "SDT"));
        let mst: HashSet<_> = convert_fact!(rt.query_program(&query, prog, "Bottom-up"));
        assert_eq!(sdt, mst, "SDT must match MST on paper's running example");
    });
}

// Gap 2: Pointer analysis (Andersen's)
#[test]
fn sdt_pointer_analysis() {
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            pt(?p, ?q) <- [bare_addr(?p, ?q)],
            pt(?p, ?q) <- [bare_bare(?p, ?r), pt(?r, ?q)],
            pt(?p, ?q) <- [bare_star(?p, ?s), pt(?s, ?r), pt(?r, ?q)],
            pt(?p, ?q) <- [star_bare(?r, ?s), pt(?r, ?p), pt(?s, ?q)]
        };
        let mut rt_sdt = make_runtime(prog.clone());
        let mut rt_mst = make_runtime(prog.clone());
        let mut rt_naive = make_runtime(prog.clone());

        let facts = vec![
            ("bare_addr", vec!["a", "x"]),
            ("bare_addr", vec!["b", "y"]),
            ("bare_bare", vec!["c", "a"]),
            ("bare_bare", vec!["d", "b"]),
            ("bare_star", vec!["e", "a"]),
            ("star_bare", vec!["a", "b"]),
        ];
        for (rel, fact) in &facts {
            rt_sdt.insert(rel, fact.clone());
            rt_mst.insert(rel, fact.clone());
            rt_naive.insert(rel, fact.clone());
        }
        rt_naive.poll();

        let query = build_query!(pt("c", _));
        let naive: HashSet<(&str, &str)> = convert_fact!(rt_naive.query(&query));
        let sdt: HashSet<_> = convert_fact!(rt_sdt.query_program(&query, prog.clone(), "SDT"));
        let mst: HashSet<_> = convert_fact!(rt_mst.query_program(&query, prog, "Bottom-up"));

        assert_eq!(naive, sdt, "SDT pointer analysis must match naive");
        assert_eq!(naive, mst, "MST pointer analysis must match naive");
    });
}

// Gap 3: SDT fb on recursive TC
#[test]
fn sdt_tc_fb_recursive() {
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let mut rt = make_runtime(prog.clone());
        for (s, d) in [("a","b"),("b","c"),("c","d")] {
            rt.insert("e", (s, d));
        }
        rt.poll();
        let naive: HashSet<(&str, &str)> = convert_fact!(rt.query(&build_query!(tc(_, "d"))));

        let mut rt2 = make_runtime(prog.clone());
        for (s, d) in [("a","b"),("b","c"),("c","d")] {
            rt2.insert("e", (s, d));
        }
        let sdt: HashSet<_> = convert_fact!(rt2.query_program(
            &build_query!(tc(_, "d")), prog, "SDT"
        ));
        assert_eq!(naive, sdt, "SDT fb recursive must match naive");
        assert_eq!(naive.len(), 3); // a->d, b->d, c->d
    });
}

// Gap 4: SDT bb with subsumption-triggering program
#[test]
fn sdt_ancestor_bb_multi_hop() {
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };
        let mut rt = make_runtime(prog.clone());
        rt.insert("parent", ("alice", "carol"));
        rt.insert("parent", ("carol", "frank"));
        rt.insert("parent", ("frank", "ivy"));

        let query = build_query!(ancestor("alice", "ivy"));
        let sdt: HashSet<_> = convert_fact!(rt.query_program(&query, prog.clone(), "SDT"));
        let mst: HashSet<_> = convert_fact!(rt.query_program(&query, prog, "Bottom-up"));
        assert_eq!(sdt.len(), 1, "SDT bb multi-hop must find alice->ivy");
        assert_eq!(sdt, mst);
    });
}

// Gap 6: SDT empty result
#[test]
fn sdt_empty_result() {
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let mut rt = make_runtime(prog.clone());
        rt.insert("e", ("a", "b"));

        let query = build_query!(tc("z", _));
        let sdt: HashSet<(&str, &str)> = convert_fact!(rt.query_program(&query, prog, "SDT"));
        assert!(sdt.is_empty(), "SDT must return empty for unreachable node");
    });
}

// Gap 8: Same-generation bb
#[test]
fn sdt_same_generation_bb() {
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            sg(?x, ?y) <- [flat(?x, ?y)],
            sg(?y, ?x) <- [sg(?x, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
        };
        let mut rt = make_runtime(prog.clone());
        rt.insert("up", ("b1", "a1"));
        rt.insert("up", ("b2", "a1"));
        rt.insert("flat", ("a1", "a1"));
        rt.insert("down", ("a1", "b1"));
        rt.insert("down", ("a1", "b2"));

        let query = build_query!(sg("b1", "b2"));
        let sdt: HashSet<_> = convert_fact!(rt.query_program(&query, prog.clone(), "SDT"));
        let mst: HashSet<_> = convert_fact!(rt.query_program(&query, prog, "Bottom-up"));
        assert_eq!(sdt, mst, "SDT same-gen bb must match MST");
        assert_eq!(sdt.len(), 1);
    });
}

// ============================================================================
// F1: Guaranteed flag — non-first-hypothesis IDB should NOT suppress
// ============================================================================

#[test]
fn f1_non_guaranteed_pattern_must_not_suppress() {
    // p(x,y) :- q(x,z), p(z,y), r(y,w), p(w,x)
    // Query: p("a", _) -> bf
    // Body: q(x,z) EDB, p(z,y) position 2 -> bf (NOT guaranteed, position > 1),
    //       r(y,w) EDB, p(w,x) position 4 -> bb
    // bf subsumes bb, but bf is NOT guaranteed (position 2, not 1).
    // SDT must NOT suppress bb demands with bf negation.
    let prog = program! {
        p(?x, ?y) <- [q(?x, ?z), p(?z, ?y), r(?y, ?w), p(?w, ?x)]
    };
    // Need base case too
    let prog_with_base = program! {
        p(?x, ?y) <- [base(?x, ?y)],
        p(?x, ?y) <- [q(?x, ?z), p(?z, ?y), r(?y, ?w), p(?w, ?x)]
    };

    run_on_both_engines(|make_runtime| {
        let mut rt_naive = make_runtime(prog_with_base.clone());
        let mut rt_sdt = make_runtime(prog_with_base.clone());

        let facts: Vec<(&str, (&str, &str))> = vec![
            ("base", ("a", "b")), ("base", ("b", "c")), ("base", ("c", "a")),
            ("q", ("a", "b")), ("q", ("b", "c")), ("q", ("c", "a")),
            ("r", ("a", "b")), ("r", ("b", "c")), ("r", ("c", "a")),
        ];
        for (rel, (a, b)) in &facts {
            rt_naive.insert(rel, (*a, *b));
            rt_sdt.insert(rel, (*a, *b));
        }
        rt_naive.poll();

        let query = build_query!(p("a", _));
        let naive: HashSet<(&str, &str)> = convert_fact!(rt_naive.query(&query));
        let sdt: HashSet<_> = convert_fact!(rt_sdt.query_program(&query, prog_with_base.clone(), "SDT"));

        assert_eq!(naive, sdt,
            "F1: SDT with non-guaranteed subsuming pattern must match naive. \
             Non-first-hypothesis bf must NOT suppress bb.");
    });
}

// ============================================================================
// F2: Exhaustive pattern negation — all possible subsuming patterns
// ============================================================================

#[test]
fn f2_exhaustive_negation() {
    // The paper includes negated hypotheses for ALL properly subsuming patterns,
    // including patterns never computed (like fb, ff). These are trivially satisfied
    // since those demand predicates have no facts. Our implementation should at
    // minimum produce CORRECT results regardless of whether exhaustive or minimal
    // negation is used. This test verifies correctness.
    let prog = program! {
        rel(?x, ?y) <- [imm(?x, ?y)],
        rel(?x, ?y) <- [imm(?u, ?v), rel(?u, ?x), rel(?v, ?y)]
    };

    run_on_both_engines(|make_runtime| {
        let mut rt_naive = make_runtime(prog.clone());
        let mut rt_sdt = make_runtime(prog.clone());

        for (a, b) in [("a","b"),("b","c"),("c","d"),("d","a")] {
            rt_naive.insert("imm", (a, b));
            rt_sdt.insert("imm", (a, b));
        }
        rt_naive.poll();

        let query = build_query!(rel("a", _));
        let naive: HashSet<(&str, &str)> = convert_fact!(rt_naive.query(&query));
        let sdt: HashSet<_> = convert_fact!(rt_sdt.query_program(&query, prog.clone(), "SDT"));

        assert_eq!(naive, sdt,
            "F2: SDT must produce correct results (exhaustive vs minimal negation)");
    });
}

// ============================================================================
// F5: redirect_subsumed_body_atoms correctness
// ============================================================================

#[test]
fn f5_redirect_subsumed_body_atoms_correct() {
    // When SDT suppresses bb demands because bf subsumes bb,
    // body atoms referencing rel_bb must be redirected to rel_bf.
    // Verify end-to-end correctness.
    let prog = program! {
        rel(?x, ?y) <- [imm(?x, ?y)],
        rel(?x, ?y) <- [imm(?u, ?v), rel(?u, ?x), rel(?v, ?y)]
    };

    run_on_both_engines(|make_runtime| {
        let mut rt_naive = make_runtime(prog.clone());
        let mut rt_sdt = make_runtime(prog.clone());
        let mut rt_mst = make_runtime(prog.clone());

        for (a, b) in [("a","b"),("b","c"),("c","d")] {
            rt_naive.insert("imm", (a, b));
            rt_sdt.insert("imm", (a, b));
            rt_mst.insert("imm", (a, b));
        }
        rt_naive.poll();

        let query = build_query!(rel("a", _));
        let naive: HashSet<(&str, &str)> = convert_fact!(rt_naive.query(&query));
        let sdt: HashSet<_> = convert_fact!(rt_sdt.query_program(&query, prog.clone(), "SDT"));
        let mst: HashSet<_> = convert_fact!(rt_mst.query_program(&query, prog.clone(), "Bottom-up"));

        assert_eq!(naive, sdt, "F5: SDT with body atom redirection must match naive");
        assert_eq!(naive, mst, "F5: MST must match naive");
    });
}

// ============================================================================
// F3: Binary rule splitting — rules with >2 body atoms must still be correct
// ============================================================================

#[test]
fn f3_multi_hypothesis_rules_correct() {
    // Even without binary splitting, rules with 3+ body atoms must produce
    // correct results. Test with same-generation (4-atom rule) and pointer analysis.
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            sg(?x, ?y) <- [flat(?x, ?y)],
            sg(?y, ?x) <- [sg(?x, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
        };

        let mut rt_naive = make_runtime(prog.clone());
        let mut rt_sdt = make_runtime(prog.clone());

        for f in [("up", ("b1","a1")), ("up", ("b2","a1")), ("up", ("b3","a2")), ("up", ("b4","a2")),
                  ("down", ("a1","b1")), ("down", ("a1","b2")), ("down", ("a2","b3")), ("down", ("a2","b4")),
                  ("flat", ("a1","a2"))] {
            rt_naive.insert(f.0, f.1);
            rt_sdt.insert(f.0, f.1);
        }
        rt_naive.poll();

        let query = build_query!(sg("b1", _));
        let naive: HashSet<(&str, &str)> = convert_fact!(rt_naive.query(&query));
        let sdt: HashSet<_> = convert_fact!(rt_sdt.query_program(&query, prog.clone(), "SDT"));

        assert_eq!(naive, sdt,
            "F3: Multi-hypothesis rules (same-gen, 4 atoms) must be correct without binary splitting");
        assert!(naive.len() >= 4, "b1 should be same-gen as b1,b2,b3,b4");
    });
}

// ============================================================================
// Gap 5: Nonlinear TC bb
// ============================================================================

#[test]
fn gap5_nonlinear_tc_bb() {
    run_on_both_engines(|make_runtime| {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
        };

        let mut rt = make_runtime(prog.clone());
        for (s, d) in [("a","b"),("b","c"),("c","d"),("d","e")] {
            rt.insert("e", (s, d));
        }
        rt.poll();

        // BB query: tc("a", "e") should exist (a->b->c->d->e, 4 hops)
        let query = build_query!(tc("a", "e"));
        let naive: HashSet<(&str, &str)> = convert_fact!(rt.query(&query));
        assert_eq!(naive.len(), 1);

        let mut rt_sdt = make_runtime(prog.clone());
        let mut rt_mst = make_runtime(prog.clone());
        for (s, d) in [("a","b"),("b","c"),("c","d"),("d","e")] {
            rt_sdt.insert("e", (s, d));
            rt_mst.insert("e", (s, d));
        }

        let sdt: HashSet<_> = convert_fact!(rt_sdt.query_program(&query, prog.clone(), "SDT"));
        let mst: HashSet<_> = convert_fact!(rt_mst.query_program(&query, prog.clone(), "Bottom-up"));

        assert_eq!(naive, sdt, "Gap5: Nonlinear TC bb SDT must match naive");
        assert_eq!(naive, mst, "Gap5: Nonlinear TC bb MST must match naive");
    });
}
