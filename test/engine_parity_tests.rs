/// Engine parity tests: SDT vs pure semi-naive (ground truth).
///
/// Covers 5 programs × 4 query patterns where supported.
/// Working: bf, ff on all programs. bb on 1-hop and nonrecursive.
/// Known limitations: fb and multi-hop bb (demand propagation + SPJ chaining issues).
use std::collections::HashSet;

use datalog_rule_macro::program;
use datalog_syntax::*;
use micro_datalog::{convert_fact, engine::datalog::MicroRuntime};

fn run_naive_sdt(
    program: Program,
    facts: Vec<(&str, Vec<&str>)>,
    query: Query,
) -> (HashSet<Vec<String>>, HashSet<Vec<String>>) {
    let mut naive = MicroRuntime::new(program.clone());
    for (rel, fact) in &facts { naive.insert(rel, fact.clone()); }
    naive.poll();
    let naive_r: HashSet<Vec<String>> = naive.query(&query).unwrap()
        .map(|a| a.into_iter().map(|tv| match tv {
            TypedValue::Str(s) => s, TypedValue::Int(i) => i.to_string(), TypedValue::Bool(b) => b.to_string(),
        }).collect()).collect();

    let mut sdt = MicroRuntime::new(program.clone());
    for (rel, fact) in &facts { sdt.insert(rel, fact.clone()); }
    let sdt_r: HashSet<Vec<String>> = sdt.query_program(&query, program, "SDT").unwrap()
        .map(|a| a.into_iter().map(|tv| match tv {
            TypedValue::Str(s) => s, TypedValue::Int(i) => i.to_string(), TypedValue::Bool(b) => b.to_string(),
        }).collect()).collect();

    (naive_r, sdt_r)
}

fn assert_parity(naive: &HashSet<Vec<String>>, sdt: &HashSet<Vec<String>>, label: &str) {
    assert_eq!(naive, sdt, "{}: semi-naive vs SDT divergence", label);
}

fn cyclic_graph() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("e", vec!["a","b"]), ("e", vec!["b","c"]), ("e", vec!["c","d"]),
        ("e", vec!["d","e"]), ("e", vec!["e","f"]), ("e", vec!["f","a"]),
        ("e", vec!["a","d"]), ("e", vec!["c","f"]), ("e", vec!["b","e"]),
    ]
}
fn family() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("parent", vec!["alice","carol"]), ("parent", vec!["alice","dave"]),
        ("parent", vec!["bob","eve"]),     ("parent", vec!["carol","frank"]),
        ("parent", vec!["dave","grace"]),  ("parent", vec!["eve","henry"]),
        ("parent", vec!["frank","ivy"]),   ("parent", vec!["grace","jack"]),
    ]
}
fn sg_tree() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("flat", vec!["r1","r2"]),
        ("up", vec!["m1","r1"]), ("up", vec!["m2","r1"]),
        ("up", vec!["m3","r2"]), ("up", vec!["m4","r2"]),
        ("down", vec!["r1","m1"]), ("down", vec!["r1","m2"]),
        ("down", vec!["r2","m3"]), ("down", vec!["r2","m4"]),
        ("up", vec!["l1","m1"]), ("up", vec!["l2","m1"]),
        ("up", vec!["l3","m2"]), ("up", vec!["l4","m2"]),
        ("up", vec!["l5","m3"]), ("up", vec!["l6","m3"]),
        ("up", vec!["l7","m4"]), ("up", vec!["l8","m4"]),
        ("down", vec!["m1","l1"]), ("down", vec!["m1","l2"]),
        ("down", vec!["m2","l3"]), ("down", vec!["m2","l4"]),
        ("down", vec!["m3","l5"]), ("down", vec!["m3","l6"]),
        ("down", vec!["m4","l7"]), ("down", vec!["m4","l8"]),
        ("flat", vec!["m1","m2"]), ("flat", vec!["m3","m4"]),
    ]
}
fn chain() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![("e", vec!["a","b"]), ("e", vec!["b","c"]), ("e", vec!["c","d"]), ("e", vec!["d","e"]), ("e", vec!["b","d"])]
}

fn linear_tc() -> Program { program! { tc(?x, ?y) <- [e(?x, ?y)], tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)] } }
fn left_linear_tc() -> Program { program! { tc(?x, ?y) <- [e(?x, ?y)], tc(?x, ?z) <- [tc(?x, ?y), e(?y, ?z)] } }
fn same_gen() -> Program {
    program! {
        sg(?x, ?y) <- [flat(?x, ?y)], sg(?y, ?x) <- [sg(?x, ?y)],
        sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
        sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
    }
}
fn ancestor_prog() -> Program { program! { ancestor(?x, ?y) <- [parent(?x, ?y)], ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)] } }
fn two_hop() -> Program { program! { hop2(?x, ?z) <- [e(?x, ?y), e(?y, ?z)] } }

// P1: Linear TC
#[test] fn p1_bf() { let (n, s) = run_naive_sdt(linear_tc(), cyclic_graph(), build_query!(tc("a", _))); assert_parity(&n, &s, "p1 bf"); assert_eq!(n.len(), 6); }
#[test] fn p1_bb() { let (n, s) = run_naive_sdt(linear_tc(), cyclic_graph(), build_query!(tc("a", "d"))); assert_parity(&n, &s, "p1 bb"); assert_eq!(n.len(), 1); }
#[test] fn p1_bb_neg() { let (n, s) = run_naive_sdt(linear_tc(), vec![("e", vec!["a","b"]),("e", vec!["b","c"])], build_query!(tc("c", "a"))); assert_parity(&n, &s, "p1 bb-"); assert_eq!(n.len(), 0); }
#[test] fn p1_ff() { let (n, s) = run_naive_sdt(linear_tc(), cyclic_graph(), build_query!(tc(_, _))); assert_parity(&n, &s, "p1 ff"); assert_eq!(n.len(), 36); }

// P2: Left-linear TC
#[test] fn p2_bf() { let (n, s) = run_naive_sdt(left_linear_tc(), cyclic_graph(), build_query!(tc("a", _))); assert_parity(&n, &s, "p2 bf"); assert_eq!(n.len(), 6); }
#[test] fn p2_ff() { let (n, s) = run_naive_sdt(left_linear_tc(), cyclic_graph(), build_query!(tc(_, _))); assert_parity(&n, &s, "p2 ff"); assert_eq!(n.len(), 36); }

// P3: Same-generation
#[test] fn p3_bf() { let (n, s) = run_naive_sdt(same_gen(), sg_tree(), build_query!(sg("l1", _))); assert_parity(&n, &s, "p3 bf"); assert!(n.len() >= 8); }
#[test] fn p3_ff() { let (n, s) = run_naive_sdt(same_gen(), sg_tree(), build_query!(sg(_, _))); assert_parity(&n, &s, "p3 ff"); assert!(n.len() > 20); }

// P4: Ancestor
#[test] fn p4_bf() { let (n, s) = run_naive_sdt(ancestor_prog(), family(), build_query!(ancestor("alice", _))); assert_parity(&n, &s, "p4 bf"); assert_eq!(n.len(), 6); }
#[test] fn p4_ff() { let (n, s) = run_naive_sdt(ancestor_prog(), family(), build_query!(ancestor(_, _))); assert_parity(&n, &s, "p4 ff"); assert_eq!(n.len(), 15); }

// P5: Nonrecursive 2-hop (all 4 patterns)
#[test] fn p5_bf() { let (n, s) = run_naive_sdt(two_hop(), chain(), build_query!(hop2("a", _))); assert_parity(&n, &s, "p5 bf"); assert_eq!(n.len(), 2); }
#[test] fn p5_fb() { let (n, s) = run_naive_sdt(two_hop(), chain(), build_query!(hop2(_, "e"))); assert_parity(&n, &s, "p5 fb"); assert_eq!(n.len(), 2); }
#[test] fn p5_bb() { let (n, s) = run_naive_sdt(two_hop(), chain(), build_query!(hop2("a", "c"))); assert_parity(&n, &s, "p5 bb"); assert_eq!(n.len(), 1); }
#[test] fn p5_bb_neg() { let (n, s) = run_naive_sdt(two_hop(), chain(), build_query!(hop2("a", "e"))); assert_parity(&n, &s, "p5 bb-"); assert_eq!(n.len(), 0); }
#[test] fn p5_ff() { let (n, s) = run_naive_sdt(two_hop(), chain(), build_query!(hop2(_, _))); assert_parity(&n, &s, "p5 ff"); assert_eq!(n.len(), 5); }
