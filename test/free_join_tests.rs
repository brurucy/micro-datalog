/// Free Join regression and parity tests.
///
/// These tests target the 4 known SPJ bugs that Free Join is designed to fix,
/// plus full parity coverage (5 programs x 4 patterns), edge cases, and SDT
/// integration.
///
/// The tests use a "FreeJoin" strategy via `query_program`. They will fail
/// until the Free Join evaluator is wired into `MicroRuntime::query_program`.
/// That is intentional -- the tests document the expected behavior.
use std::collections::HashSet;

use datalog_rule_macro::program;
use datalog_syntax::*;
use micro_datalog::{convert_fact, engine::datalog::MicroRuntime};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Run a query via pure semi-naive (poll + query) as ground truth, and via
/// Free Join (query_program with "FreeJoin" strategy). Returns (naive, fj).
fn run_naive_fj(
    program: Program,
    facts: Vec<(&str, Vec<&str>)>,
    query: Query,
) -> (HashSet<Vec<String>>, HashSet<Vec<String>>) {
    // Ground truth: pure semi-naive bottom-up
    let mut naive = MicroRuntime::new(program.clone());
    for (rel, fact) in &facts {
        naive.insert(rel, fact.clone());
    }
    naive.poll();
    let naive_r: HashSet<Vec<String>> = naive
        .query(&query)
        .unwrap()
        .map(|a| {
            a.into_iter()
                .map(|tv| match tv {
                    TypedValue::Str(s) => s,
                    TypedValue::Int(i) => i.to_string(),
                    TypedValue::Bool(b) => b.to_string(),
                })
                .collect()
        })
        .collect();

    // Free Join path
    let mut fj = MicroRuntime::new(program.clone());
    for (rel, fact) in &facts {
        fj.insert(rel, fact.clone());
    }
    let fj_r: HashSet<Vec<String>> = fj
        .query_program(&query, program, "FreeJoin")
        .unwrap()
        .map(|a| {
            a.into_iter()
                .map(|tv| match tv {
                    TypedValue::Str(s) => s,
                    TypedValue::Int(i) => i.to_string(),
                    TypedValue::Bool(b) => b.to_string(),
                })
                .collect()
        })
        .collect();

    (naive_r, fj_r)
}

/// Run query via SDT and via Free Join, returning (sdt, fj).
fn run_sdt_fj(
    program: Program,
    facts: Vec<(&str, Vec<&str>)>,
    query: Query,
) -> (HashSet<Vec<String>>, HashSet<Vec<String>>) {
    // SDT path
    let mut sdt = MicroRuntime::new(program.clone());
    for (rel, fact) in &facts {
        sdt.insert(rel, fact.clone());
    }
    let sdt_r: HashSet<Vec<String>> = sdt
        .query_program(&query, program.clone(), "SDT")
        .unwrap()
        .map(|a| {
            a.into_iter()
                .map(|tv| match tv {
                    TypedValue::Str(s) => s,
                    TypedValue::Int(i) => i.to_string(),
                    TypedValue::Bool(b) => b.to_string(),
                })
                .collect()
        })
        .collect();

    // Free Join path
    let mut fj = MicroRuntime::new(program.clone());
    for (rel, fact) in &facts {
        fj.insert(rel, fact.clone());
    }
    let fj_r: HashSet<Vec<String>> = fj
        .query_program(&query, program, "FreeJoin")
        .unwrap()
        .map(|a| {
            a.into_iter()
                .map(|tv| match tv {
                    TypedValue::Str(s) => s,
                    TypedValue::Int(i) => i.to_string(),
                    TypedValue::Bool(b) => b.to_string(),
                })
                .collect()
        })
        .collect();

    (sdt_r, fj_r)
}

fn assert_parity(left: &HashSet<Vec<String>>, right: &HashSet<Vec<String>>, label: &str) {
    assert_eq!(left, right, "{}: result sets diverge", label);
}

// ---------------------------------------------------------------------------
// Data sets (reused across tests)
// ---------------------------------------------------------------------------

/// 6-node cyclic graph with shortcut edges.
fn cyclic_graph() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("e", vec!["a", "b"]),
        ("e", vec!["b", "c"]),
        ("e", vec!["c", "d"]),
        ("e", vec!["d", "e"]),
        ("e", vec!["e", "f"]),
        ("e", vec!["f", "a"]),
        ("e", vec!["a", "d"]),
        ("e", vec!["c", "f"]),
        ("e", vec!["b", "e"]),
    ]
}

/// Simple chain a->b->c->d->e->f with NO shortcut edges.
fn chain6() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("e", vec!["a", "b"]),
        ("e", vec!["b", "c"]),
        ("e", vec!["c", "d"]),
        ("e", vec!["d", "e"]),
        ("e", vec!["e", "f"]),
    ]
}

/// 4-generation family tree.
/// alice, bob -> carol, dave, eve
/// carol, dave, eve -> frank, grace, henry
/// frank, grace -> ivy, jack
fn family() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("parent", vec!["alice", "carol"]),
        ("parent", vec!["alice", "dave"]),
        ("parent", vec!["bob", "eve"]),
        ("parent", vec!["carol", "frank"]),
        ("parent", vec!["dave", "grace"]),
        ("parent", vec!["eve", "henry"]),
        ("parent", vec!["frank", "ivy"]),
        ("parent", vec!["grace", "jack"]),
    ]
}

/// Same-generation tree: two roots (r1, r2) connected by flat;
/// each root has two mid-level children (m1-m4), each mid has two leaves (l1-l8).
fn sg_tree() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("flat", vec!["r1", "r2"]),
        ("up", vec!["m1", "r1"]),
        ("up", vec!["m2", "r1"]),
        ("up", vec!["m3", "r2"]),
        ("up", vec!["m4", "r2"]),
        ("down", vec!["r1", "m1"]),
        ("down", vec!["r1", "m2"]),
        ("down", vec!["r2", "m3"]),
        ("down", vec!["r2", "m4"]),
        ("up", vec!["l1", "m1"]),
        ("up", vec!["l2", "m1"]),
        ("up", vec!["l3", "m2"]),
        ("up", vec!["l4", "m2"]),
        ("up", vec!["l5", "m3"]),
        ("up", vec!["l6", "m3"]),
        ("up", vec!["l7", "m4"]),
        ("up", vec!["l8", "m4"]),
        ("down", vec!["m1", "l1"]),
        ("down", vec!["m1", "l2"]),
        ("down", vec!["m2", "l3"]),
        ("down", vec!["m2", "l4"]),
        ("down", vec!["m3", "l5"]),
        ("down", vec!["m3", "l6"]),
        ("down", vec!["m4", "l7"]),
        ("down", vec!["m4", "l8"]),
        ("flat", vec!["m1", "m2"]),
        ("flat", vec!["m3", "m4"]),
    ]
}

/// Small chain with a shortcut (for 2-hop tests).
fn chain() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("e", vec!["a", "b"]),
        ("e", vec!["b", "c"]),
        ("e", vec!["c", "d"]),
        ("e", vec!["d", "e"]),
        ("e", vec!["b", "d"]),
    ]
}

// ---------------------------------------------------------------------------
// Programs
// ---------------------------------------------------------------------------

fn linear_tc() -> Program {
    program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
    }
}

fn left_linear_tc() -> Program {
    program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [tc(?x, ?y), e(?y, ?z)]
    }
}

fn same_gen() -> Program {
    program! {
        sg(?x, ?y) <- [flat(?x, ?y)],
        sg(?y, ?x) <- [sg(?x, ?y)],
        sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
        sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
    }
}

fn ancestor_prog() -> Program {
    program! {
        ancestor(?x, ?y) <- [parent(?x, ?y)],
        ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
    }
}

fn two_hop() -> Program {
    program! {
        hop2(?x, ?z) <- [e(?x, ?y), e(?y, ?z)]
    }
}

// =========================================================================
// A. Bug regression tests (the 4 known bugs)
// =========================================================================

/// Bug 1 (fb on recursive): magic predicate shares no vars with first EDB atom,
/// causing a cross product that breaks join_key_positions.
///
/// tc(_, "a") on a cyclic graph must return all 6 nodes that can reach "a".
/// The SPJ compiler returns only 1 (f->a via direct edge); Free Join must
/// return 6 because every node reaches "a" in a cycle.
#[test]
fn test_fb_linear_tc() {
    let (naive, fj) = run_naive_fj(linear_tc(), cyclic_graph(), build_query!(tc(_, "a")));
    assert_parity(&naive, &fj, "Bug1: fb linear tc");
    // In a 6-node cycle with shortcuts, every node can reach every other node.
    // tc(_, "a") should return 6 results (one per source node).
    assert_eq!(
        naive.len(),
        6,
        "Bug1: expected 6 sources reaching 'a' in cyclic graph, got {}",
        naive.len()
    );
}

/// Bug 1 variant: fb query on ancestor.
///
/// ancestor(_, "ivy") on the family tree. ivy is 4 generations deep:
///   frank -> ivy, carol -> frank -> ivy, alice -> carol -> frank -> ivy.
/// So ancestors of ivy are: frank, carol, alice (3 ancestors).
#[test]
fn test_fb_ancestor() {
    let (naive, fj) = run_naive_fj(ancestor_prog(), family(), build_query!(ancestor(_, "ivy")));
    assert_parity(&naive, &fj, "Bug1: fb ancestor");
    assert_eq!(
        naive.len(),
        3,
        "Bug1: expected 3 ancestors of 'ivy' (frank, carol, alice), got {}",
        naive.len()
    );
}

/// Bug 1 variant: fb query on same-generation.
///
/// sg(_, "l1") should return all nodes in the same generation as l1.
/// l1 is a leaf under m1 under r1. Same-generation leaves under r1 are
/// l1, l2 (under m1), l3, l4 (under m2). Via flat(r1, r2), also l5-l8.
/// Total: 8 same-gen nodes (including l1 itself via reflexive path).
#[test]
fn test_fb_same_generation() {
    let (naive, fj) = run_naive_fj(same_gen(), sg_tree(), build_query!(sg(_, "l1")));
    assert_parity(&naive, &fj, "Bug1: fb same-generation");
    // l1 is same-gen with all 8 leaves (l1..l8), so sg(_, "l1") returns 8.
    assert!(
        naive.len() >= 8,
        "Bug1: expected at least 8 nodes in sg(_, 'l1'), got {}",
        naive.len()
    );
}

/// Bug 2 (bb on multi-hop): binary delta decomposition drops intermediate
/// results when only the 3rd relation has deltas.
///
/// ancestor("alice", "ivy") requires 3 hops: alice->carol->frank->ivy.
/// SPJ returns 0 because the binary join chain loses old intermediates.
/// Free Join must return 1.
#[test]
fn test_bb_multi_hop_ancestor() {
    let (naive, fj) = run_naive_fj(
        ancestor_prog(),
        family(),
        build_query!(ancestor("alice", "ivy")),
    );
    assert_parity(&naive, &fj, "Bug2: bb multi-hop ancestor");
    assert_eq!(
        naive.len(),
        1,
        "Bug2: expected 1 result for ancestor('alice','ivy'), got {}",
        naive.len()
    );
}

/// Bug 2 variant: bb on a pure chain with no shortcut edges.
///
/// tc("a", "f") on chain a->b->c->d->e->f (5 hops). Must return 1.
/// With the SPJ bug, multi-hop bb queries fail because the binary delta
/// decomposition drops old intermediates beyond the first join.
#[test]
fn test_bb_multi_hop_tc() {
    let (naive, fj) = run_naive_fj(linear_tc(), chain6(), build_query!(tc("a", "f")));
    assert_parity(&naive, &fj, "Bug2: bb multi-hop tc on chain");
    assert_eq!(
        naive.len(),
        1,
        "Bug2: expected 1 result for tc('a','f') on chain, got {}",
        naive.len()
    );
}

/// Bug 4 (left-deep delta tracking): 3-atom recursive rule where new facts
/// arrive only in the 3rd relation.
///
/// The same-generation program has a 3-atom recursive rule:
///   sg(X,Y) <- up(X,Z1), sg(Z1,Z2), down(Z2,Y).
/// When sg has new deltas but up and down do not, the left-deep SPJ
/// evaluator misses the case delta_sg paired with old_up and old_down.
///
/// We test this by querying sg(_, _) (ff) and verifying the full closure.
/// The full closure requires multiple iterations where only sg has deltas.
#[test]
fn test_three_atom_rule_delta() {
    let (naive, fj) = run_naive_fj(same_gen(), sg_tree(), build_query!(sg(_, _)));
    assert_parity(&naive, &fj, "Bug4: 3-atom rule delta tracking");
    // The full same-generation closure must include cross-subtree pairs.
    // With correct delta tracking for the 3-atom rule, the transitive
    // closure through sg(Z1,Z2) propagates across the flat edge.
    assert!(
        naive.len() > 20,
        "Bug4: expected >20 sg pairs from full closure, got {}",
        naive.len()
    );
}

/// Bug 1 + Bug 3: fb query where the magic predicate shares no variables
/// with the first EDB atom, forcing a cross product in SPJ.
///
/// For ancestor(_, "ivy"), the magic-transformed program produces:
///   magic_fb(Y), parent(X, P), ancestor_fb(P, Y)
/// where magic_fb and parent share no variables. This is the cross-product
/// scenario that exposes both Bug 1 (cross product) and Bug 3 (empty
/// join_key_positions when inner/diff are empty).
#[test]
fn test_cross_product_in_demand_rule() {
    // This is the same as test_fb_ancestor but we name it explicitly
    // to document the cross-product bug.
    let (naive, fj) = run_naive_fj(ancestor_prog(), family(), build_query!(ancestor(_, "ivy")));
    assert_parity(&naive, &fj, "Bug1+3: cross-product in demand rule");
    assert_eq!(naive.len(), 3);
}

// =========================================================================
// B. Full parity matrix: 5 programs x 4 patterns (20 tests)
// =========================================================================

// --- P1: Linear TC ---

#[test]
fn parity_linear_tc_bf() {
    let (n, fj) = run_naive_fj(linear_tc(), cyclic_graph(), build_query!(tc("a", _)));
    assert_parity(&n, &fj, "P1 bf");
    assert_eq!(n.len(), 6);
}

#[test]
fn parity_linear_tc_fb() {
    let (n, fj) = run_naive_fj(linear_tc(), cyclic_graph(), build_query!(tc(_, "a")));
    assert_parity(&n, &fj, "P1 fb");
    assert_eq!(n.len(), 6);
}

#[test]
fn parity_linear_tc_bb() {
    let (n, fj) = run_naive_fj(linear_tc(), cyclic_graph(), build_query!(tc("a", "d")));
    assert_parity(&n, &fj, "P1 bb");
    assert_eq!(n.len(), 1);
}

#[test]
fn parity_linear_tc_ff() {
    let (n, fj) = run_naive_fj(linear_tc(), cyclic_graph(), build_query!(tc(_, _)));
    assert_parity(&n, &fj, "P1 ff");
    assert_eq!(n.len(), 36);
}

// --- P2: Left-linear TC ---

#[test]
fn parity_left_linear_tc_bf() {
    let (n, fj) = run_naive_fj(left_linear_tc(), cyclic_graph(), build_query!(tc("a", _)));
    assert_parity(&n, &fj, "P2 bf");
    assert_eq!(n.len(), 6);
}

#[test]
fn parity_left_linear_tc_fb() {
    let (n, fj) = run_naive_fj(left_linear_tc(), cyclic_graph(), build_query!(tc(_, "a")));
    assert_parity(&n, &fj, "P2 fb");
    assert_eq!(n.len(), 6);
}

#[test]
fn parity_left_linear_tc_bb() {
    let (n, fj) = run_naive_fj(left_linear_tc(), cyclic_graph(), build_query!(tc("a", "d")));
    assert_parity(&n, &fj, "P2 bb");
    assert_eq!(n.len(), 1);
}

#[test]
fn parity_left_linear_tc_ff() {
    let (n, fj) = run_naive_fj(left_linear_tc(), cyclic_graph(), build_query!(tc(_, _)));
    assert_parity(&n, &fj, "P2 ff");
    assert_eq!(n.len(), 36);
}

// --- P3: Same-generation ---

#[test]
fn parity_same_gen_bf() {
    let (n, fj) = run_naive_fj(same_gen(), sg_tree(), build_query!(sg("l1", _)));
    assert_parity(&n, &fj, "P3 bf");
    assert!(n.len() >= 8);
}

#[test]
fn parity_same_gen_fb() {
    let (n, fj) = run_naive_fj(same_gen(), sg_tree(), build_query!(sg(_, "l1")));
    assert_parity(&n, &fj, "P3 fb");
    assert!(n.len() >= 8);
}

#[test]
fn parity_same_gen_bb() {
    let (n, fj) = run_naive_fj(same_gen(), sg_tree(), build_query!(sg("l1", "l5")));
    assert_parity(&n, &fj, "P3 bb");
    assert_eq!(n.len(), 1);
}

#[test]
fn parity_same_gen_ff() {
    let (n, fj) = run_naive_fj(same_gen(), sg_tree(), build_query!(sg(_, _)));
    assert_parity(&n, &fj, "P3 ff");
    assert!(n.len() > 20);
}

// --- P4: Ancestor ---

#[test]
fn parity_ancestor_bf() {
    let (n, fj) = run_naive_fj(ancestor_prog(), family(), build_query!(ancestor("alice", _)));
    assert_parity(&n, &fj, "P4 bf");
    assert_eq!(n.len(), 6);
}

#[test]
fn parity_ancestor_fb() {
    let (n, fj) = run_naive_fj(ancestor_prog(), family(), build_query!(ancestor(_, "ivy")));
    assert_parity(&n, &fj, "P4 fb");
    assert_eq!(n.len(), 3);
}

#[test]
fn parity_ancestor_bb() {
    let (n, fj) = run_naive_fj(
        ancestor_prog(),
        family(),
        build_query!(ancestor("alice", "ivy")),
    );
    assert_parity(&n, &fj, "P4 bb");
    assert_eq!(n.len(), 1);
}

#[test]
fn parity_ancestor_ff() {
    let (n, fj) = run_naive_fj(ancestor_prog(), family(), build_query!(ancestor(_, _)));
    assert_parity(&n, &fj, "P4 ff");
    assert_eq!(n.len(), 15);
}

// --- P5: Nonrecursive 2-hop ---

#[test]
fn parity_two_hop_bf() {
    let (n, fj) = run_naive_fj(two_hop(), chain(), build_query!(hop2("a", _)));
    assert_parity(&n, &fj, "P5 bf");
    assert_eq!(n.len(), 2);
}

#[test]
fn parity_two_hop_fb() {
    let (n, fj) = run_naive_fj(two_hop(), chain(), build_query!(hop2(_, "e")));
    assert_parity(&n, &fj, "P5 fb");
    assert_eq!(n.len(), 2);
}

#[test]
fn parity_two_hop_bb() {
    let (n, fj) = run_naive_fj(two_hop(), chain(), build_query!(hop2("a", "c")));
    assert_parity(&n, &fj, "P5 bb");
    assert_eq!(n.len(), 1);
}

#[test]
fn parity_two_hop_ff() {
    let (n, fj) = run_naive_fj(two_hop(), chain(), build_query!(hop2(_, _)));
    assert_parity(&n, &fj, "P5 ff");
    assert_eq!(n.len(), 5);
}

// =========================================================================
// C. Edge cases
// =========================================================================

/// Edge case 1: Empty program (no rules, no facts). Queries return nothing.
#[test]
fn edge_empty_program() {
    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)]
    };
    let facts: Vec<(&str, Vec<&str>)> = vec![];
    let (n, fj) = run_naive_fj(program, facts, build_query!(tc(_, _)));
    assert_parity(&n, &fj, "edge: empty program");
    assert_eq!(n.len(), 0);
}

/// Edge case 2: Single fact, point query (bb).
#[test]
fn edge_single_fact_bb() {
    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
    };
    let facts = vec![("e", vec!["a", "b"])];
    let (n, fj) = run_naive_fj(program, facts, build_query!(tc("a", "b")));
    assert_parity(&n, &fj, "edge: single fact bb");
    assert_eq!(n.len(), 1);
}

/// Edge case 3: Cyclic graph full closure (ff). Every node reaches every node.
#[test]
fn edge_cyclic_full_closure() {
    let (n, fj) = run_naive_fj(linear_tc(), cyclic_graph(), build_query!(tc(_, _)));
    assert_parity(&n, &fj, "edge: cyclic full closure");
    // 6 nodes, each reaches all 6 (including itself via the cycle).
    assert_eq!(n.len(), 36);
}

/// Edge case 4: Rule with constants in the body.
/// Only derive tc edges from "a".
#[test]
fn edge_rule_with_constants() {
    let program = program! {
        from_a(?y) <- [e("a", ?y)],
        from_a(?z) <- [e("a", ?y), from_a(?z)]
    };
    // Note: the second rule is intentionally odd -- it derives from_a(Z)
    // for any Z already in from_a, as long as "a" has *some* edge. This
    // tests constant handling in the body. The key test is that the constant
    // "a" in e("a", ?y) is handled correctly by Free Join.
    let facts = vec![
        ("e", vec!["a", "b"]),
        ("e", vec!["b", "c"]),
        ("e", vec!["a", "d"]),
    ];
    let (n, fj) = run_naive_fj(program, facts, build_query!(from_a(_)));
    assert_parity(&n, &fj, "edge: constants in body");
    // from_a should contain "b" and "d" (direct edges from "a").
    // The second rule re-derives existing from_a facts, adding nothing new.
    assert_eq!(n.len(), 2);
}

/// Edge case 5: Rule with a negated atom (antijoin).
///
/// Derive reachable nodes that are NOT directly connected.
/// indirect(X,Z) <- tc(X,Z), !e(X,Z)
#[test]
fn edge_negated_atom_antijoin() {
    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        indirect(?x, ?z) <- [tc(?x, ?z), !e(?x, ?z)]
    };
    let facts = vec![
        ("e", vec!["a", "b"]),
        ("e", vec!["b", "c"]),
        ("e", vec!["c", "d"]),
    ];
    let (n, fj) = run_naive_fj(program, facts, build_query!(indirect(_, _)));
    assert_parity(&n, &fj, "edge: antijoin");
    // tc = {(a,b),(b,c),(c,d),(a,c),(b,d),(a,d)}
    // e  = {(a,b),(b,c),(c,d)}
    // indirect = tc - e = {(a,c),(b,d),(a,d)}
    assert_eq!(n.len(), 3);
}

/// Edge case 6: Self-join / nonlinear TC.
/// tc(X,Z) <- tc(X,Y), tc(Y,Z).
/// This is a self-join on tc. Combined with the base case tc(X,Y) <- e(X,Y),
/// this computes the full transitive closure using nonlinear recursion.
#[test]
fn edge_self_join_nonlinear_tc() {
    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
    };
    let facts = vec![
        ("e", vec!["a", "b"]),
        ("e", vec!["b", "c"]),
        ("e", vec!["c", "d"]),
    ];
    let (n, fj) = run_naive_fj(program, facts, build_query!(tc(_, _)));
    assert_parity(&n, &fj, "edge: self-join nonlinear tc");
    // Full closure: {(a,b),(b,c),(c,d),(a,c),(b,d),(a,d)}
    assert_eq!(n.len(), 6);
}

// =========================================================================
// D. SDT integration
// =========================================================================

/// SDT bf query produces same results as Free Join.
#[test]
fn sdt_bf_parity_with_fj() {
    let (sdt, fj) = run_sdt_fj(
        ancestor_prog(),
        family(),
        build_query!(ancestor("alice", _)),
    );
    assert_parity(&sdt, &fj, "SDT bf vs FreeJoin");
    assert_eq!(sdt.len(), 6);
}

/// SDT ff query produces same results as Free Join.
#[test]
fn sdt_ff_parity_with_fj() {
    let (sdt, fj) = run_sdt_fj(ancestor_prog(), family(), build_query!(ancestor(_, _)));
    assert_parity(&sdt, &fj, "SDT ff vs FreeJoin");
    assert_eq!(sdt.len(), 15);
}

/// SDT with negated demand hypotheses produces correct results via Free Join.
///
/// The SDT transformation adds negated hypotheses to demand rules for
/// subsumption suppression. Free Join must handle these antijoins correctly.
/// We test via a bf query on linear TC (the SDT transformation produces
/// demand rules with negated hypotheses for the bf adornment).
#[test]
fn sdt_negated_demand_hypotheses() {
    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
    };
    let facts = vec![
        ("e", vec!["a", "b"]),
        ("e", vec!["b", "c"]),
        ("e", vec!["c", "d"]),
        ("e", vec!["d", "e"]),
    ];
    let (sdt, fj) = run_sdt_fj(program, facts, build_query!(tc("a", _)));
    assert_parity(&sdt, &fj, "SDT negated demand vs FreeJoin");
    assert_eq!(sdt.len(), 4); // a->b, a->c, a->d, a->e
}
