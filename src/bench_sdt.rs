/// Benchmarks from Tekle & Liu 2011 comparing MST vs SDT (subsumptive demand
/// transformation) on the paper's programs, using both SPJ and Free Join backends.
///
/// Run with: cargo test --release bench_sdt -- --nocapture
use std::time::Instant;
use std::collections::HashSet;

use crate::engine::datalog::MicroRuntime;
use datalog_syntax::*;

/// Generate a chain graph: 0->1->2->...->n-1
fn chain(n: usize) -> Vec<(&'static str, (usize, usize))> {
    (0..n-1).map(|i| ("e", (i, i + 1))).collect()
}

/// Generate a cycle: 0->1->...->n-1->0
fn cycle(n: usize) -> Vec<(&'static str, (usize, usize))> {
    (0..n).map(|i| ("e", (i, (i + 1) % n))).collect()
}

/// Generate a dense graph (deterministic pseudo-random)
fn dense(n: usize, edges: usize) -> Vec<(&'static str, (usize, usize))> {
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    for i in 0..edges * 2 {
        let src = (i * 13 + 7) % n;
        let dst = (i * 31 + 11) % n;
        if src != dst && seen.insert((src, dst)) {
            result.push(("e", (src, dst)));
        }
        if result.len() >= edges { break; }
    }
    result
}

/// Paper's running example: rel(x,y) :- imm(x,y). rel(x,y) :- imm(u,v), rel(u,x), rel(v,y).
/// Generate imm facts as a chain
fn imm_chain(n: usize) -> Vec<(&'static str, (usize, usize))> {
    (0..n-1).map(|i| ("imm", (i, i + 1))).collect()
}

struct BenchResult {
    name: String,
    median_us: u128,
    result_count: usize,
}

fn bench_strategy(
    label: &str,
    make_runtime: fn(Program) -> MicroRuntime,
    program: &Program,
    facts: &[(&str, (usize, usize))],
    query: &Query,
    strategy: &str,
    iterations: usize,
) -> BenchResult {
    let mut times = Vec::new();
    let mut count = 0;

    for _ in 0..iterations {
        let mut rt = make_runtime(program.clone());
        for &(rel, (a, b)) in facts {
            rt.insert(rel, (a, b));
        }

        let start = Instant::now();
        let results: Vec<_> = rt.query_program(query, program.clone(), strategy)
            .unwrap()
            .collect();
        let elapsed = start.elapsed();

        count = results.len();
        times.push(elapsed.as_micros());
    }

    times.sort();
    BenchResult {
        name: label.to_string(),
        median_us: times[times.len() / 2],
        result_count: count,
    }
}

fn bench_naive(
    label: &str,
    make_runtime: fn(Program) -> MicroRuntime,
    program: &Program,
    facts: &[(&str, (usize, usize))],
    query: &Query,
    iterations: usize,
) -> BenchResult {
    let mut times = Vec::new();
    let mut count = 0;

    for _ in 0..iterations {
        let mut rt = make_runtime(program.clone());
        for &(rel, (a, b)) in facts {
            rt.insert(rel, (a, b));
        }

        let start = Instant::now();
        rt.poll();
        let results: Vec<_> = rt.query(query).unwrap().collect();
        let elapsed = start.elapsed();

        count = results.len();
        times.push(elapsed.as_micros());
    }

    times.sort();
    BenchResult {
        name: label.to_string(),
        median_us: times[times.len() / 2],
        result_count: count,
    }
}

fn print_results(header: &str, results: &[BenchResult]) {
    eprintln!("\n{}", header);
    eprintln!("{:-<90}", "");
    for r in results {
        eprintln!("  {:<45} {:>8}µs  ({} results)", r.name, r.median_us, r.result_count);
    }
}

#[cfg(test)]
mod bench_sdt {
    use super::*;
    use datalog_rule_macro::program;

    // ====================================================================
    // Benchmark 1: Linear TC with BF query (paper's basic case)
    // Compare: Naive, MST, SDT on SPJ and FreeJoin backends
    // ====================================================================

        #[test]
    #[ignore]
    fn bench_sdt_linear_tc_bf() {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let query = build_query!(tc(0, _));
        let iters = 10;

        for (size_label, facts) in [
            ("chain(50)", chain(50)),
            ("chain(100)", chain(100)),
            ("cycle(30)", cycle(30)),
            ("dense(30,100)", dense(30, 100)),
        ] {
            let mut results = Vec::new();

            // SPJ backend
            results.push(bench_naive("Naive+SPJ", MicroRuntime::new, &prog, &facts, &query, iters));
            results.push(bench_strategy("MST+SPJ", MicroRuntime::new, &prog, &facts, &query, "Bottom-up", iters));
            results.push(bench_strategy("SDT+SPJ", MicroRuntime::new, &prog, &facts, &query, "SDT", iters));

            // Free Join backend
            results.push(bench_naive("Naive+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, iters));
            results.push(bench_strategy("MST+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, "Bottom-up", iters));
            results.push(bench_strategy("SDT+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, "SDT", iters));

            // Verify correctness: all should produce same count
            let counts: HashSet<_> = results.iter().map(|r| r.result_count).collect();
            assert!(counts.len() == 1, "Result count mismatch in {}: {:?}",
                size_label, results.iter().map(|r| (r.name.as_str(), r.result_count)).collect::<Vec<_>>());

            print_results(&format!("Linear TC BF query, {}", size_label), &results);
        }
    }

    // ====================================================================
    // Benchmark 2: Linear TC with FF query (full materialization)
    // SDT should have minimal advantage here (no demand restriction)
    // ====================================================================

        #[test]
    #[ignore]
    fn bench_sdt_linear_tc_ff() {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let query = build_query!(tc(_, _));
        let iters = 5;

        for (size_label, facts) in [
            ("chain(50)", chain(50)),
            ("cycle(20)", cycle(20)),
        ] {
            let mut results = Vec::new();
            results.push(bench_naive("Naive+SPJ", MicroRuntime::new, &prog, &facts, &query, iters));
            results.push(bench_strategy("MST+SPJ", MicroRuntime::new, &prog, &facts, &query, "Bottom-up", iters));
            results.push(bench_strategy("SDT+SPJ", MicroRuntime::new, &prog, &facts, &query, "SDT", iters));
            results.push(bench_naive("Naive+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, iters));
            results.push(bench_strategy("MST+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, "Bottom-up", iters));
            results.push(bench_strategy("SDT+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, "SDT", iters));

            let counts: HashSet<_> = results.iter().map(|r| r.result_count).collect();
            assert!(counts.len() == 1, "Result count mismatch in {}", size_label);

            print_results(&format!("Linear TC FF query, {}", size_label), &results);
        }
    }

    // ====================================================================
    // Benchmark 3: Paper's running example (rel with imm)
    // This is where SDT should shine — bf subsumes bb
    // ====================================================================

        #[test]
    #[ignore]
    fn bench_sdt_paper_running_example() {
        let prog = program! {
            rel(?x, ?y) <- [imm(?x, ?y)],
            rel(?x, ?y) <- [imm(?u, ?v), rel(?u, ?x), rel(?v, ?y)]
        };
        let iters = 10;

        for (size_label, facts) in [
            ("imm_chain(20)", imm_chain(20)),
            ("imm_chain(40)", imm_chain(40)),
            ("imm_chain(60)", imm_chain(60)),
        ] {
            let query_bf = Query {
                symbol: "rel",
                matchers: vec![Matcher::Constant(TypedValue::Int(0)), Matcher::Any],
            };

            let mut results = Vec::new();
            results.push(bench_naive("Naive+SPJ", MicroRuntime::new, &prog, &facts, &query_bf, iters));
            results.push(bench_strategy("MST+SPJ", MicroRuntime::new, &prog, &facts, &query_bf, "Bottom-up", iters));
            results.push(bench_strategy("SDT+SPJ", MicroRuntime::new, &prog, &facts, &query_bf, "SDT", iters));
            results.push(bench_naive("Naive+FJ", MicroRuntime::new_free_join, &prog, &facts, &query_bf, iters));
            results.push(bench_strategy("MST+FJ", MicroRuntime::new_free_join, &prog, &facts, &query_bf, "Bottom-up", iters));
            results.push(bench_strategy("SDT+FJ", MicroRuntime::new_free_join, &prog, &facts, &query_bf, "SDT", iters));

            let counts: HashSet<_> = results.iter().map(|r| r.result_count).collect();
            assert!(counts.len() == 1, "Result count mismatch in {}: {:?}",
                size_label, results.iter().map(|r| (r.name.as_str(), r.result_count)).collect::<Vec<_>>());

            print_results(&format!("Paper running example BF, {}", size_label), &results);
        }
    }

        #[test]
    #[ignore]
    fn bench_sdt_ancestor_bb() {
        let prog = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };
        let iters = 10;

        for n in [20, 50, 100] {
            let facts: Vec<_> = (0..n-1).map(|i| ("parent", (i, i + 1))).collect();
            let query = Query {
                symbol: "ancestor",
                matchers: vec![
                    Matcher::Constant(TypedValue::Int(0)),
                    Matcher::Constant(TypedValue::Int(n - 1)),
                ],
            };

            let mut results = Vec::new();
            results.push(bench_naive("Naive+SPJ", MicroRuntime::new, &prog, &facts, &query, iters));
            results.push(bench_naive("Naive+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, iters));
            results.push(bench_strategy("MST+SPJ", MicroRuntime::new, &prog, &facts, &query, "Bottom-up", iters));
            results.push(bench_strategy("MST+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, "Bottom-up", iters));
            results.push(bench_strategy("SDT+SPJ", MicroRuntime::new, &prog, &facts, &query, "SDT", iters));
            results.push(bench_strategy("SDT+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, "SDT", iters));

            let counts: HashSet<_> = results.iter().map(|r| r.result_count).collect();
            assert!(counts.len() == 1, "Result count mismatch for ancestor bb n={}: {:?}",
                n, results.iter().map(|r| (r.name.as_str(), r.result_count)).collect::<Vec<_>>());

            print_results(&format!("Ancestor BB (0->{}), chain({})", n-1, n), &results);
        }
    }

        #[test]
    #[ignore]
    fn bench_sdt_linear_tc_fb() {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let iters = 10;

        for (size_label, facts) in [
            ("cycle(30)", cycle(30)),
            ("cycle(50)", cycle(50)),
        ] {
            let query = Query {
                symbol: "tc",
                matchers: vec![Matcher::Any, Matcher::Constant(TypedValue::Int(0))],
            };

            let mut results = Vec::new();
            results.push(bench_naive("Naive+SPJ", MicroRuntime::new, &prog, &facts, &query, iters));
            results.push(bench_naive("Naive+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, iters));
            results.push(bench_strategy("MST+SPJ", MicroRuntime::new, &prog, &facts, &query, "Bottom-up", iters));
            results.push(bench_strategy("MST+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, "Bottom-up", iters));
            results.push(bench_strategy("SDT+SPJ", MicroRuntime::new, &prog, &facts, &query, "SDT", iters));
            results.push(bench_strategy("SDT+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, "SDT", iters));

            let counts: HashSet<_> = results.iter().map(|r| r.result_count).collect();
            assert!(counts.len() == 1, "Result count mismatch in {}: {:?}",
                size_label, results.iter().map(|r| (r.name.as_str(), r.result_count)).collect::<Vec<_>>());

            print_results(&format!("Linear TC FB query, {}", size_label), &results);
        }
    }

    // ====================================================================
    // Benchmark 5: Same-generation BF query
    // ====================================================================

        #[test]
    #[ignore]
    fn bench_sdt_same_generation() {
        let prog = program! {
            sg(?x, ?y) <- [flat(?x, ?y)],
            sg(?y, ?x) <- [sg(?x, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
        };
        let iters = 10;

        // Build a tree with `levels` levels, branching factor 2
        for levels in [3, 4] {
            let mut facts: Vec<(&str, (usize, usize))> = Vec::new();
            let mut node_id = 0;
            let mut level_nodes: Vec<Vec<usize>> = Vec::new();

            // Build tree
            level_nodes.push(vec![node_id]); // root
            node_id += 1;

            for _l in 1..levels {
                let mut next_level = Vec::new();
                for &parent in level_nodes.last().unwrap() {
                    for _ in 0..2 {
                        facts.push(("up", (node_id, parent)));
                        facts.push(("down", (parent, node_id)));
                        next_level.push(node_id);
                        node_id += 1;
                    }
                }
                level_nodes.push(next_level);
            }

            // flat connects roots (just self for single root)
            facts.push(("flat", (0, 0)));

            // Query: same-gen of a leaf node
            let leaf = *level_nodes.last().unwrap().first().unwrap();
            let query = Query {
                symbol: "sg",
                matchers: vec![Matcher::Constant(TypedValue::Int(leaf)), Matcher::Any],
            };

            let mut results = Vec::new();
            results.push(bench_naive("Naive+SPJ", MicroRuntime::new, &prog, &facts, &query, iters));
            results.push(bench_strategy("MST+SPJ", MicroRuntime::new, &prog, &facts, &query, "Bottom-up", iters));
            results.push(bench_strategy("SDT+SPJ", MicroRuntime::new, &prog, &facts, &query, "SDT", iters));
            results.push(bench_naive("Naive+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, iters));
            results.push(bench_strategy("MST+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, "Bottom-up", iters));
            results.push(bench_strategy("SDT+FJ", MicroRuntime::new_free_join, &prog, &facts, &query, "SDT", iters));

            let counts: HashSet<_> = results.iter().map(|r| r.result_count).collect();
            assert!(counts.len() == 1, "Result count mismatch for sg levels={}: {:?}",
                levels, results.iter().map(|r| (r.name.as_str(), r.result_count)).collect::<Vec<_>>());

            print_results(&format!("Same-generation BF, {} levels ({} nodes)", levels, node_id), &results);
        }
    }
}
