/// Generic evaluation engine trait.
///
/// Allows different join implementations (SPJ, Free Join) to be swapped
/// and tested against each other for correctness on any Datalog program.
use crate::engine::storage::RelationStorage;
use datalog_syntax::Program;

pub trait EvaluationEngine {
    /// Evaluate a Datalog program to fixpoint.
    fn evaluate(
        &self,
        relation_storage: &mut RelationStorage,
        nonrecursive_program: &Program,
        recursive_program: &Program,
    );

    /// Human-readable name for this engine.
    fn name(&self) -> &'static str;
}

/// The original SPJ-based semi-naive evaluation engine.
pub struct SpjEngine;

impl EvaluationEngine for SpjEngine {
    fn evaluate(
        &self,
        relation_storage: &mut RelationStorage,
        nonrecursive_program: &Program,
        recursive_program: &Program,
    ) {
        crate::evaluation::semi_naive::semi_naive_evaluation(
            relation_storage,
            nonrecursive_program,
            recursive_program,
        );
    }

    fn name(&self) -> &'static str {
        "SPJ"
    }
}

/// Agent 4's Free Join evaluation engine.
pub struct FreeJoinEngine;

impl EvaluationEngine for FreeJoinEngine {
    fn evaluate(
        &self,
        relation_storage: &mut RelationStorage,
        nonrecursive_program: &Program,
        recursive_program: &Program,
    ) {
        crate::evaluation::free_join_semi_naive::free_join_evaluation(
            relation_storage,
            nonrecursive_program,
            recursive_program,
        );
    }

    fn name(&self) -> &'static str {
        "FreeJoin"
    }
}

/// All available engines.
#[cfg(test)]
pub fn all_engines() -> Vec<Box<dyn EvaluationEngine>> {
    vec![Box::new(SpjEngine), Box::new(FreeJoinEngine)]
}

// ============================================================================
// Generic test harness
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::helpers::helpers::split_program;
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use std::sync::Arc;

    fn register(storage: &mut RelationStorage, names: &[&str]) {
        for n in names {
            storage.inner.insert(n.to_string(), Default::default());
        }
    }

    fn insert_into(storage: &mut RelationStorage, rel: &str, facts: Vec<AnonymousGroundAtom>) {
        for f in facts {
            storage.inner.get_mut(rel).unwrap().insert(Arc::new(f));
        }
    }

    fn collect(storage: &RelationStorage, name: &str) -> std::collections::HashSet<AnonymousGroundAtom> {
        storage.get_relation(name).iter().map(|x| (**x).clone()).collect()
    }

    /// Run a program on all engines and assert they all produce the same results.
    fn assert_all_engines_agree(
        program: Program,
        relations: &[&str],
        facts: Vec<(&str, Vec<AnonymousGroundAtom>)>,
        check_relation: &str,
        label: &str,
    ) {
        let engines = all_engines();
        let mut results = Vec::new();

        for engine in &engines {
            let mut storage: RelationStorage = Default::default();
            register(&mut storage, relations);
            for (rel, data) in &facts {
                insert_into(&mut storage, rel, data.clone());
            }
            let (nr, r) = split_program(program.clone());
            engine.evaluate(&mut storage, &nr, &r);
            let result = collect(&storage, check_relation);
            results.push((engine.name(), result));
        }

        // All engines must agree with each other
        for i in 1..results.len() {
            assert_eq!(
                results[0].1, results[i].1,
                "{}: {} ({} facts) vs {} ({} facts) disagree",
                label, results[0].0, results[0].1.len(), results[i].0, results[i].1.len()
            );
        }
    }

    // ====================================================================
    // Linear TC
    // ====================================================================

    #[test]
    fn all_engines_linear_tc_chain() {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let facts = vec![("e", vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            vec!["d".into(), "e".into()],
        ])];
        assert_all_engines_agree(prog, &["e", "tc"], facts, "tc", "linear TC chain");
    }

    #[test]
    fn all_engines_linear_tc_cycle() {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let facts = vec![("e", vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "a".into()],
        ])];
        assert_all_engines_agree(prog, &["e", "tc"], facts, "tc", "linear TC cycle");
    }

    // ====================================================================
    // Left-linear TC
    // ====================================================================

    #[test]
    fn all_engines_left_linear_tc() {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), e(?y, ?z)]
        };
        let facts = vec![("e", vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
        ])];
        assert_all_engines_agree(prog, &["e", "tc"], facts, "tc", "left-linear TC");
    }

    // ====================================================================
    // Nonlinear TC (self-join)
    // ====================================================================

    #[test]
    fn all_engines_nonlinear_tc() {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
        };
        let facts = vec![("e", vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
        ])];
        assert_all_engines_agree(prog, &["e", "tc"], facts, "tc", "nonlinear TC");
    }

    // ====================================================================
    // Ancestor (deep chain)
    // ====================================================================

    #[test]
    fn all_engines_ancestor() {
        let prog = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };
        let facts = vec![("parent", vec![
            vec!["alice".into(), "carol".into()],
            vec!["alice".into(), "dave".into()],
            vec!["bob".into(), "eve".into()],
            vec!["carol".into(), "frank".into()],
            vec!["dave".into(), "grace".into()],
            vec!["eve".into(), "henry".into()],
            vec!["frank".into(), "ivy".into()],
            vec!["grace".into(), "jack".into()],
        ])];
        assert_all_engines_agree(prog, &["parent", "ancestor"], facts, "ancestor", "ancestor 4-gen");
    }

    // ====================================================================
    // Same-generation
    // ====================================================================

    #[test]
    fn all_engines_same_generation() {
        let prog = program! {
            sg(?x, ?y) <- [flat(?x, ?y)],
            sg(?y, ?x) <- [sg(?x, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
        };
        let facts = vec![
            ("flat", vec![vec!["r1".into(), "r2".into()]]),
            ("up", vec![
                vec!["m1".into(), "r1".into()], vec!["m2".into(), "r1".into()],
                vec!["m3".into(), "r2".into()], vec!["m4".into(), "r2".into()],
                vec!["l1".into(), "m1".into()], vec!["l2".into(), "m1".into()],
                vec!["l3".into(), "m2".into()], vec!["l4".into(), "m2".into()],
            ]),
            ("down", vec![
                vec!["r1".into(), "m1".into()], vec!["r1".into(), "m2".into()],
                vec!["r2".into(), "m3".into()], vec!["r2".into(), "m4".into()],
                vec!["m1".into(), "l1".into()], vec!["m1".into(), "l2".into()],
                vec!["m2".into(), "l3".into()], vec!["m2".into(), "l4".into()],
            ]),
        ];
        assert_all_engines_agree(
            prog, &["flat", "up", "down", "sg"], facts, "sg", "same-generation"
        );
    }

    // ====================================================================
    // Nonrecursive 2-hop
    // ====================================================================

    #[test]
    fn all_engines_two_hop() {
        let prog = program! {
            hop2(?x, ?z) <- [e(?x, ?y), e(?y, ?z)]
        };
        let facts = vec![("e", vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            vec!["b".into(), "d".into()],
        ])];
        assert_all_engines_agree(prog, &["e", "hop2"], facts, "hop2", "2-hop");
    }

    // ====================================================================
    // Cross product
    // ====================================================================

    #[test]
    fn all_engines_cross_product() {
        let prog = program! {
            pair(?x, ?y) <- [p(?x), q(?y)]
        };
        let facts = vec![
            ("p", vec![vec!["a".into()], vec!["b".into()]]),
            ("q", vec![vec!["1".into()], vec!["2".into()], vec!["3".into()]]),
        ];
        assert_all_engines_agree(prog, &["p", "q", "pair"], facts, "pair", "cross product");
    }

    // ====================================================================
    // Stratified evaluation (multi-stratum)
    // ====================================================================

    #[test]
    fn all_engines_stratified() {
        let prog = program! {
            base(?x, ?y) <- [edge(?x, ?y)],
            derived(?x, ?y) <- [base(?x, ?y)],
            derived(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)],
            top(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)]
        };
        let facts = vec![("edge", vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
        ])];
        assert_all_engines_agree(
            prog, &["edge", "base", "derived", "top"], facts, "derived", "stratified"
        );
    }

    // ====================================================================
    // Dense graph (stress test)
    // ====================================================================

    #[test]
    fn all_engines_dense_graph() {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        // 20-node dense graph
        let mut edges = Vec::new();
        for i in 0..20 {
            let src = i % 20;
            let dst = (i * 7 + 3) % 20;
            edges.push(vec![TypedValue::Int(src), TypedValue::Int(dst)]);
        }
        let facts = vec![("e", edges)];
        assert_all_engines_agree(prog, &["e", "tc"], facts, "tc", "dense graph 20");
    }

    // ====================================================================
    // Empty program / empty facts
    // ====================================================================

    #[test]
    fn all_engines_empty_facts() {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let facts: Vec<(&str, Vec<AnonymousGroundAtom>)> = vec![("e", vec![])];
        assert_all_engines_agree(prog, &["e", "tc"], facts, "tc", "empty facts");
    }
}
