use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::evaluation::semi_naive::semi_naive_evaluation;
use crate::helpers::helpers::{
    add_prefix, split_program, OVERDELETION_PREFIX, REDERIVATION_PREFIX,
};
use crate::program_transformations::dependency_graph::sort_program;
use crate::program_transformations::dred::{make_overdeletion_program, make_rederivation_program};
use datalog_syntax::*;
use indexmap::IndexSet;
pub struct MicroRuntime {
    processed: RelationStorage,
    unprocessed_insertions: RelationStorage,
    unprocessed_deletions: RelationStorage,
    program: Program,
    nonrecursive_program: Program,
    recursive_program: Program,
    nonrecursive_overdeletion_program: Program,
    recursive_overdeletion_program: Program,
    nonrecursive_rederivation_program: Program,
    recursive_rederivation_program: Program,
}

impl MicroRuntime {
    pub fn insert(&mut self, relation: &str, ground_atom: AnonymousGroundAtom) -> bool {
        self.unprocessed_insertions.insert(relation, ground_atom)
    }
    pub fn remove(&mut self, query: &Query) {
        let deletion_targets: Vec<_> = self
            .processed
            .get_relation(query.symbol)
            .iter()
            .map(|hash| hash)
            .filter(|fact| pattern_match(query, fact))
            .cloned()
            .collect();

        self.unprocessed_deletions
            .insert_registered(query.symbol, deletion_targets.into_iter());
    }
    pub fn contains(
        &self,
        relation: &str,
        ground_atom: &AnonymousGroundAtom,
    ) -> Result<bool, String> {
        if !self.safe() {
            return Err("poll needed to obtain correct results".to_string());
        }

        if !self.processed.contains(relation, ground_atom) {
            return Ok(self.unprocessed_insertions.contains(relation, ground_atom));
        }

        Ok(true)
    }
    pub fn query<'a>(
        &'a self,
        query: &'a Query,
    ) -> Result<impl Iterator<Item = AnonymousGroundAtom> + 'a, String> {
        if !self.safe() {
            return Err("poll needed to obtain correct results".to_string());
        }

        return Ok(self
            .processed
            .get_relation(query.symbol)
            .iter()
            .filter(|fact| pattern_match(query, fact))
            .map(|fact| (**fact).clone()));
    }

    pub fn poll(&mut self) {
        if !self.unprocessed_deletions.is_empty() {
            self.unprocessed_deletions.drain_all_relations().for_each(
                |(relation_symbol, unprocessed_facts)| {
                    let mut overdeletion_symbol = relation_symbol.clone();
                    add_prefix(&mut overdeletion_symbol, OVERDELETION_PREFIX);

                    self.processed.insert_all(
                        &overdeletion_symbol,
                        unprocessed_facts.into_iter().map(|fact| fact),
                    );
                },
            );

            semi_naive_evaluation(
                &mut self.processed,
                &self.nonrecursive_overdeletion_program,
                &self.recursive_overdeletion_program,
            );
            self.processed.overdelete();

            semi_naive_evaluation(
                &mut self.processed,
                &self.nonrecursive_rederivation_program,
                &self.recursive_rederivation_program,
            );
            self.processed.rederive();

            self.processed.clear_prefix(OVERDELETION_PREFIX);
            self.processed.clear_prefix(REDERIVATION_PREFIX);
        }
        if !self.unprocessed_insertions.is_empty() {
            // Additions
            self.unprocessed_insertions.drain_all_relations().for_each(
                |(relation_symbol, unprocessed_facts)| {
                    // And in their respective place
                    self.processed
                        .insert_registered(&relation_symbol, unprocessed_facts.into_iter());
                },
            );

            semi_naive_evaluation(
                &mut self.processed,
                &self.nonrecursive_program,
                &self.recursive_program,
            );
        }
    }

    pub fn new(program: Program) -> Self {
        let mut processed: RelationStorage = Default::default();
        let mut unprocessed_insertions: RelationStorage = Default::default();
        let mut unprocessed_deletions: RelationStorage = Default::default();

        let mut relations = IndexSet::new();
        let mut overdeletion_relations = IndexSet::new();
        let mut rederive_relations = IndexSet::new();

        program.inner.iter().for_each(|rule| {
            relations.insert(&rule.head.symbol);
            overdeletion_relations.insert(format!("{}{}", OVERDELETION_PREFIX, rule.head.symbol));
            rederive_relations.insert(format!("{}{}", REDERIVATION_PREFIX, rule.head.symbol));
            rule.body.iter().for_each(|body_atom| {
                relations.insert(&body_atom.symbol);
                overdeletion_relations
                    .insert(format!("{}{}", OVERDELETION_PREFIX, body_atom.symbol));
            })
        });

        relations.iter().for_each(|relation_symbol| {
            processed
                .inner
                .entry(relation_symbol.to_string())
                .or_default();

            unprocessed_insertions
                .inner
                .entry(relation_symbol.to_string())
                .or_default();

            unprocessed_deletions
                .inner
                .entry(relation_symbol.to_string())
                .or_default();
        });

        overdeletion_relations.iter().for_each(|relation_symbol| {
            processed
                .inner
                .entry(relation_symbol.to_string())
                .or_default();
        });

        rederive_relations.iter().for_each(|relation_symbol| {
            processed
                .inner
                .entry(relation_symbol.to_string())
                .or_default();
        });

        let (nonrecursive_program, recursive_program) = split_program(program.clone());

        let overdeletion_program = make_overdeletion_program(&program);
        let (nonrecursive_overdeletion_program, recursive_overdeletion_program) =
            split_program(overdeletion_program);

        let rederivation_program = make_rederivation_program(&program);
        let (nonrecursive_rederivation_program, recursive_rederivation_program) =
            split_program(rederivation_program);

        let nonrecursive_program = sort_program(&nonrecursive_program);
        let nonrecursive_overdeletion_program = sort_program(&nonrecursive_overdeletion_program);
        let nonrecursive_rederivation_program = sort_program(&nonrecursive_rederivation_program);

        Self {
            processed,
            unprocessed_insertions,
            unprocessed_deletions,
            program,
            nonrecursive_program,
            recursive_program,
            nonrecursive_overdeletion_program,
            recursive_overdeletion_program,
            nonrecursive_rederivation_program,
            recursive_rederivation_program,
        }
    }
    pub fn safe(&self) -> bool {
        self.unprocessed_insertions.is_empty() && self.unprocessed_deletions.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::datalog::MicroRuntime;
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use std::collections::HashSet;

    #[test]
    fn integration_test_insertions_only() {
        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };

        let mut runtime = MicroRuntime::new(tc_program);
        vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
        ]
        .into_iter()
        .for_each(|edge| {
            runtime.insert("e", edge);
        });

        runtime.poll();

        // This query reads as: "Get all in tc with any values in any positions"
        let all = build_query!(tc(_, _));
        // And this one as: "Get all in tc with the first term being a"
        // There also is a QueryBuilder, if you do not want to use a macro.
        let all_from_a = build_query!(tc("a", _));

        let actual_all: HashSet<AnonymousGroundAtom> = runtime.query(&all).unwrap().collect();
        let expected_all: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all, actual_all);

        let actual_all_from_a: HashSet<AnonymousGroundAtom> =
            runtime.query(&all_from_a).unwrap().collect();
        let expected_all_from_a: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all_from_a, actual_all_from_a);

        expected_all.iter().for_each(|fact| {
            assert!(runtime.contains("tc", fact).unwrap());
        });

        expected_all_from_a.iter().for_each(|fact| {
            assert!(runtime.contains("tc", fact).unwrap());
        });

        // Update
        runtime.insert("e", vec!["d".into(), "e".into()]);
        assert!(!runtime.safe());
        runtime.poll();
        assert!(runtime.safe());

        let actual_all_after_update: HashSet<AnonymousGroundAtom> =
            runtime.query(&all).unwrap().collect();
        let expected_all_after_update: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
            // Update
            vec!["d".into(), "e".into()],
            vec!["c".into(), "e".into()],
            vec!["b".into(), "e".into()],
            vec!["a".into(), "e".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all_after_update, actual_all_after_update);

        let actual_all_from_a_after_update: HashSet<AnonymousGroundAtom> =
            runtime.query(&all_from_a).unwrap().collect();
        let expected_all_from_a_after_update: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()],
            vec!["a".into(), "e".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(
            expected_all_from_a_after_update,
            actual_all_from_a_after_update
        );
    }
    #[test]
    fn integration_test_stratified_evaluation() {
        let stratified_program = program! {
            // Stratum 1: Base rule
            base(?x, ?y) <- [edge(?x, ?y)],

            // Stratum 2: Derived rule depends on Stratum 1
            derived(?x, ?y) <- [base(?x, ?y)],
            derived(?x, ?z) <- [base(?x, ?y), derived(?y, ?z)],

            // Stratum 3: Another level of derivation
            top(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)],
        };

        let mut runtime = MicroRuntime::new(stratified_program);

        // Insert facts into the base layer (Stratum 1)
        vec![vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]]
            .into_iter()
            .for_each(|edge| {
                runtime.insert("edge", edge);
            });

        runtime.poll();

        // Query and assert expectations for each stratum
        // Expected results for Stratum 1: `base`
        let base_query = build_query!(base(_, _));
        let actual_base: HashSet<AnonymousGroundAtom> =
            runtime.query(&base_query).unwrap().collect();
        let expected_base: HashSet<AnonymousGroundAtom> =
            vec![vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]]
                .into_iter()
                .collect();
        assert_eq!(expected_base, actual_base);

        // Expected results for Stratum 2: `derived`
        let derived_query = build_query!(derived(_, _));
        let actual_derived: HashSet<AnonymousGroundAtom> =
            runtime.query(&derived_query).unwrap().collect();
        let expected_derived: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["a".into(), "c".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_derived, actual_derived);

        // Expected results for Stratum 3: `top`
        let top_query = build_query!(top(_, _));
        let actual_top: HashSet<AnonymousGroundAtom> = runtime.query(&top_query).unwrap().collect();
        let expected_top: HashSet<AnonymousGroundAtom> =
            vec![vec!["a".into(), "c".into()]].into_iter().collect();
        assert_eq!(expected_top, actual_top);
    }

    #[test]
    fn test_query_program_same_generation() {
        let program = program! {
            sg(?x, ?y) <- [flat(?x, ?y)],
            sg(?y, ?x) <- [sg(?x, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
        };

        let mut runtime = MicroRuntime::new(program.clone());

        // Set up tree structure:
        //       a1    a2   (flat connects these)
        //      /  \  /  \
        //    b1  b2 b3  b4
        runtime.insert("up", vec!["b1".into(), "a1".into()]); // b1 up to a1
        runtime.insert("up", vec!["b2".into(), "a1".into()]); // b2 up to a1
        runtime.insert("up", vec!["b3".into(), "a2".into()]); // b3 up to a2
        runtime.insert("up", vec!["b4".into(), "a2".into()]); // b4 up to a2

        // Direct same-generation relationships
        runtime.insert("flat", vec!["a1".into(), "a2".into()]); // a1 same gen as a2

        runtime.insert("down", vec!["a1".into(), "b1".into()]); // a1 down to b1
        runtime.insert("down", vec!["a1".into(), "b2".into()]); // a1 down to b2
        runtime.insert("down", vec!["a2".into(), "b3".into()]); // a2 down to b3
        runtime.insert("down", vec!["a2".into(), "b4".into()]); // a2 down to b4

        runtime.poll();

        // Query for nodes in same generation as b1 (should find b2, b3, b4)
        let query = build_query!(sg("b1", _));
        let results: HashSet<_> = runtime.query(&query).unwrap().collect();

        // b1 should be in same generation as b2, b3, and b4
        let expected: HashSet<_> = vec![
            vec!["b1".into(), "b2".into()], // Same parent a1
            vec!["b1".into(), "b3".into()], // Through flat a1-a2
            vec!["b1".into(), "b4".into()], // Through flat a1-a2
            vec!["b1".into(), "b1".into()], // Every node is in same gen with itself
        ]
        .into_iter()
        .collect();

        assert_eq!(expected, results);
    }
}
