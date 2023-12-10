use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::evaluation::semi_naive::semi_naive_evaluation;
use crate::helpers::helpers::{
    add_prefix, split_program, DELTA_PREFIX, OVERDELETION_PREFIX, REDERIVATION_PREFIX,
};
use crate::program_transformations::delta_program::make_delta_program;
use crate::program_transformations::dred::{make_overdeletion_program, make_rederivation_program};
use datalog_syntax::*;
use std::collections::HashSet;

// Hairy
pub struct ChibiRuntime {
    processed: RelationStorage,
    unprocessed_insertions: RelationStorage,
    unprocessed_deletions: RelationStorage,
    program: Program,
    nonrecursive_delta_program: Program,
    recursive_delta_program: Program,
    nonrecursive_delta_overdeletion_program: Program,
    recursive_delta_overdeletion_program: Program,
    nonrecursive_delta_rederivation_program: Program,
    recursive_delta_rederivation_program: Program,
}

impl ChibiRuntime {
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
            .map(|fact| fact.clone()));
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
                &self.nonrecursive_delta_overdeletion_program,
                &self.recursive_delta_overdeletion_program,
            );
            self.processed.drain_deltas();
            self.processed.overdelete();

            semi_naive_evaluation(
                &mut self.processed,
                &self.nonrecursive_delta_rederivation_program,
                &self.recursive_delta_rederivation_program,
            );
            self.processed.drain_deltas();
            self.processed.rederive();

            self.processed.clear_prefix(OVERDELETION_PREFIX);
            self.processed.clear_prefix(REDERIVATION_PREFIX);
        }
        if !self.unprocessed_insertions.is_empty() {
            // Additions
            self.unprocessed_insertions.drain_all_relations().for_each(
                |(relation_symbol, unprocessed_facts)| {
                    // We dump all unprocessed EDB relations into delta EDB relations
                    self.processed.insert_registered(
                        &format!("{}{}", DELTA_PREFIX, relation_symbol),
                        unprocessed_facts.clone().into_iter(),
                    );
                    // And in their respective place
                    self.processed
                        .insert_registered(&relation_symbol, unprocessed_facts.into_iter());
                },
            );

            semi_naive_evaluation(
                &mut self.processed,
                &self.nonrecursive_delta_program,
                &self.recursive_delta_program,
            );

            self.processed.drain_deltas()
        }
    }
    pub fn new(program: Program) -> Self {
        let mut processed: RelationStorage = Default::default();
        let mut unprocessed_insertions: RelationStorage = Default::default();
        let mut unprocessed_deletions: RelationStorage = Default::default();

        let mut relations = HashSet::new();
        let mut delta_relations = HashSet::new();
        let mut overdeletion_relations = HashSet::new();
        let mut rederive_relations = HashSet::new();

        program.inner.iter().for_each(|rule| {
            relations.insert(&rule.head.symbol);
            delta_relations.insert(format!("{}{}", DELTA_PREFIX, rule.head.symbol));
            overdeletion_relations.insert(format!("{}{}", OVERDELETION_PREFIX, rule.head.symbol));
            overdeletion_relations.insert(format!(
                "{}{}{}",
                DELTA_PREFIX, OVERDELETION_PREFIX, rule.head.symbol
            ));
            rederive_relations.insert(format!("{}{}", REDERIVATION_PREFIX, rule.head.symbol));
            rederive_relations.insert(format!(
                "{}{}{}",
                DELTA_PREFIX, REDERIVATION_PREFIX, rule.head.symbol
            ));

            rule.body.iter().for_each(|body_atom| {
                relations.insert(&body_atom.symbol);
                delta_relations.insert(format!("{}{}", DELTA_PREFIX, body_atom.symbol));
                overdeletion_relations
                    .insert(format!("{}{}", OVERDELETION_PREFIX, body_atom.symbol));
                overdeletion_relations.insert(format!(
                    "{}{}{}",
                    DELTA_PREFIX, OVERDELETION_PREFIX, body_atom.symbol
                ));
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

        delta_relations.iter().for_each(|relation_symbol| {
            processed
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

        let (nonrecursive_delta_program, recursive_delta_program) =
            split_program(make_delta_program(&program, true));

        let overdeletion_program = make_delta_program(&make_overdeletion_program(&program), false);
        let (nonrecursive_delta_overdeletion_program, recursive_delta_overdeletion_program) =
            split_program(overdeletion_program);

        let rederivation_program = make_delta_program(&make_rederivation_program(&program), false);
        let (nonrecursive_delta_rederivation_program, recursive_delta_rederivation_program) =
            split_program(rederivation_program);

        Self {
            processed,
            unprocessed_insertions,
            unprocessed_deletions,
            program,
            nonrecursive_delta_program,
            recursive_delta_program,
            nonrecursive_delta_overdeletion_program,
            recursive_delta_overdeletion_program,
            nonrecursive_delta_rederivation_program,
            recursive_delta_rederivation_program,
        }
    }
    pub fn safe(&self) -> bool {
        self.unprocessed_insertions.is_empty() && self.unprocessed_deletions.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::datalog::ChibiRuntime;
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use std::collections::HashSet;

    #[test]
    fn integration_test_insertions_only() {
        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };

        let mut runtime = ChibiRuntime::new(tc_program);
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
    fn integration_test_deletions() {
        // Queries. The explanation is in the test above
        let all = build_query!(tc(_, _));
        let all_from_a = build_query!(tc("a", _));

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
        };

        let mut runtime = ChibiRuntime::new(tc_program);
        vec![
            vec!["a".into(), "b".into()],
            // this extra atom will help with testing that rederivation works
            vec!["a".into(), "e".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            vec!["d".into(), "e".into()],
        ]
        .into_iter()
        .for_each(|edge| {
            runtime.insert("e", edge);
        });

        runtime.poll();

        let actual_all: HashSet<AnonymousGroundAtom> = runtime.query(&all).unwrap().collect();
        let expected_all: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "e".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
            // Fourth iter
            vec!["d".into(), "e".into()],
            vec!["c".into(), "e".into()],
            vec!["b".into(), "e".into()],
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
            vec!["a".into(), "e".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all_from_a, actual_all_from_a);

        // Update
        // Point removals are a bit annoying, since they incur creating a query.
        let d_to_e = build_query!(e("d", "e"));
        runtime.remove(&d_to_e);
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
            // This remains
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
}
