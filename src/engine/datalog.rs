use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::engine::storage::RelationStorage;
use crate::engine::subsumptive_table::SubsumptiveTable;
use crate::evaluation::query::pattern_match;
use crate::evaluation::semi_naive::semi_naive_evaluation;
use crate::helpers::helpers::split_program;
use crate::program_transformations::dependency_graph::sort_program;
use crate::program_transformations::magic_sets::{
    apply_magic_transformation, create_magic_seed_fact,
};
use datalog_syntax::*;
use indexmap::IndexSet;

use super::magic_evaluator::MagicEvaluator;
use super::subsumptive_evaluator::SubsumptiveEvaluator;

/// A Datalog runtime engine that supports incremental evaluation of rules using semi-naive strategy
#[derive(Default)]
pub struct MicroRuntime {
    /// Storage for facts that have gone through all fixpoint iterations
    /// These facts represent the current state of derived relations
    pub processed: RelationStorage,

    /// Storage for newly inserted facts that haven't been processed yet
    pub unprocessed_insertions: RelationStorage,

    /// Contains rules that can be evaluated in a single pass without fixpoint iteration
    nonrecursive_program: Program,

    /// Contains rules that require fixpoint iteration for complete evaluation
    recursive_program: Program,
}

impl MicroRuntime {
    pub fn insert(&mut self, relation: &str, ground_atom: impl Into<Fact>) -> bool {
        self.unprocessed_insertions
            .insert(relation, ground_atom.into().0)
    }

    pub fn contains(&self, relation: &str, ground_atom: impl Into<Fact>) -> Result<bool, String> {
        if !self.safe() {
            return Err("poll needed to obtain correct results".to_string());
        }

        let point_query = Fact::from(ground_atom.into()).0;
        if !self.processed.contains(relation, &point_query) {
            return Ok(self.unprocessed_insertions.contains(relation, &point_query));
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
        if !self.unprocessed_insertions.is_empty() {
            self.unprocessed_insertions.drain_all_relations().for_each(
                |(relation_symbol, unprocessed_facts)| {
                    self.processed
                        .insert_registered(&relation_symbol, unprocessed_facts.into_iter());
                },
            );
        }

        semi_naive_evaluation(
            &mut self.processed,
            &self.nonrecursive_program,
            &self.recursive_program,
        );
    }

    pub fn query_program<'a>(
        &'a mut self,
        query: &'a Query,
        program: Program,
        strategy: &str,
    ) -> Result<impl Iterator<Item = AnonymousGroundAtom> + 'a, String> {
        match strategy {
            "Bottom-up" => {
                let mut evaluator = MagicEvaluator::new(
                    self.processed.clone(),
                    self.unprocessed_insertions.clone(),
                );
               evaluator.evaluate_query(query, program)
            }
            "Top-down" => {
                let mut evaluator = SubsumptiveEvaluator::new(
                    self.processed.clone(),
                    self.unprocessed_insertions.clone(),
                    program,
                );

              let res = evaluator.evaluate_query(query);
              Ok(res.into_iter())
            }
            _ => return Err("Did you invent a new evaluation strategy?".to_string()),
        }
    }

    pub fn new(program: Program) -> Self {
        let mut processed: RelationStorage = Default::default();
        let mut unprocessed_insertions: RelationStorage = Default::default();

        let mut relations = IndexSet::new();

        program.inner.iter().for_each(|rule| {
            relations.insert(&rule.head.symbol);
            rule.body.iter().for_each(|body_atom| {
                relations.insert(&body_atom.symbol);
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
        });

        let (nonrecursive_program, recursive_program) = split_program(program.clone());

        let nonrecursive_program = sort_program(&nonrecursive_program);

        Self {
            processed,
            unprocessed_insertions,
            nonrecursive_program,
            recursive_program,
        }
    }

    pub fn safe(&self) -> bool {
        self.unprocessed_insertions.is_empty()
    }
}

#[macro_export]
macro_rules! convert_fact {
    ($query:expr) => {{
        $query
            .unwrap()
            .map(|aga| {
                (
                    &*Into::<String>::into(aga[0].clone()).leak(),
                    &*Into::<String>::into(aga[1].clone()).leak(),
                )
            })
            .collect()
    }};
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
        vec![("a", "b"), ("b", "c"), ("c", "d")]
            .into_iter()
            .for_each(|xy| {
                runtime.insert("e", xy);
            });

        runtime.poll();

        // This query reads as: "Get all in tc with any values in any positions"
        let all = build_query!(tc(_, _));
        // And this one as: "Get all in tc with the first term being a"
        // There also is a QueryBuilder, if you do not want to use a macro.
        let all_from_a = build_query!(tc("a", _));

        let actual_all: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all));
        let expected_all: HashSet<(&str, &str)> = vec![
            ("a", "b"),
            ("b", "c"),
            ("c", "d"),
            // Second iter
            ("a", "c"),
            ("b", "d"),
            // Third iter
            ("a", "d"),
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all, actual_all);

        let actual_all_from_a: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all_from_a));
        let expected_all_from_a: HashSet<(&str, &str)> = vec![("a", "b"), ("a", "c"), ("a", "d")]
            .into_iter()
            .collect();
        assert_eq!(expected_all_from_a, actual_all_from_a);

        expected_all.iter().for_each(|fact| {
            assert!(runtime.contains("tc", *fact).unwrap());
        });

        expected_all_from_a.iter().for_each(|fact| {
            assert!(runtime.contains("tc", *fact).unwrap());
        });

        // Update
        runtime.insert("e", ("d", "e"));
        assert!(!runtime.safe());
        runtime.poll();
        assert!(runtime.safe());

        let actual_all_after_update: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all));
        let expected_all_after_update: HashSet<(&str, &str)> = vec![
            ("a", "b"),
            ("b", "c"),
            ("c", "d"),
            // Second iter
            ("a", "c"),
            ("b", "d"),
            // Third iter
            ("a", "d"),
            // Update
            ("d", "e"),
            ("c", "e"),
            ("b", "e"),
            ("a", "e"),
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all_after_update, actual_all_after_update);

        let actual_all_from_a_after_update: HashSet<(&str, &str)> =
            convert_fact!(runtime.query(&all_from_a));
        let expected_all_from_a_after_update: HashSet<(&str, &str)> =
            vec![("a", "b"), ("a", "c"), ("a", "d"), ("a", "e")]
                .into_iter()
                .collect();
        assert_eq!(
            expected_all_from_a_after_update,
            actual_all_from_a_after_update
        );
    }

    #[test]
    fn integration_test_insertions_only_rev() {
        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), e(?y, ?z)],
        };

        let mut runtime = MicroRuntime::new(tc_program);
        vec![("a", "b"), ("b", "c"), ("c", "d")]
            .into_iter()
            .for_each(|xy| {
                runtime.insert("e", xy);
            });

        runtime.poll();

        // This query reads as: "Get all in tc with any values in any positions"
        let all = build_query!(tc(_, _));
        // And this one as: "Get all in tc with the first term being a"
        // There also is a QueryBuilder, if you do not want to use a macro.
        let all_from_a = build_query!(tc("a", _));

        let actual_all: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all));
        let expected_all: HashSet<(&str, &str)> = vec![
            ("a", "b"),
            ("b", "c"),
            ("c", "d"),
            // Second iter
            ("a", "c"),
            ("b", "d"),
            // Third iter
            ("a", "d"),
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all, actual_all);

        let actual_all_from_a: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all_from_a));
        let expected_all_from_a: HashSet<(&str, &str)> = vec![("a", "b"), ("a", "c"), ("a", "d")]
            .into_iter()
            .collect();
        assert_eq!(expected_all_from_a, actual_all_from_a);

        expected_all.iter().for_each(|fact| {
            assert!(runtime.contains("tc", *fact).unwrap());
        });

        expected_all_from_a.iter().for_each(|fact| {
            assert!(runtime.contains("tc", *fact).unwrap());
        });

        // Update
        runtime.insert("e", ("d", "e"));
        assert!(!runtime.safe());
        runtime.poll();
        assert!(runtime.safe());

        let actual_all_after_update: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all));
        let expected_all_after_update: HashSet<(&str, &str)> = vec![
            ("a", "b"),
            ("b", "c"),
            ("c", "d"),
            // Second iter
            ("a", "c"),
            ("b", "d"),
            // Third iter
            ("a", "d"),
            // Update
            ("d", "e"),
            ("c", "e"),
            ("b", "e"),
            ("a", "e"),
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all_after_update, actual_all_after_update);

        let actual_all_from_a_after_update: HashSet<(&str, &str)> =
            convert_fact!(runtime.query(&all_from_a));
        let expected_all_from_a_after_update: HashSet<(&str, &str)> =
            vec![("a", "b"), ("a", "c"), ("a", "d"), ("a", "e")]
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
            derived(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)],

            // Stratum 3: Another level of derivation
            top(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)],
        };

        let mut runtime = MicroRuntime::new(stratified_program);

        // Insert facts into the base layer (Stratum 1)
        vec![("a", "b"), ("b", "c")].into_iter().for_each(|edge| {
            runtime.insert("edge", edge);
        });

        runtime.poll();

        // Query and assert expectations for each stratum
        // Expected results for Stratum 1: `base`
        let base_query = build_query!(base(_, _));
        let actual_base: HashSet<(&str, &str)> = convert_fact!(runtime.query(&base_query));
        let expected_base: HashSet<(&str, &str)> =
            vec![("a", "b"), ("b", "c")].into_iter().collect();
        assert_eq!(expected_base, actual_base);

        // Expected results for Stratum 2: `derived`
        let derived_query = build_query!(derived(_, _));
        let actual_derived: HashSet<(&str, &str)> = convert_fact!(runtime.query(&derived_query));
        let expected_derived: HashSet<(&str, &str)> = vec![("a", "b"), ("b", "c"), ("a", "c")]
            .into_iter()
            .collect();
        assert_eq!(expected_derived, actual_derived);

        // Expected results for Stratum 3: `top`
        let top_query = build_query!(top(_, _));
        let actual_top: HashSet<(&str, &str)> = convert_fact!(runtime.query(&top_query));
        let expected_top: HashSet<(&str, &str)> = vec![("a", "c")].into_iter().collect();
        assert_eq!(expected_top, actual_top);
    }
}
