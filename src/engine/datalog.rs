use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::evaluation::semi_naive::semi_naive_evaluation;
use crate::helpers::helpers::split_program;
use crate::program_transformations::dependency_graph::sort_program;
use datalog_syntax::*;
use indexmap::IndexSet;

pub struct MicroRuntime {
    processed: RelationStorage,
    unprocessed_insertions: RelationStorage,
    nonrecursive_program: Program,
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
        runtime.insert("up", ("b1", "a1")); // b1 up to a1
        runtime.insert("up", ("b2", "a1")); // b2 up to a1
        runtime.insert("up", ("b3", "a2")); // b3 up to a2
        runtime.insert("up", ("b4", "a2")); // b4 up to a2

        // Direct same-generation relationships
        runtime.insert("flat", ("a1", "a2")); // a1 same gen as a2

        runtime.insert("down", ("a1", "b1")); // a1 down to b1
        runtime.insert("down", ("a1", "b2")); // a1 down to b2
        runtime.insert("down", ("a2", "b3")); // a2 down to b3
        runtime.insert("down", ("a2", "b4")); // a2 down to b4

        runtime.poll();

        // Query for nodes in same generation as b1 (should find b2, b3, b4)
        let query = build_query!(sg("b1", _));
        let results: HashSet<_> = convert_fact!(runtime.query(&query));

        // b1 should be in same generation as b2, b3, and b4
        let expected: HashSet<_> = vec![
            ("b1", "b2"), // Same parent a1
            ("b1", "b3"), // Through flat a1-a2
            ("b1", "b4"), // Through flat a1-a2
            ("b1", "b1"), // Every node is in same gen with itself
        ]
        .into_iter()
        .collect();

        assert_eq!(expected, results);
    }
}
