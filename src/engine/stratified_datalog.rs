use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::evaluation::semi_naive::semi_naive_evaluation;
use crate::helpers::helpers::{
    add_prefix,
    split_program,
    DELTA_PREFIX,
    OVERDELETION_PREFIX,
    REDERIVATION_PREFIX,
};
use crate::program_transformations::delta_program::make_delta_program_stratified;
use crate::program_transformations::dred::{
    make_overdeletion_program_stratified,
    make_rederivation_program_stratified,
};
use datalog_syntax::*;
use std::collections::HashSet;
use crate::program_transformations::dependency_graph::sort_program;

// Hairy
pub struct MicroRuntime {
    processed: RelationStorage,
    unprocessed_insertions: RelationStorage,
    unprocessed_deletions: RelationStorage,
    program: StratifiedProgram,
    nonrecursive_delta_program: StratifiedProgram,
    recursive_delta_program: StratifiedProgram,
    nonrecursive_delta_overdeletion_program: StratifiedProgram,
    recursive_delta_overdeletion_program: StratifiedProgram,
    nonrecursive_delta_rederivation_program: StratifiedProgram,
    recursive_delta_rederivation_program: StratifiedProgram,
}

pub fn make_delta_program_stratified(program: &StratifiedProgram, update: bool) -> Program {
    let idb_relation_symbols: HashSet<_> = program.strata
    .iter() // Iterate over each stratum (Vec<Rule>)
    .flat_map(|stratum| stratum.iter()) // Flatten the strata to iterate over each rule
    .map(|rule| rule.head.symbol.clone()) // Extract the `symbol` from the rule head
    .collect(); // Collect the unique symbols into a HashSet

    let mut delta_rules_set = HashSet::new();

    // Process each stratum separately
    for stratum in program.strata {
        for rule in stratum {
            let mut delta_rule = rule.clone();
            add_prefix(&mut delta_rule.head.symbol, DELTA_PREFIX);

            let contains_idb = rule.body
                .iter()
                .any(|atom| idb_relation_symbols.contains(&atom.symbol));

            if !contains_idb && !update {
                // If the body does not contain any IDB relation symbols and it's not an update phase,
                // add the delta rule directly to the set.
                delta_rules_set.insert(delta_rule);
            } else {
                // Otherwise, consider each body atom and deltaify if necessary.
                for (index, body_atom) in rule.body.iter().enumerate() {
                    if update || idb_relation_symbols.contains(&body_atom.symbol) {
                        let mut new_rule = delta_rule.clone();
                        add_prefix(&mut new_rule.body[index].symbol, DELTA_PREFIX);
                        delta_rules_set.insert(new_rule);
                    }
                }
            }
        }
    }

    // Convert HashSet back into Vec and construct the Program.
    let delta_program: Vec<Rule> = delta_rules_set.into_iter().collect();

    StratifiedProgram::from(delta_program)
}

impl MicroRuntime {
    pub fn insert(&mut self, relation: &str, ground_atom: AnonymousGroundAtom) -> bool {
        self.unprocessed_insertions.insert(relation, ground_atom)
    }
    pub fn remove(&mut self, query: &Query) {
        let deletion_targets: Vec<_> = self.processed
            .get_relation(query.symbol)
            .iter()
            .map(|hash| hash)
            .filter(|fact| pattern_match(query, fact))
            .cloned()
            .collect();

        self.unprocessed_deletions.insert_registered(query.symbol, deletion_targets.into_iter());
    }
    pub fn contains(
        &self,
        relation: &str,
        ground_atom: &AnonymousGroundAtom
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
        query: &'a Query
    ) -> Result<impl Iterator<Item = AnonymousGroundAtom> + 'a, String> {
        if !self.safe() {
            return Err("poll needed to obtain correct results".to_string());
        }
        return Ok(
            self.processed
                .get_relation(query.symbol)
                .iter()
                .filter(|fact| pattern_match(query, fact))
                .map(|fact| fact.clone())
        );
    }

    fn process_overdeletion(&mut self, stratum_rules: &[Rule]) {
        self.unprocessed_deletions
            .drain_all_relations()
            .for_each(|(relation_symbol, unprocessed_facts)| {
                let mut overdeletion_symbol = relation_symbol.clone();
                add_prefix(&mut overdeletion_symbol, OVERDELETION_PREFIX);

                self.processed.insert_all(
                    &overdeletion_symbol,
                    unprocessed_facts.into_iter().map(|fact| fact)
                );
            });

        let nonrecursive_delta_overdeletion_program = sort_program(
            &Program::from(stratum_rules.to_vec())
        );
        semi_naive_evaluation(
            &mut self.processed,
            &nonrecursive_delta_overdeletion_program,
            &self.recursive_delta_overdeletion_program
        );
        self.processed.drain_deltas();
        self.processed.overdelete();

        self.processed.clear_prefix(OVERDELETION_PREFIX);
    }

    fn process_insertion(&mut self, stratum_rules: &[Rule]) {
        // Drain unprocessed insertions and distribute facts into the respective delta relations
        self.unprocessed_insertions
            .drain_all_relations()
            .for_each(|(relation_symbol, unprocessed_facts)| {
                // Insert facts into the delta relation for semi-naive evaluation
                let delta_relation_symbol = format!("{}{}", DELTA_PREFIX, relation_symbol);
                self.processed.insert_registered(
                    &delta_relation_symbol,
                    unprocessed_facts.clone().into_iter()
                );
                // Also insert facts into the base relation
                self.processed.insert_registered(&relation_symbol, unprocessed_facts.into_iter());
            });

        // Create a localized non-recursive delta program for the current stratum
        let nonrecursive_delta_program = sort_program(&Program::from(stratum_rules.to_vec()));

        // Perform semi-naive evaluation for both the non-recursive and recursive delta programs
        semi_naive_evaluation(
            &mut self.processed,
            &nonrecursive_delta_program,
            &self.recursive_delta_program
        );

        // Clear delta relations after processing to prepare for the next round
        self.processed.drain_deltas();
    }

    fn process_rederivation(&mut self, stratum_rules: &[Rule]) {
        let rederivation_program = Program::from(stratum_rules.to_vec());
        let (nonrecursive_rederivation, recursive_rederivation) = split_program(
            make_delta_program(&rederivation_program, false)
        );

        semi_naive_evaluation(
            &mut self.processed,
            &sort_program(&nonrecursive_rederivation),
            &recursive_rederivation
        );
        self.processed.drain_deltas();
        self.processed.rederive();
        self.processed.clear_prefix(REDERIVATION_PREFIX);
    }

    pub fn poll(&mut self) {
        let sorted_program = sort_program(&self.program);
        for stratum_rules in sorted_program.inner.iter() {
            if !self.unprocessed_deletions.is_empty() {
                self.process_overdeletion(stratum_rules);
                self.process_rederivation(stratum_rules);
            }
            if !self.unprocessed_insertions.is_empty() {
                self.process_insertion(stratum_rules);
            }
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
            overdeletion_relations.insert(
                format!("{}{}{}", DELTA_PREFIX, OVERDELETION_PREFIX, rule.head.symbol)
            );
            rederive_relations.insert(format!("{}{}", REDERIVATION_PREFIX, rule.head.symbol));
            rederive_relations.insert(
                format!("{}{}{}", DELTA_PREFIX, REDERIVATION_PREFIX, rule.head.symbol)
            );

            rule.body.iter().for_each(|body_atom| {
                relations.insert(&body_atom.symbol);
                delta_relations.insert(format!("{}{}", DELTA_PREFIX, body_atom.symbol));
                overdeletion_relations.insert(
                    format!("{}{}", OVERDELETION_PREFIX, body_atom.symbol)
                );
                overdeletion_relations.insert(
                    format!("{}{}{}", DELTA_PREFIX, OVERDELETION_PREFIX, body_atom.symbol)
                );
            })
        });

        relations.iter().for_each(|relation_symbol| {
            processed.inner.entry(relation_symbol.to_string()).or_default();

            unprocessed_insertions.inner.entry(relation_symbol.to_string()).or_default();

            unprocessed_deletions.inner.entry(relation_symbol.to_string()).or_default();
        });

        delta_relations.iter().for_each(|relation_symbol| {
            processed.inner.entry(relation_symbol.to_string()).or_default();
        });

        overdeletion_relations.iter().for_each(|relation_symbol| {
            processed.inner.entry(relation_symbol.to_string()).or_default();
        });

        rederive_relations.iter().for_each(|relation_symbol| {
            processed.inner.entry(relation_symbol.to_string()).or_default();
        });

        let (nonrecursive_delta_program, recursive_delta_program) = split_program(
            make_delta_program(&program, true)
        );

        let overdeletion_program = make_delta_program(&make_overdeletion_program(&program), false);
        let (nonrecursive_delta_overdeletion_program, recursive_delta_overdeletion_program) =
            split_program(overdeletion_program);
        let overdeletion_program = make_overdeletion_program_stratified(&program);
        let (nonrecursive_delta_overdeletion_program, recursive_delta_overdeletion_program) =
            split_program(make_delta_program(&overdeletion_program, false));

        let rederivation_program = make_delta_program(&make_rederivation_program(&program), false);
        let (nonrecursive_delta_rederivation_program, recursive_delta_rederivation_program) =
            split_program(rederivation_program);

        let nonrecursive_delta_program = sort_program(&nonrecursive_delta_program);
        let nonrecursive_delta_overdeletion_program = sort_program(
            &nonrecursive_delta_overdeletion_program
        );
        let nonrecursive_delta_rederivation_program = sort_program(
            &nonrecursive_delta_rederivation_program
        );

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
    use crate::engine::datalog::MicroRuntime;
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use std::collections::HashSet;

    #[test]
    fn integration_test_insertions_only() {
        let tc_program =
            program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };

        let mut runtime = MicroRuntime::new(tc_program);
        vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()]
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
            vec!["a".into(), "d".into()]
        ]
            .into_iter()
            .collect();
        assert_eq!(expected_all, actual_all);

        let actual_all_from_a: HashSet<AnonymousGroundAtom> = runtime
            .query(&all_from_a)
            .unwrap()
            .collect();
        let expected_all_from_a: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()]
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

        let actual_all_after_update: HashSet<AnonymousGroundAtom> = runtime
            .query(&all)
            .unwrap()
            .collect();
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
            vec!["a".into(), "e".into()]
        ]
            .into_iter()
            .collect();
        assert_eq!(expected_all_after_update, actual_all_after_update);

        let actual_all_from_a_after_update: HashSet<AnonymousGroundAtom> = runtime
            .query(&all_from_a)
            .unwrap()
            .collect();
        let expected_all_from_a_after_update: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()],
            vec!["a".into(), "e".into()]
        ]
            .into_iter()
            .collect();
        assert_eq!(expected_all_from_a_after_update, actual_all_from_a_after_update);
    }
    #[test]
    fn integration_test_deletions() {
        // Queries. The explanation is in the test above
        let all = build_query!(tc(_, _));
        let all_from_a = build_query!(tc("a", _));

        let tc_program =
            program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
        };

        let mut runtime = MicroRuntime::new(tc_program);
        vec![
            vec!["a".into(), "b".into()],
            // this extra atom will help with testing that rederivation works
            vec!["a".into(), "e".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            vec!["d".into(), "e".into()]
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
            vec!["b".into(), "e".into()]
        ]
            .into_iter()
            .collect();
        assert_eq!(expected_all, actual_all);

        let actual_all_from_a: HashSet<AnonymousGroundAtom> = runtime
            .query(&all_from_a)
            .unwrap()
            .collect();
        let expected_all_from_a: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()],
            vec!["a".into(), "e".into()]
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

        let actual_all_after_update: HashSet<AnonymousGroundAtom> = runtime
            .query(&all)
            .unwrap()
            .collect();
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
            vec!["a".into(), "e".into()]
        ]
            .into_iter()
            .collect();
        assert_eq!(expected_all_after_update, actual_all_after_update);

        let actual_all_from_a_after_update: HashSet<AnonymousGroundAtom> = runtime
            .query(&all_from_a)
            .unwrap()
            .collect();
        let expected_all_from_a_after_update: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()],
            vec!["a".into(), "e".into()]
        ]
            .into_iter()
            .collect();
        assert_eq!(expected_all_from_a_after_update, actual_all_from_a_after_update);
    }

    #[test]
    fn integration_test_stratified_evaluation() {
        let stratified_program =
            program! {
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
        let actual_base: HashSet<AnonymousGroundAtom> = runtime
            .query(&base_query)
            .unwrap()
            .collect();
        let expected_base: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()]
        ]
            .into_iter()
            .collect();
        assert_eq!(expected_base, actual_base);

        // Expected results for Stratum 2: `derived`
        let derived_query = build_query!(derived(_, _));
        let actual_derived: HashSet<AnonymousGroundAtom> = runtime
            .query(&derived_query)
            .unwrap()
            .collect();
        let expected_derived: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["a".into(), "c".into()]
        ]
            .into_iter()
            .collect();
        assert_eq!(expected_derived, actual_derived);

        // Expected results for Stratum 3: `top`
        let top_query = build_query!(top(_, _));
        let actual_top: HashSet<AnonymousGroundAtom> = runtime.query(&top_query).unwrap().collect();
        let expected_top: HashSet<AnonymousGroundAtom> = vec![vec!["a".into(), "c".into()]]
            .into_iter()
            .collect();
        assert_eq!(expected_top, actual_top);

        // Test deletions to check if stratified rederivation works correctly
        let edge_b_to_c = build_query!(edge("b", "c"));
        runtime.remove(&edge_b_to_c);
        runtime.poll();

        // After deletion, only certain derived facts should remain
        let actual_derived_after_delete: HashSet<AnonymousGroundAtom> = runtime
            .query(&derived_query)
            .unwrap()
            .collect();
        let expected_derived_after_delete: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()]
        ]
            .into_iter()
            .collect();
        assert_eq!(expected_derived_after_delete, actual_derived_after_delete);

        let actual_top_after_delete: HashSet<AnonymousGroundAtom> = runtime
            .query(&top_query)
            .unwrap()
            .collect();
        let expected_top_after_delete: HashSet<AnonymousGroundAtom> = HashSet::new();
        assert_eq!(expected_top_after_delete, actual_top_after_delete);
    }
}
