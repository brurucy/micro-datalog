use std::collections::{ HashMap, HashSet };
use std::sync::Arc;

use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::evaluation::semi_naive::semi_naive_evaluation;
use crate::helpers::helpers::{
    add_prefix,
    split_program,
    OVERDELETION_PREFIX,
    REDERIVATION_PREFIX,
};
use crate::program_transformations::dependency_graph::sort_program;
use crate::program_transformations::dred::{ make_overdeletion_program, make_rederivation_program };
use crate::program_transformations::magic_sets::{
    apply_magic_transformation,
    create_magic_seed_fact,
};
use datalog_syntax::*;
use indexmap::IndexSet;
use crate::engine::subsumptive_table::*;

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
                .map(|fact| (**fact).clone())
        );
    }

    pub fn poll(&mut self) {
        println!("\n=== Starting poll() ===");
        if !self.unprocessed_deletions.is_empty() {
            println!("\nProcessing unprocessed deletions");
            self.unprocessed_deletions
                .drain_all_relations()
                .for_each(|(relation_symbol, unprocessed_facts)| {
                    println!(
                        "  Draining {} facts from {}",
                        unprocessed_facts.len(),
                        relation_symbol
                    );
                    let mut overdeletion_symbol = relation_symbol.clone();
                    add_prefix(&mut overdeletion_symbol, OVERDELETION_PREFIX);

                    println!("  Adding facts to {}", overdeletion_symbol);
                    self.processed.insert_all(
                        &overdeletion_symbol,
                        unprocessed_facts.into_iter().map(|fact| fact)
                    );
                });

            println!("\nRunning overdeletion evaluation");
            println!(
                "Nonrecursive overdeletion program: {:?}",
                self.nonrecursive_overdeletion_program
            );
            println!("Recursive overdeletion program: {:?}", self.recursive_overdeletion_program);
            semi_naive_evaluation(
                &mut self.processed,
                &self.nonrecursive_overdeletion_program,
                &self.recursive_overdeletion_program
            );
            self.processed.overdelete();

            println!("\nRunning rederivation evaluation");
            println!(
                "Nonrecursive rederivation program: {:?}",
                self.nonrecursive_rederivation_program
            );
            println!("Recursive rederivation program: {:?}", self.recursive_rederivation_program);
            semi_naive_evaluation(
                &mut self.processed,
                &self.nonrecursive_rederivation_program,
                &self.recursive_rederivation_program
            );
            self.processed.rederive();

            self.processed.clear_prefix(OVERDELETION_PREFIX);
            self.processed.clear_prefix(REDERIVATION_PREFIX);
        }

        if !self.unprocessed_insertions.is_empty() {
            println!("\nProcessing unprocessed insertions");
            println!("Before processing - Relations:");
            for (rel, facts) in &self.processed.inner {
                println!("  {}: {:?}", rel, facts);
            }

            // Additions
            self.unprocessed_insertions
                .drain_all_relations()
                .for_each(|(relation_symbol, unprocessed_facts)| {
                    println!(
                        "\nDraining {} facts from {}",
                        unprocessed_facts.len(),
                        relation_symbol
                    );
                    // Add them to processed
                    self.processed.insert_registered(
                        &relation_symbol,
                        unprocessed_facts.into_iter()
                    );
                    println!(
                        "After insertion - {} facts: {:?}",
                        relation_symbol,
                        self.processed.get_relation(&relation_symbol)
                    );
                });

            println!("\nRunning semi-naive evaluation");
            println!("Nonrecursive program: {:?}", self.nonrecursive_program);
            println!("Recursive program: {:?}", self.recursive_program);
            semi_naive_evaluation(
                &mut self.processed,
                &self.nonrecursive_program,
                &self.recursive_program
            );

            println!("\nAfter evaluation - Final relations state:");
            for (rel, facts) in &self.processed.inner {
                println!("  {}: {:?}", rel, facts);
            }
        } else {
            println!("No unprocessed insertions to handle");
        }
    }

    pub fn query_program<'a>(
        &'a mut self,
        query: &'a Query,
        query_temp: &'a Query,
        program: Program,
        strategy: &str
    ) -> Result<impl Iterator<Item = AnonymousGroundAtom> + 'a, String> {
        match strategy {
            "Top-down" => {
                println!("Using subsumptive tabling for evaluation");
                let mut table = SubsumptiveTable::new();

                // Save current base facts
                let mut base_facts = HashMap::new();
                for (rel_name, facts) in &self.processed.inner {
                    if !program.inner.iter().any(|rule| rule.head.symbol == *rel_name) {
                        let facts_vec: Vec<Arc<AnonymousGroundAtom>> = facts
                            .iter()
                            .cloned()
                            .collect();
                        if !facts_vec.is_empty() {
                            println!("Saving base facts for {}: {:?}", rel_name, facts_vec);
                            base_facts.insert(rel_name.clone(), facts_vec);
                        }
                    }
                }

                // Create new runtime with original program
                *self = MicroRuntime::new(program);

                // Restore base facts
                for (rel_name, facts) in base_facts {
                    println!("Restoring {} facts for {}", facts.len(), rel_name);
                    self.processed.insert_registered(&rel_name, facts.into_iter());
                }
                // Evaluate using subsumptive tabling and collect into Vec
                let results: Vec<_> = self.evaluate_subsumptive(query)?.into_iter().collect();
                Ok(results.into_iter())
            }
            "Bottom-up" => {
                // Save base facts before transformation
                let mut base_facts = HashMap::new();
                for (rel_name, facts) in &self.processed.inner {
                    if !program.inner.iter().any(|rule| rule.head.symbol == *rel_name) {
                        let facts_vec: Vec<Arc<AnonymousGroundAtom>> = facts
                            .iter()
                            .cloned()
                            .collect();
                        if !facts_vec.is_empty() {
                            println!("Saving base facts for {}: {:?}", rel_name, facts_vec);
                            base_facts.insert(rel_name.clone(), facts_vec);
                        }
                    }
                }

                // Transform program using magic sets
                let magic_program = apply_magic_transformation(&program, query);
                println!("Magic program: {:?}", magic_program);
                // After creating magic_program:
                let (nonrec, rec) = split_program(magic_program.clone());
                println!("\nProgram split:");
                println!("Nonrecursive: {:?}", nonrec);
                println!("Recursive: {:?}", rec);

                // Create new runtime with transformed program
                *self = MicroRuntime::new(magic_program);

                // Restore base facts
                for (rel_name, facts) in base_facts {
                    println!("Restoring {} facts for {}", facts.len(), rel_name);
                    self.processed.insert_registered(&rel_name, facts.into_iter());
                }

                // Add magic seed fact
                let (magic_pred, seed_fact) = create_magic_seed_fact(query);
                println!("Adding magic seed: {} {:?}", magic_pred, seed_fact);
                self.insert(&magic_pred, seed_fact);

                // Log initial state before evaluation
                println!("\nInitial state:");
                println!("Parent facts: {:?}", self.processed.get_relation("parent"));
                println!("Magic facts: {:?}", self.processed.get_relation(&magic_pred));

                println!("\nStarting evaluation");
                self.poll();

                // Log state after evaluation
                println!("\nFinal state:");
                println!("Parent facts: {:?}", self.processed.get_relation("parent"));
                println!("Magic facts: {:?}", self.processed.get_relation(&magic_pred));
                println!("Ancestor facts: {:?}", self.processed.get_relation("ancestor_bf"));

                println!("\nQuerying for results");
                let results: Vec<_> = self.query(&query_temp)?.collect();
                Ok(results.into_iter())
            }
            &_ => Err("Invalid evaluation strategy. Use 'Top-down' or 'Bottom-up'".to_string()),
        }
    }

    pub fn new(program: Program) -> Self {
        println!("\n=== Initializing MicroRuntime ===");
        let mut processed: RelationStorage = Default::default();
        let mut unprocessed_insertions: RelationStorage = Default::default();
        let mut unprocessed_deletions: RelationStorage = Default::default();

        let mut relations = IndexSet::new();
        let mut overdeletion_relations = IndexSet::new();
        let mut rederive_relations = IndexSet::new();

        println!("Adding relations from program rules:");
        program.inner.iter().for_each(|rule| {
            println!("  Head: {}", rule.head.symbol);
            relations.insert(&rule.head.symbol);
            overdeletion_relations.insert(format!("{}{}", OVERDELETION_PREFIX, rule.head.symbol));
            rederive_relations.insert(format!("{}{}", REDERIVATION_PREFIX, rule.head.symbol));
            rule.body.iter().for_each(|body_atom| {
                println!("  Body: {}", body_atom.symbol);
                relations.insert(&body_atom.symbol);
                overdeletion_relations.insert(
                    format!("{}{}", OVERDELETION_PREFIX, body_atom.symbol)
                );
            })
        });

        println!("\nInitializing storage with relations:");
        relations.iter().for_each(|relation_symbol| {
            println!("  {}", relation_symbol);
            processed.inner.entry(relation_symbol.to_string()).or_default();

            unprocessed_insertions.inner.entry(relation_symbol.to_string()).or_default();

            unprocessed_deletions.inner.entry(relation_symbol.to_string()).or_default();
        });

        overdeletion_relations.iter().for_each(|relation_symbol| {
            processed.inner.entry(relation_symbol.to_string()).or_default();
        });

        rederive_relations.iter().for_each(|relation_symbol| {
            processed.inner.entry(relation_symbol.to_string()).or_default();
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

    pub fn evaluate_subsumptive(
        &mut self,
        query: &Query
    ) -> Result<Vec<AnonymousGroundAtom>, String> {
        let mut table = SubsumptiveTable::new();
        let mut results = HashSet::new();

        // Convert query to pattern
        let pattern: Vec<Option<TypedValue>> = query.matchers
            .iter()
            .map(|m| {
                match m {
                    Matcher::Any => None,
                    Matcher::Constant(val) => Some(val.clone()),
                }
            })
            .collect();

        // Evaluate the query using subsumptive evaluation
        results = self.evaluate_subquery(
            &(Atom {
                symbol: query.symbol.to_string(),
                terms: query.matchers
                    .iter()
                    .map(|_| Term::Variable("_".to_string()))
                    .collect(),
                sign: true,
            }),
            &pattern,
            &mut table
        )?;

        // Filter results to match query pattern
        Ok(
            results
                .into_iter()
                .filter(|fact| pattern_match(query, fact))
                .collect()
        )
    }

    fn evaluate_rule_subsumptive(
        &self,
        rule: &Rule,
        pattern: &[Option<TypedValue>],
        table: &mut SubsumptiveTable,
        results: &mut HashSet<AnonymousGroundAtom>
    ) -> Result<(), String> {
        let mut bindings = HashMap::new();

        // Initialize bindings with pattern
        for (i, bound_val) in pattern.iter().enumerate() {
            if let Some(val) = bound_val {
                if let Term::Variable(var) = &rule.head.terms[i] {
                    bindings.insert(var.clone(), val.clone());
                }
            }
        }

        // Evaluate each body predicate using current bindings
        for body_atom in &rule.body {
            let subquery_pattern = create_subquery_pattern(body_atom, &bindings);
            let body_results = self.evaluate_subquery(body_atom, &subquery_pattern, table)?;

            // If no results found for this predicate, rule fails
            if body_results.is_empty() {
                return Ok(());
            }

            update_bindings(&mut bindings, body_atom, &body_results);
        }

        // Create result if bindings match pattern
        if let Some(result) = create_result(&rule.head, &bindings) {
            if
                result
                    .iter()
                    .zip(pattern.iter())
                    .all(|(val, pat)| {
                        match pat {
                            Some(bound_val) => val == bound_val,
                            None => true,
                        }
                    })
            {
                results.insert(result);
            }
        }

        Ok(())
    }

    fn evaluate_subquery(
        &self,
        atom: &Atom,
        pattern: &[Option<TypedValue>],
        table: &mut SubsumptiveTable
    ) -> Result<HashSet<AnonymousGroundAtom>, String> {
        println!("\nEvaluating subquery for atom {:?} with pattern {:?}", atom, pattern);

        // Check if we have cached results from a subsuming query
        if let Some(cached_results) = table.find_subsuming(&atom.symbol, pattern) {
            println!("Found cached results from subsuming query");
            return Ok(cached_results.iter().cloned().collect::<HashSet<_>>());
        }

        // Initialize partial results and cache them immediately
        let mut all_results = HashSet::new();

        // First handle base facts
        if let Some(facts) = self.processed.inner.get(&atom.symbol) {
            let matching_facts: HashSet<_> = facts
                .iter()
                .filter(|fact| {
                    fact.iter()
                        .zip(pattern)
                        .all(|(val, pattern_val)| {
                            match pattern_val {
                                Some(bound_val) => val == bound_val,
                                None => true,
                            }
                        })
                })
                .map(|arc_fact| (**arc_fact).clone())
                .collect();

            println!("Found {} matching base facts", matching_facts.len());
            all_results.extend(matching_facts);

            // Cache these initial results before recursion
            if !all_results.is_empty() {
                table.insert(&atom.symbol, pattern.to_vec(), all_results.iter().cloned().collect());
            }
        }

        // Then handle derived predicates
        let mut new_results = true;
        while new_results {
            new_results = false;
            let prev_size = all_results.len();

            for rule in &self.program.inner {
                if rule.head.symbol == atom.symbol {
                    println!("Evaluating rule: {:?}", rule);
                    let mut rule_results = HashSet::new();
                    self.evaluate_rule_subsumptive(rule, pattern, table, &mut rule_results)?;

                    // Track if we got any new results
                    let old_len = all_results.len();
                    all_results.extend(rule_results);
                    if all_results.len() > old_len {
                        new_results = true;
                    }
                }
            }

            // Cache intermediate results after each iteration
            if all_results.len() > prev_size {
                table.insert(&atom.symbol, pattern.to_vec(), all_results.iter().cloned().collect());
            }
        }

        println!("Derived {} total results", all_results.len());
        Ok(all_results)
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

    #[test]
    fn test_query_program_basic_ancestor() {
        // Set up a simple ancestor program
        let program =
            program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        // Create runtime and add base facts
        let mut runtime = MicroRuntime::new(program.clone());
        runtime.insert("parent", vec!["john".into(), "bob".into()]);
        runtime.insert("parent", vec!["bob".into(), "mary".into()]);
        runtime.poll();

        // Query for ancestors of john
        let query = build_query!(ancestor("john", _));
        let query_temp = build_query!(ancestor_bf("john", _));
        let results: HashSet<_> = runtime
            .query_program(&query, &query_temp, program, "Bottom-up")
            .unwrap()
            .collect();

        // Expected results - john is ancestor of both bob and mary
        let expected: HashSet<_> = vec![
            vec!["john".into(), "bob".into()],
            vec!["john".into(), "mary".into()]
        ]
            .into_iter()
            .collect();

        assert_eq!(expected, results);
    }

    #[test]
    fn test_query_program_basic_ancestor_top_down() {
        // Set up a simple ancestor program
        let program =
            program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        // Create runtime and add base facts
        let mut runtime = MicroRuntime::new(program.clone());
        runtime.insert("parent", vec!["john".into(), "bob".into()]);
        runtime.insert("parent", vec!["bob".into(), "mary".into()]);
        runtime.poll();

        // Query for ancestors of john
        let query = build_query!(ancestor("john", _));
        let results: HashSet<_> = runtime
            .query_program(&query, &query, program.clone(), "Top-down")
            .unwrap()
            .collect();

        // Expected results - john is ancestor of both bob and mary
        let expected: HashSet<_> = vec![
            vec!["john".into(), "bob".into()],
            vec!["john".into(), "mary".into()]
        ]
            .into_iter()
            .collect();

        assert_eq!(expected, results);

        // Test subsumption - query for specific case should reuse previous results
        let specific_query = build_query!(ancestor("john", "mary"));
        let specific_results: HashSet<_> = runtime
            .query_program(&specific_query, &specific_query, program, "Top-down")
            .unwrap()
            .collect();

        let expected_specific: HashSet<_> = vec![vec!["john".into(), "mary".into()]]
            .into_iter()
            .collect();

        assert_eq!(expected_specific, specific_results);
    }

    #[test]
    fn test_query_basic_ancestor() {
        // Set up a simple ancestor program
        let program =
            program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        // Create runtime and add base facts
        let mut runtime = MicroRuntime::new(program.clone());
        runtime.insert("parent", vec!["john".into(), "bob".into()]);
        runtime.insert("parent", vec!["bob".into(), "mary".into()]);

        runtime.poll();
        // Query for ancestors of john
        let query = build_query!(ancestor("john", _));
        let results: HashSet<_> = runtime.query(&query).unwrap().collect();

        // Expected results - john is ancestor of both bob and mary
        let expected: HashSet<_> = vec![
            vec!["john".into(), "bob".into()],
            vec!["john".into(), "mary".into()]
        ]
            .into_iter()
            .collect();

        assert_eq!(expected, results);
    }

    /* 
    #[test]
    fn test_query_program_same_generation() {
        let program =
            program! {
            sg(?x, ?y) <- [flat(?x, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
        };

        let mut runtime = MicroRuntime::new(program.clone());

        // Set up family tree facts
        runtime.insert("up", vec!["b1".into(), "a1".into()]);
        runtime.insert("up", vec!["b2".into(), "a1".into()]);
        runtime.insert("up", vec!["b3".into(), "a2".into()]);
        runtime.insert("up", vec!["b4".into(), "a2".into()]);
        runtime.insert("flat", vec!["a1".into(), "a2".into()]);
        runtime.insert("down", vec!["a1".into(), "b1".into()]);
        runtime.insert("down", vec!["a1".into(), "b2".into()]);
        runtime.insert("down", vec!["a2".into(), "b3".into()]);
        runtime.insert("down", vec!["a2".into(), "b4".into()]);

        // Query for nodes in same generation as b1
        let query = build_query!(sg("b1", _));
        let results: HashSet<_> = runtime.query_program(&query, program).unwrap().collect();

        // b1 should be in same generation as b2, b3, and b4
        let expected: HashSet<_> = vec![
            vec!["b1".into(), "b2".into()],
            vec!["b1".into(), "b3".into()],
            vec!["b1".into(), "b4".into()]
        ]
            .into_iter()
            .collect();

        assert_eq!(expected, results);
    }

    #[test]
    fn test_query_program_empty_result() {
        let program =
            program! {
            path(?x, ?y) <- [edge(?x, ?y)],
            path(?x, ?z) <- [edge(?x, ?y), path(?y, ?z)]
        };

        let mut runtime = MicroRuntime::new(program.clone());

        // Query with no matching facts
        let query = build_query!(path("nonexistent", _));
        let results: Vec<_> = runtime.query_program(&query, program).unwrap().collect();

        assert!(results.is_empty());
    }

    #[test]
    fn test_query_program_magic_sets_optimization() {
        // Program that would be inefficient without magic sets
        let program =
            program! {
            path(?x, ?y) <- [edge(?x, ?y)],
            path(?x, ?z) <- [edge(?x, ?y), path(?y, ?z)]
        };

        let mut runtime = MicroRuntime::new(program.clone());

        // Create a long chain a->b->c->d
        runtime.insert("edge", vec!["a".into(), "b".into()]);
        runtime.insert("edge", vec!["b".into(), "c".into()]);
        runtime.insert("edge", vec!["c".into(), "d".into()]);
        runtime.insert("edge", vec!["x".into(), "y".into()]); // Unrelated edge

        // Query paths from 'a'
        let query = build_query!(path("a", _));
        let results: HashSet<_> = runtime.query_program(&query, program).unwrap().collect();

        // Should only compute paths starting from 'a'
        let expected: HashSet<_> = vec![
            vec!["a".into(), "b".into()],
            vec!["a".into(), "c".into()],
            vec!["a".into(), "d".into()]
        ]
            .into_iter()
            .collect();

        assert_eq!(expected, results);
    }
    */
}
