use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::engine::storage::RelationStorage;
use crate::helpers::helpers::is_derived_predicate;
use crate::helpers::subsumptive_helpers::{create_result, update_bindings};
use datalog_rule_macro::rule;
use datalog_syntax::*;

use super::subsumptive_table::SubsumptiveTable;

pub struct SubsumptiveEvaluator {
    processed: RelationStorage,
    unprocessed_insertions: RelationStorage,
    program: Program,
    unprocessed_subqueries: HashMap<usize, HashMap<Atom, (Rule, HashMap<String, TypedValue>)>>,
}

impl<'a> SubsumptiveEvaluator {
    pub fn new(processed: RelationStorage, unprocessed: RelationStorage, program: Program) -> Self {
        Self {
            processed,
            unprocessed_insertions: unprocessed,
            program,
            unprocessed_subqueries: HashMap::new(),
        }
    }

    pub fn evaluate_query<'b>(&mut self, query: &'b Query) -> (Vec<Vec<TypedValue>>, Duration) {
        //Create an Atom object from the query
        let query_atom = Atom {
            symbol: query.symbol.to_string(),
            terms: query
                .matchers
                .iter()
                .map(|m| match m {
                    Matcher::Any => Term::Variable("_".to_string()),
                    Matcher::Constant(val) => Term::Constant(val.clone()),
                })
                .collect(),
            sign: true,
        };
        let mut table = SubsumptiveTable::new();
        let mut all_results = HashSet::new();
        let mut iteration = 0;

        let start = Instant::now();

        //loop {
        iteration += 1;
        let mut round_results = HashSet::new();

        let results: Vec<Vec<TypedValue>> = self.evaluate_subquery(
            self.program.clone(),
            &query_atom,
            None,
            &mut HashSet::new(),
            &mut table,
            None,
            0, // Start with depth 0
            false,
        );

        //println!("Unprocessed subqueries {:?}", self.unprocessed_subqueries);

        round_results.extend(results.into_iter().map(|r| r));

        while !self.unprocessed_subqueries.is_empty() {
            let mut new_unprocessed_subqueries = self.unprocessed_subqueries.clone();
            for (depth, subqueries) in new_unprocessed_subqueries.iter_mut() {
                for (subquery_atom, (subquery_rule, bindings)) in subqueries.iter() {
                    let mut subquery_results = HashSet::new();

                    self.evaluate_unprocessed_subquery(
                        subquery_atom,
                        subquery_rule,
                        &bindings,
                        &mut HashSet::new(),
                        &mut table,
                        &mut subquery_results,
                        0,
                        depth + 1,
                    );

                    round_results.extend(subquery_results);
                }
                self.unprocessed_subqueries.remove(depth);
            }
        }

        // Check for convergence
        let previous_size = all_results.len();
        all_results.extend(round_results);

        // if all_results.len() == previous_size {
        //     break; // Fixed point reached
        // }

        let arc_facts: Vec<Arc<AnonymousGroundAtom>> = all_results
            .iter()
            .map(|fact| Arc::new(fact.clone()))
            .collect();

        self.processed
            .insert_all(&query_atom.symbol, arc_facts.into_iter());

        println!("Subsumptive table at iteration {:?}", iteration);
        for (atom, facts) in table.tables.iter() {
            println!("Atom {:?}", atom);
            for fact in facts {
                println!("Subquery {:?}", fact.0);
                for tuples in fact.1.iter() {
                    println!("{:?}", tuples);
                }
                //println!("Fact {:?}", fact);
            }
        }

        //}
        let evaluation_time = start.elapsed();
        let final_results = self.filter_results_for_query(all_results.into_iter().collect(), query);

        //println!("Subsumptive table {:?}", table);
        //Return the results as an iterator
        return (final_results, evaluation_time);
    }

    pub fn evaluate_subquery(
        &mut self,
        program: Program,
        subquery_atom: &Atom,
        subquery_rule: Option<&Rule>,
        seen_queries: &mut HashSet<Atom>,
        table: &mut SubsumptiveTable,
        cache: Option<(usize, HashMap<String, TypedValue>)>, // (body atom index, bindings)
        depth: usize,
        is_unprocessed: bool,
    ) -> Vec<Vec<TypedValue>> {
        //println!("Evaluating subquery {:?}", subquery_atom);
        if depth > 20 {
            return Vec::new();
        }
        let mut all_results = HashSet::new();

        let mut subquery_atom = subquery_atom.clone();

        if is_unprocessed && cache.is_some() {
            let (body_atom_index, cached_rule_bindings) = cache.clone().unwrap();

            let cached_body_atom = Atom {
                symbol: subquery_rule.unwrap().body[body_atom_index].symbol.clone(),
                sign: subquery_rule.unwrap().body[body_atom_index].sign,
                terms: subquery_rule.unwrap().body[body_atom_index]
                    .terms
                    .iter()
                    .map(|term| {
                        if let Term::Variable(var) = term {
                            if let Some(bound_value) = cached_rule_bindings.get(var) {
                                Term::Constant(bound_value.clone())
                            } else {
                                term.clone()
                            }
                        } else {
                            term.clone()
                        }
                    })
                    .collect(),
            };
            subquery_atom = cached_body_atom;
        }

        if let Some(cached_results) = table.find_subsuming(&subquery_atom) {
            return cached_results
                .iter()
                .filter(|subresult| {
                    subresult
                        .iter()
                        .enumerate()
                        .all(|(i, res)| match &subquery_atom.terms[i] {
                            Term::Constant(atom_val) => res == atom_val,
                            Term::Variable(_) => true,
                        })
                })
                .cloned()
                .collect();
        }

        //Prevent infinite recursion by tracking seen queries
        if seen_queries.contains(&subquery_atom) {
            let (body_atom_index, cached_rule_bindings) = cache.unwrap();
            // this should only happen in the unprocessed subqueries?
            // println!("Inserting unprocessed subquery {:?}", subquery_atom);
            // println!("Body atom index {:?}", body_atom_index);
            // println!("Cached rule bindings {:?}", cached_rule_bindings);
            // println!("Depth {:?}", depth);
            // println!("Subquery rule {:?}", subquery_rule.unwrap());
            self.insert_unprocessed_subquery(
                body_atom_index,
                subquery_rule.unwrap().clone(),
                cached_rule_bindings.clone(),
                depth,
            );

            return Vec::new();
        }

        seen_queries.insert(subquery_atom.clone());

        //First, process base facts (facts in storage)
        if let Some(facts) = self.unprocessed_insertions.inner.get(&subquery_atom.symbol) {
            let matching_facts: HashSet<_> = facts
                .iter()
                .filter(|fact| {
                    fact.iter()
                        .zip(subquery_atom.terms.iter())
                        .all(|(val, term)| match term {
                            Term::Constant(bound_val) => val == bound_val,
                            Term::Variable(_) => true,
                        })
                })
                .map(|arc_fact| (**arc_fact).clone())
                .collect();

            all_results.extend(matching_facts);
        }

        if let Some(facts) = self.processed.inner.get(&subquery_atom.symbol) {
            let matching_facts: HashSet<_> = facts
                .iter()
                .filter(|fact| {
                    fact.iter()
                        .zip(subquery_atom.terms.iter())
                        .all(|(val, term)| match term {
                            Term::Constant(bound_val) => val == bound_val,
                            Term::Variable(_) => true,
                        })
                })
                .map(|arc_fact| (**arc_fact).clone())
                .collect();

            all_results.extend(matching_facts);
        }

        //Process each matching rule
        for rule in program.inner.iter() {
            if rule.head.symbol != subquery_atom.symbol {
                continue;
            }
            let mut rule_results = HashSet::new();
            let mut new_subquery_terms = Vec::new();

            // Check if rule is compatible with subquery
            let mut is_compatible = true;
            for (rule_term, subquery_term) in rule.head.terms.iter().zip(subquery_atom.terms.iter())
            {
                match (rule_term, subquery_term) {
                    //If rule has a constant, subquery must have the same constant
                    (Term::Constant(rule_val), Term::Constant(subquery_val)) => {
                        if rule_val != subquery_val {
                            is_compatible = false;
                            break;
                        } else {
                            new_subquery_terms.push(rule_term.clone());
                        }
                    }
                    //If rule has a variable, subquery can have any constant
                    (Term::Variable(_), Term::Constant(_)) => {
                        new_subquery_terms.push(subquery_term.clone());
                    }
                    //If subquery has a variable, rule can have anything
                    (_, Term::Variable(_)) => {
                        new_subquery_terms.push(rule_term.clone());
                    }
                }
            }

            //Skip this rule if incompatible
            if !is_compatible {
                continue;
            }

            // if let Some(existing_bindings) = &bindings {
            //     new_subquery_terms = new_subquery_terms.iter().map(|term| {
            //         if let Term::Variable(var) = term {
            //             if let Some(bound_value) = existing_bindings.get(var) {
            //                 Term::Constant(bound_value.clone())
            //             } else {
            //                 term.clone()
            //             }
            //         } else {
            //             term.clone()
            //         }
            //     }).collect();
            // }

            // if subquery_atom.terms[0] == Term::Variable("x".to_string()) && subquery_atom.terms[1] == Term::Variable("y".to_string()) {
            //     println!("================================================");
            //     println!("wazzup");
            //     println!("Bindings {:?}", bindings.as_ref().unwrap());
            //     println!("Evaluating rule {:?}", rule);
            //     println!("Subquery atom {:?}", current_subquery_atom);
            //     println!("New subquery terms {:?}", new_subquery_terms);
            //     println!("================================================");
            // }

            let next_subquery_atom = Atom {
                symbol: subquery_atom.symbol.clone(), // the same as head of rule
                sign: subquery_atom.sign,
                terms: new_subquery_terms.clone(), // mixed with head of rule terms
            };

            self.evaluate_rule_subsumptive(
                &next_subquery_atom,
                &rule,
                Some(HashMap::new()),
                seen_queries,
                table,
                &mut rule_results,
                depth + 1,
                is_unprocessed,
            );

            all_results.extend(rule_results);
        }

        //Cache results if we found any
        if !all_results.is_empty() {
            // println!(
            //     "Inserting results for subquery atom {:?} at depth {:?}",
            //     subquery_atom.clone(),
            //     depth
            // );
            // println!("Results {:?}", all_results);
            table.insert(&subquery_atom, all_results.iter().cloned().collect());
        }

        //Remove this query from seen set since we're done processing it
        seen_queries.remove(&subquery_atom);
        all_results.into_iter().collect()
    }

    fn evaluate_rule_subsumptive(
        &mut self,
        subquery_atom: &Atom, // should have a bound term
        rule: &Rule,
        bindings: Option<HashMap<String, TypedValue>>,
        seen_queries: &mut HashSet<Atom>,
        table: &mut SubsumptiveTable,
        results: &mut HashSet<AnonymousGroundAtom>,
        depth: usize,
        is_unprocessed: bool,
    ) -> () {
        let mut new_bindings: HashMap<String, TypedValue>;
        if let Some(existing_bindings) = &bindings {
            new_bindings = existing_bindings.clone();
        } else {
            new_bindings = HashMap::new();
        }

        //Initialize bindings from the head pattern
        // ignoring constants in the head bc we've already checked that they match with the subquery atom
        for (i, arg) in rule.head.terms.iter().enumerate() {
            if let (Term::Variable(var), Term::Constant(val)) =
                (arg, subquery_atom.terms[i].clone())
            {
                new_bindings.insert(var.clone(), val.clone());
            }
        }

        //Evaluate each body atom in sequence
        self.evaluate_rule_body(
            &rule,
            0,
            &mut new_bindings,
            seen_queries,
            table,
            results,
            depth + 1,
            is_unprocessed,
        );
    }

    fn evaluate_rule_body(
        &mut self,
        subquery_rule: &Rule,
        pos: usize,
        rule_bindings: &mut HashMap<String, TypedValue>,
        seen_queries: &mut HashSet<Atom>,
        table: &mut SubsumptiveTable,
        results: &mut HashSet<AnonymousGroundAtom>,
        depth: usize,
        is_unprocessed: bool,
    ) -> () {
        let body = &subquery_rule.body;
        let head = &subquery_rule.head;

        // Base case: all body atoms have been processed
        if pos >= body.len() {
            if let Some(result) = create_result(head, rule_bindings) {
                results.insert(result);
            }
            return;
        }

        let body_atom = Atom {
            symbol: body[pos].symbol.clone(),
            sign: body[pos].sign,
            terms: body[pos]
                .terms
                .iter()
                .map(|term| match term {
                    Term::Variable(var) => {
                        if let Some(bound_value) = rule_bindings.get(var) {
                            Term::Constant(bound_value.clone())
                        } else {
                            term.clone()
                        }
                    }
                    Term::Constant(_) => term.clone(),
                })
                .collect(),
        };

        let mut subresults: Vec<Vec<TypedValue>> = Vec::new();

        if is_derived_predicate(&self.program, &body_atom.symbol) {
            // we moving out of this rule

            // let head_atom = Atom {
            //     symbol: subquery_rule.head.symbol.clone(),
            //     sign: subquery_rule.head.sign,
            //     terms: subquery_rule
            //         .head
            //         .terms
            //         .iter()
            //         .map(|term| match term {
            //             Term::Variable(var) => {
            //                 if let Some(bound_value) = rule_bindings.get(var) {
            //                     Term::Constant(bound_value.clone())
            //                 } else {
            //                     term.clone()
            //                 }
            //             }
            //             Term::Constant(_) => term.clone(),
            //         })
            //         .collect(),
            // };

            let new_query_atom = Atom {
                symbol: body_atom.symbol.clone(),
                sign: body_atom.sign,
                terms: body_atom
                    .terms
                    .iter()
                    .map(|term| match term {
                        Term::Variable(var) => {
                            if let Some(bound_value) = rule_bindings.get(var) {
                                Term::Constant(bound_value.clone())
                            } else {
                                Term::Variable("_".to_string())
                            }
                        }
                        Term::Constant(_) => term.clone(),
                    })
                    .collect(),
            };

            subresults = self.evaluate_subquery(
                self.program.clone(),
                &new_query_atom,
                Some(subquery_rule),
                seen_queries,
                table,
                Some((pos, rule_bindings.clone())),
                depth + 1,
                is_unprocessed,
            );
        }

        subresults.extend(self.match_base_predicate(&body_atom));

        for subresult in subresults {
            let mut updated_bindings = rule_bindings.clone();
            let subresult_set = HashSet::from_iter(vec![subresult.clone()]);
            update_bindings(&mut updated_bindings, &body_atom, &subresult_set);

            self.evaluate_rule_body(
                subquery_rule,
                pos + 1,
                &mut updated_bindings,
                seen_queries,
                table,
                results,
                depth + 1,
                is_unprocessed,
            );
        }
    }

    fn evaluate_unprocessed_subquery(
        &mut self,
        subquery_atom: &Atom,
        subquery_rule: &Rule,
        bindings: &HashMap<String, TypedValue>,
        seen_queries: &mut HashSet<Atom>,
        table: &mut SubsumptiveTable,
        results: &mut HashSet<AnonymousGroundAtom>,
        pos: usize,
        depth: usize,
    ) -> () {
        let mut subresults = self.evaluate_subquery(
            self.program.clone(),
            &subquery_atom,
            Some(subquery_rule),
            seen_queries,
            table,
            Some((pos, bindings.clone())),
            depth,
            true,
        );

        //println!("ALL unprocessed subresults {:?}", subresults);

        subresults = subresults
            .iter()
            .filter(|subresult| {
                subresult
                    .iter()
                    .enumerate()
                    .all(|(i, res)| match &subquery_atom.terms[i] {
                        Term::Constant(atom_val) => res == atom_val,
                        Term::Variable(_) => true,
                    })
            })
            .cloned()
            .collect();

        for subresult in subresults {
            let mut new_bindings = bindings.clone();
            let subresult_set = HashSet::from_iter(vec![subresult.clone()]);
            update_bindings(&mut new_bindings, &subquery_atom, &subresult_set);
            self.evaluate_rule_body(
                subquery_rule,
                pos + 1,
                &mut new_bindings,
                seen_queries,
                table,
                results,
                depth,
                false, //not sure TODO
            );
        }
        // println!("================================================");
        // println!("Evaluated unprocessed subquery {:?}", subquery_atom); // tc("x", "y")
        // println!("Subquery rule {:?}", subquery_rule); // tc("x", "z") <- [tc("x", "y"), tc("y", "z")]
        // println!("Bindings {:?}", bindings); //this should have bindings
        // println!("Pos {:?}", pos); //0
        // println!("Depth {:?}", depth); // 7
        // println!("Results {:?}", results); // should be w.o bindings [("a", "b"), ("b", "c"), ("c", "d"), ("a", "c"), ("b", "d"), ("a", "d")]
        // println!("================================================");
    }

    fn match_base_predicate(&self, atom: &Atom) -> HashSet<AnonymousGroundAtom> {
        let mut results = HashSet::new();

        if let Some(facts) = self.processed.inner.get(&atom.symbol) {
            let matching_facts: Vec<_> = facts
                .iter()
                .filter(|fact| {
                    fact.iter()
                        .zip(atom.terms.iter())
                        .all(|(val, term)| match term {
                            Term::Constant(bound_val) => val == bound_val,
                            Term::Variable(_) => true,
                        })
                })
                .map(|arc_fact| (**arc_fact).clone())
                .collect();

            results.extend(matching_facts);
        }

        if let Some(facts) = self.unprocessed_insertions.inner.get(&atom.symbol) {
            let matching_facts: Vec<_> = facts
                .iter()
                .filter(|fact| {
                    fact.iter()
                        .zip(atom.terms.iter())
                        .all(|(val, term)| match term {
                            Term::Constant(bound_val) => val == bound_val,
                            Term::Variable(_) => true,
                        })
                })
                .map(|arc_fact| (**arc_fact).clone())
                .collect();

            results.extend(matching_facts);
        }

        results
    }

    fn insert_unprocessed_subquery(
        &mut self,
        body_atom_index: usize,
        subquery_rule: Rule,
        bindings: HashMap<String, TypedValue>,
        depth: usize,
    ) {
        // Get mutable reference to the inner map for this depth, or insert a new one if it doesn't exist
        let atoms_at_depth = self
            .unprocessed_subqueries
            .entry(depth)
            .or_insert_with(HashMap::new);
        // Insert the subquery_atom and its bindings
        atoms_at_depth.insert(
            subquery_rule.body[body_atom_index].clone(),
            (subquery_rule, bindings.clone()),
        );
    }

    fn filter_results_for_query(
        &self,
        results: Vec<Vec<TypedValue>>,
        query: &Query,
    ) -> Vec<Vec<TypedValue>> {
        results
            .into_iter()
            .filter(|result| {
                // Use existing pattern_match function
                use crate::evaluation::query::pattern_match;
                pattern_match(query, result)
            })
            .collect()
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use std::sync::Arc;

//     fn setup_storage() -> RelationStorage {
//         let mut storage = RelationStorage::default();

//         // Insert some test facts into parent relation
//         storage
//             .inner
//             .insert("parent".to_string(), Default::default());
//         let parent_facts = vec![
//             vec![TypedValue::from("john"), TypedValue::from("mary")],
//             vec![TypedValue::from("john"), TypedValue::from("bob")],
//             vec![TypedValue::from("mary"), TypedValue::from("ann")],
//         ];
//         for fact in parent_facts {
//             storage
//                 .inner
//                 .get_mut("parent")
//                 .unwrap()
//                 .insert(Arc::new(fact));
//         }
//         storage
//     }

//     #[test]
//     fn test_match_base_predicate_exact_match() {
//         let evaluator = SubsumptiveEvaluator::new(
//             setup_storage(),
//             RelationStorage::default(),
//             Program::default(),
//         );

//         let atom = Atom {
//             symbol: "parent".to_string(),
//             terms: vec![
//                 Term::Variable("X".to_string()),
//                 Term::Variable("Y".to_string()),
//             ],
//             sign: true,
//         };

//         // Pattern matching "parent(john, mary)"
//         let pattern = vec![
//             Some(TypedValue::from("john")),
//             Some(TypedValue::from("mary")),
//         ];

//         let results = evaluator.match_base_predicate(&atom, &pattern);
//         assert_eq!(results.len(), 1);
//         assert!(
//             results
//                 .iter()
//                 .any(|r| r[0] == TypedValue::from("john") && r[1] == TypedValue::from("mary"))
//         );
//     }

//     #[test]
//     fn test_match_base_predicate_partial_match() {
//         let evaluator = SubsumptiveEvaluator::new(
//             setup_storage(),
//             RelationStorage::default(),
//             Program::default(),
//         );

//         let atom = Atom {
//             symbol: "parent".to_string(),
//             terms: vec![
//                 Term::Variable("X".to_string()),
//                 Term::Variable("Y".to_string()),
//             ],
//             sign: true,
//         };

//         // Pattern matching "parent(john, _)"
//         let pattern = vec![Some(TypedValue::from("john")), None];

//         let results = evaluator.match_base_predicate(&atom, &pattern);
//         assert_eq!(results.len(), 2); // Should match both of John's children
//         assert!(
//             results
//                 .iter()
//                 .any(|r| r[0] == TypedValue::from("john") && r[1] == TypedValue::from("mary"))
//         );
//         assert!(
//             results
//                 .iter()
//                 .any(|r| r[0] == TypedValue::from("john") && r[1] == TypedValue::from("bob"))
//         );
//     }

//     #[test]
//     fn test_match_base_predicate_all_free() {
//         let evaluator = SubsumptiveEvaluator::new(
//             setup_storage(),
//             RelationStorage::default(),
//             Program::default(),
//         );

//         let atom = Atom {
//             symbol: "parent".to_string(),
//             terms: vec![
//                 Term::Variable("X".to_string()),
//                 Term::Variable("Y".to_string()),
//             ],
//             sign: true,
//         };

//         // Pattern matching "parent(_, _)"
//         let pattern = vec![None, None];

//         let results = evaluator.match_base_predicate(&atom, &pattern);
//         assert_eq!(results.len(), 3); // Should match all parent facts
//     }

//     #[test]
//     fn test_match_base_predicate_no_matches() {
//         let evaluator = SubsumptiveEvaluator::new(
//             setup_storage(),
//             RelationStorage::default(),
//             Program::default(),
//         );

//         let atom = Atom {
//             symbol: "parent".to_string(),
//             terms: vec![
//                 Term::Variable("X".to_string()),
//                 Term::Variable("Y".to_string()),
//             ],
//             sign: true,
//         };

//         // Pattern matching "parent(unknown, _)"
//         let pattern = vec![Some(TypedValue::from("unknown")), None];

//         let results = evaluator.match_base_predicate(&atom, &pattern);
//         assert_eq!(results.len(), 0); // Should find no matches
//     }

//     #[test]
//     fn test_match_base_predicate_nonexistent_predicate() {
//         let evaluator = SubsumptiveEvaluator::new(
//             setup_storage(),
//             RelationStorage::default(),
//             Program::default(),
//         );

//         let atom = Atom {
//             symbol: "nonexistent".to_string(),
//             terms: vec![
//                 Term::Variable("X".to_string()),
//                 Term::Variable("Y".to_string()),
//             ],
//             sign: true,
//         };

//         let pattern = vec![None, None];

//         let results = evaluator.match_base_predicate(&atom, &pattern);
//         assert_eq!(results.len(), 0); // Should return empty set for nonexistent predicate
//     }
// }
