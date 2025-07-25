use std::collections::{HashMap, HashSet};
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
        let start = Instant::now();

        let mut seen_queries = HashSet::new();
        let mut table = SubsumptiveTable::new();
        let mut results: Vec<Vec<TypedValue>> = self.evaluate_subquery(
            self.program.clone(),
            &query_atom,
            None,
            &mut seen_queries,
            &mut table,
            None,
            0, // Start with depth 0
        );

        // while !self.unprocessed_subqueries.is_empty() {
        //     let mut new_unprocessed_subqueries = self.unprocessed_subqueries.clone();
        //     for (depth, subqueries) in new_unprocessed_subqueries.iter_mut() {
        //         for (subquery_atom, (subquery_rule, bindings)) in subqueries.iter() {
        //             let mut subquery_results = HashSet::new();
        //             let bindings_hacked = HashMap::from([
        //                 ("z".to_string(), TypedValue::from("d")),
        //             ]);
        //             self.evaluate_unprocessed_subquery(
        //                 subquery_atom,
        //                 subquery_rule,
        //                 &bindings_hacked,
        //                 &mut seen_queries,
        //                 &mut table,
        //                 &mut subquery_results,
        //                 0,
        //                 depth + 1,
        //             );

        //             results.extend(subquery_results);
        //         }
        //         self.unprocessed_subqueries.remove(depth);
        //     }
        // }
        let evaluation_time = start.elapsed();

        //Return the results as an iterator
        return (results, evaluation_time);
    }

    pub fn evaluate_subquery(
        &mut self,
        program: Program,
        subquery_atom: &Atom,
        subquery_rule: Option<&Rule>,
        seen_queries: &mut HashSet<Atom>,
        table: &mut SubsumptiveTable,
        bindings: Option<HashMap<String, TypedValue>>,
        depth: usize,
    ) -> Vec<Vec<TypedValue>> {
        let mut current_subquery_atom: Atom;

        if let Some(existing_bindings) = bindings.clone() {
            let new_subquery_atom_terms = subquery_atom
                .terms
                .iter()
                .map(|term| {
                    if let Term::Variable(var) = term {
                        if let Some(bound_value) = existing_bindings.get(var) {
                            Term::Constant(bound_value.clone())
                        } else {
                            term.clone()
                        }
                    } else {
                        term.clone()
                    }
                })
                .collect();

            current_subquery_atom = Atom {
                symbol: subquery_atom.symbol.clone(),
                sign: subquery_atom.sign,
                terms: new_subquery_atom_terms,
            };
        } else {
            current_subquery_atom = subquery_atom.clone();
        }

        let mut all_results = HashSet::new();
        if let Some(cached_results) = table.find_subsuming(&current_subquery_atom) {
            return cached_results.iter().cloned().collect();
        }

        //Prevent infinite recursion by tracking seen queries
        if seen_queries.contains(&current_subquery_atom) {
            println!("================================================");
            println!("Found seen query {:?}", current_subquery_atom);
            println!("Subquery rule {:?}", subquery_rule);
            println!("Depth {:?}", depth);
            //println!("Bindings {:?}", bindings.unwrap());
            println!("================================================");
            self.insert_unprocessed_subquery(
                &current_subquery_atom,
                subquery_rule.unwrap().clone(),
                HashMap::new(), // TODO: This is a hack to get the subresult set. We should find a better way to do this.
                depth,
            );

            return Vec::new();
        }

        seen_queries.insert(current_subquery_atom.clone());

        //First, process base facts (facts in storage)
        if let Some(facts) = self
            .unprocessed_insertions
            .inner
            .get(&current_subquery_atom.symbol)
        {
            let matching_facts: HashSet<_> = facts
                .iter()
                .filter(|fact| {
                    fact.iter().zip(current_subquery_atom.terms.iter()).all(
                        |(val, term)| match term {
                            Term::Constant(bound_val) => val == bound_val,
                            Term::Variable(_) => true,
                        },
                    )
                })
                .map(|arc_fact| (**arc_fact).clone())
                .collect();

            all_results.extend(matching_facts);
        }

        if let Some(facts) = self.processed.inner.get(&current_subquery_atom.symbol) {
            let matching_facts: HashSet<_> = facts
                .iter()
                .filter(|fact| {
                    fact.iter().zip(current_subquery_atom.terms.iter()).all(
                        |(val, term)| match term {
                            Term::Constant(bound_val) => val == bound_val,
                            Term::Variable(_) => true,
                        },
                    )
                })
                .map(|arc_fact| (**arc_fact).clone())
                .collect();

            all_results.extend(matching_facts);
        }

        //Process each matching rule
        for rule in program.inner.iter() {
            if rule.head.symbol != current_subquery_atom.symbol {
                continue;
            }
            let mut rule_results = HashSet::new();
            let mut new_subquery_terms = Vec::new();

            // Check if rule is compatible with subquery
            let mut is_compatible = true;
            for (rule_term, subquery_term) in rule
                .head
                .terms
                .iter()
                .zip(current_subquery_atom.terms.iter())
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

            if let Some(existing_bindings) = &bindings {
                new_subquery_terms = new_subquery_terms.iter().map(|term| {
                    if let Term::Variable(var) = term {
                        if let Some(bound_value) = existing_bindings.get(var) {
                            Term::Constant(bound_value.clone())
                        } else {
                            term.clone()
                        }
                    } else {
                        term.clone()
                    }
                }).collect();
            }

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
                symbol: current_subquery_atom.symbol.clone(),
                sign: current_subquery_atom.sign,
                terms: new_subquery_terms,
            };

            // if next_subquery_atom.terms[0] == Term::Variable("x".to_string()) && next_subquery_atom.terms[1] == Term::Variable("y".to_string()) && depth == 3 {
            //     println!("================================================");
            //     println!("wazzup 2");
            //     println!("Bindings {:?}", bindings.as_ref().unwrap());
            //     println!("Evaluating rule {:?}", rule);
            //     println!("current subquery atom {:?}", current_subquery_atom);
            //     println!("Next subquery atom {:?}", next_subquery_atom);
            //     println!("================================================");
            // }

            self.evaluate_rule_subsumptive(
                &next_subquery_atom,
                &rule,
                bindings.clone(),
                seen_queries,
                table,
                &mut rule_results,
                depth + 1,
            );
            all_results.extend(rule_results);
        }

        //Cache results if we found any
        if !all_results.is_empty() {
            println!(
                "Inserting results for subquery atom {:?} at depth {:?}",
                current_subquery_atom, depth
            );
            println!("Results {:?}", all_results);
            table.insert(
                &current_subquery_atom,
                all_results.iter().cloned().collect(),
            );
        }

        //Remove this query from seen set since we're done processing it
        seen_queries.remove(&current_subquery_atom);
        all_results.into_iter().collect()
    }

    fn evaluate_rule_subsumptive(
        &mut self,
        subquery_atom: &Atom,
        rule: &Rule,
        bindings: Option<HashMap<String, TypedValue>>,
        seen_queries: &mut HashSet<Atom>,
        table: &mut SubsumptiveTable,
        results: &mut HashSet<AnonymousGroundAtom>,
        depth: usize,
    ) -> () {
        let mut new_bindings: HashMap<String, TypedValue>;
        if let Some(existing_bindings) = &bindings {
            new_bindings = existing_bindings.clone();
        } else {
            new_bindings = HashMap::new();
        }

        //Initialize bindings from the head pattern
        for (i, arg) in rule.head.terms.iter().enumerate() {
            if let (Term::Variable(var), Some(Term::Constant(val))) =
                (arg, subquery_atom.terms.get(i))
            {
                new_bindings.insert(var.clone(), val.clone());
            }
        }

        //Evaluate each body atom in sequence
        self.evaluate_body(
            &rule,
            0,
            &mut new_bindings,
            seen_queries,
            table,
            results,
            depth + 1,
        );
    }

    fn evaluate_body(
        &mut self,
        subquery_rule: &Rule,
        pos: usize,
        bindings: &mut HashMap<String, TypedValue>,
        seen_queries: &mut HashSet<Atom>,
        table: &mut SubsumptiveTable,
        results: &mut HashSet<AnonymousGroundAtom>,
        depth: usize,
    ) -> () {
        let body = &subquery_rule.body;
        let head = &subquery_rule.head;

        // Base case: all body atoms have been processed
        if pos >= body.len() {
            if let Some(result) = create_result(head, bindings) {
                results.insert(result);
            }
            return;
        }

        let subquery_atom = Atom {
            symbol: body[pos].symbol.clone(),
            sign: body[pos].sign,
            terms: body[pos]
                .terms
                .iter()
                .map(|term| match term {
                    Term::Variable(var) => {
                        if let Some(bound_value) = bindings.get(var) {
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

        if is_derived_predicate(&self.program, &subquery_atom.symbol) {
        
                println!("================================================");
                println!("Evaluating derived predicate {:?}", subquery_atom);
                println!("Bindings {:?}", bindings);
                println!("Subquery rule {:?}", subquery_rule);
                println!("Pos {:?}", pos);
                println!("Results {:?}", results);
                println!("Depth {:?}", depth);
                println!("================================================");
            

            // we moving out of this rule
            let new_query_atom = Atom {
                symbol: subquery_atom.symbol.clone(),
                sign: subquery_atom.sign,
                terms: subquery_atom.terms.iter().map(|term| 
                    match term {
                        Term::Variable(var) => {
                            if let Some(bound_value) = bindings.get(var) {
                                Term::Constant(bound_value.clone())
                            } else {
                            Term::Variable("_".to_string())
                        }
                    },
                    Term::Constant(_) => term.clone(),
                }).collect()
            };

            subresults = self.evaluate_subquery(
                self.program.clone(),
                &new_query_atom,
                Some(subquery_rule),
                seen_queries,
                table,
                None,
                depth + 1,
            );

            subresults = subresults
                .iter()
                .filter(|subresult| {
                    subresult.iter().enumerate().all(|(i, res)| {
                        match &subquery_atom.terms[i] {
                            Term::Constant(atom_val) => res == atom_val,
                            Term::Variable(_) => true,
                        }
                    })
                })
                .cloned()
                .collect();


        } else {
            subresults = self
                .match_base_predicate(&subquery_atom)
                .into_iter()
                .collect();
         
        }

        for subresult in subresults {
            let mut new_bindings = bindings.clone();
            let subresult_set = HashSet::from_iter(vec![subresult.clone()]);
            update_bindings(&mut new_bindings, &subquery_atom, &subresult_set);

            self.evaluate_body(
                subquery_rule,
                pos + 1,
                &mut new_bindings,
                seen_queries,
                table,
                results,
                depth + 1,
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
        let subresults = self.evaluate_subquery(
            self.program.clone(),
            &subquery_atom,
            Some(subquery_rule),
            seen_queries,
            table,
            Some(bindings.clone()),
            depth,
        );

        for subresult in subresults {
            let mut new_bindings = bindings.clone();
            // TODO: This is a hack to get the subresult set. We should find a better way to do this.
            let subresult_set = HashSet::from_iter(vec![subresult.clone()]);
            update_bindings(&mut new_bindings, &subquery_atom, &subresult_set);
            self.evaluate_body(
                subquery_rule,
                pos + 1,
                &mut new_bindings,
                seen_queries,
                table,
                results,
                depth,
            );
        }
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
        subquery_atom: &Atom,
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
        atoms_at_depth.insert(subquery_atom.clone(), (subquery_rule, bindings.clone()));
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
