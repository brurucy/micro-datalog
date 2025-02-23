use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::engine::storage::RelationStorage;
use crate::helpers::helpers::is_derived_predicate;
use crate::helpers::subsumptive_helpers::{
    create_result, create_subquery_pattern, update_bindings,
};
use datalog_syntax::*;

use super::datalog::MicroRuntime;
use super::subsumptive_table::SubsumptiveTable;

pub struct SubsumptiveEvaluator {
    processed: RelationStorage,
    unprocessed_insertions: RelationStorage,
    program: Program,
}

impl<'a> SubsumptiveEvaluator {
    pub fn new(processed: RelationStorage, unprocessed: RelationStorage, program: Program) -> Self {
        Self {
            processed,
            unprocessed_insertions: unprocessed,
            program,
        }
    }

    pub fn evaluate_query<'b>(
        &mut self,
        query: &'b Query,
    ) -> Result<impl Iterator<Item = AnonymousGroundAtom> + 'a, String> {
        println!("Query: {}({:?})", query.symbol, query.matchers);
        let mut table = SubsumptiveTable::new();
        let mut seen_queries = HashSet::new();

        // Convert query to pattern
        // For each matcher, create Some(value) for constants and None for Any
        let pattern: Vec<Option<TypedValue>> = query
            .matchers
            .iter()
            .map(|m| match m {
                Matcher::Any => None,
                Matcher::Constant(val) => Some(val.clone()),
            })
            .collect();
        println!("Initial Pattern: {:?}", pattern);

        // Create an Atom object from the query
        let atom = Atom {
            symbol: query.symbol.to_string(),
            terms: query
                .matchers
                .iter()
                .map(|_| Term::Variable("_".to_string()))
                .collect(),
            sign: true,
        };

        // Evaluate the query using subsumptive tabling
        let results = self.evaluate_subquery(
            &atom,
            &pattern,
            &mut table,
            &mut seen_queries,
            0, // Start with depth 0
        )?;

        println!("\n=== Final Results ===");
        println!("Results: {:?}", results);
        println!("Table Contents:");
        table.print_contents();

        // Return the results as an iterator
        Ok(results.into_iter())
    }

    fn evaluate_subquery(
        &mut self,
        atom: &Atom,
        pattern: &[Option<TypedValue>],
        table: &mut SubsumptiveTable,
        seen_queries: &mut HashSet<(String, Vec<Option<TypedValue>>)>,
        depth: usize,
    ) -> Result<HashSet<AnonymousGroundAtom>, String> {
        let indent = "  ".repeat(depth);
        println!("\n{}=== Evaluating Subquery (Depth {}) ===", indent, depth);
        println!("{}Predicate: {}", indent, atom.symbol);
        println!("{}Pattern: {:?}", indent, pattern);

        // Check if there are already cached results from a more general (subsuming) query
        if let Some(cached_results) = table.find_subsuming(&atom.symbol, pattern) {
            println!(
                "{}Found cached results: {:?}",
                "  ".repeat(depth),
                cached_results
            );

            return Ok(cached_results.iter().cloned().collect());
        }

        let mut all_results = HashSet::new();
        let query_key = (atom.symbol.clone(), pattern.to_vec());

        // Prevent infinite recursion by tracking seen queries
        if seen_queries.contains(&query_key) {
            println!(
                "{}Detected recursion, returning empty set",
                "  ".repeat(depth)
            );

            return Ok(all_results);
        }
        seen_queries.insert(query_key.clone());

        // First, process base facts (facts in storage)
        if let Some(facts) = self.unprocessed_insertions.inner.get(&atom.symbol) {
            println!(
                "{}Processing base facts for {}",
                "  ".repeat(depth),
                atom.symbol
            );
            let matching_facts: HashSet<_> = facts
                .iter()
                .filter(|fact| {
                    fact.iter()
                        .zip(pattern)
                        .all(|(val, pattern_val)| match pattern_val {
                            Some(bound_val) => val == bound_val,
                            None => true,
                        })
                })
                .map(|arc_fact| (**arc_fact).clone())
                .collect();
            println!(
                "{}Matching base facts: {:?}",
                "  ".repeat(depth),
                matching_facts
            );
            all_results.extend(matching_facts);
        }

        // Make owned copies of matching rules to avoid borrow checker issues
        let matching_rules: Vec<Rule> = self
            .program
            .inner
            .iter()
            .filter(|rule| rule.head.symbol == atom.symbol)
            .cloned()
            .collect();

        // Process each matching rule
        println!("{}Processing rules", "  ".repeat(depth));
        for rule in matching_rules {
            println!("{}Evaluating rule: {:?}", "  ".repeat(depth), rule);
            let mut rule_results = HashSet::new();
            self.evaluate_rule_subsumptive(
                &rule,
                pattern,
                table,
                seen_queries,
                &mut rule_results,
                depth + 1,
            )?;
            println!("{}Rule results: {:?}", "  ".repeat(depth), rule_results);
            all_results.extend(rule_results);
        }

        // Remove this query from seen set since we're done processing it
        seen_queries.remove(&query_key);

        // Cache results if we found any
        if !all_results.is_empty() {
            println!("{}Caching results for future use", "  ".repeat(depth));
            table.insert(
                &atom.symbol,
                pattern.to_vec(),
                all_results.iter().cloned().collect(),
            );
        }

        println!("{}Final results: {:?}", "  ".repeat(depth), all_results);
        Ok(all_results)
    }

    fn evaluate_rule_subsumptive(
        &mut self,
        rule: &Rule,
        head_pattern: &[Option<TypedValue>],
        table: &mut SubsumptiveTable,
        seen_queries: &mut HashSet<(String, Vec<Option<TypedValue>>)>,
        results: &mut HashSet<AnonymousGroundAtom>,
        depth: usize,
    ) -> Result<(), String> {
        let indent = "  ".repeat(depth);
        println!("\n{}=== Evaluating Rule Subsumptive ===", indent);
        println!("{}Rule: {:?}", indent, rule);
        println!("{}Head Pattern: {:?}", indent, head_pattern);

        // Create a variable binding map to track bound variables
        let mut bindings = HashMap::new();

        // Initialize bindings from the head pattern
        for (i, arg) in rule.head.terms.iter().enumerate() {
            if let (Term::Variable(var), Some(val)) =
                (arg, head_pattern.get(i).and_then(|p| p.as_ref()))
            {
                bindings.insert(var.clone(), val.clone());
                println!("{}Binding variable {} to value {:?}", indent, var, val);
            }
        }

        println!("{}Initial bindings: {:?}", indent, bindings);

        // Evaluate each body atom in sequence
        let result = self.evaluate_body(
            &rule.body,
            &rule.head,
            0,
            &mut bindings,
            table,
            seen_queries,
            results,
            depth + 1,
        );

        println!("{}=== Rule evaluation complete ===", indent);
        println!("{}Final results size: {}", indent, results.len());

        result
    }

    fn evaluate_body(
        &mut self,
        body: &[Atom],
        head: &Atom,
        pos: usize,
        bindings: &mut HashMap<String, TypedValue>,
        table: &mut SubsumptiveTable,
        seen_queries: &mut HashSet<(String, Vec<Option<TypedValue>>)>,
        results: &mut HashSet<AnonymousGroundAtom>,
        depth: usize,
    ) -> Result<(), String> {
        let indent = "  ".repeat(depth);
        println!("\n{}=== Evaluating Body at position {} ===", indent, pos);
        println!("{}Current bindings: {:?}", indent, bindings);

        if pos >= body.len() {
            println!("{}Reached end of body, creating result...", indent);
            if let Some(result) = create_result(head, bindings) {
                println!("{}Adding result: {:?}", indent, result);
                results.insert(result);
            } else {
                println!("{}Could not create result - incomplete bindings", indent);
            }
            return Ok(());
        }

        let atom = &body[pos];
        println!("{}Processing atom: {:?}", indent, atom);

        // Create a subquery pattern based on current bindings
        let pattern = create_subquery_pattern(atom, bindings);
        println!("{}Created subquery pattern: {:?}", indent, pattern);

        // For base predicates, directly match against facts
        if !is_derived_predicate(&self.program, &atom.symbol) {
            println!("{}Processing base predicate", indent);
            let base_results = self.match_base_predicate(atom, &pattern)?;
            println!("{}Found {} base results", indent, base_results.len());

            for base_result in base_results {
                println!("{}Processing base result: {:?}", indent, base_result);
                let mut new_bindings = bindings.clone();
                update_bindings(
                    &mut new_bindings,
                    atom,
                    &HashSet::from_iter(vec![base_result.clone()]),
                );
                println!("{}Updated bindings: {:?}", indent, new_bindings);

                self.evaluate_body(
                    body,
                    head,
                    pos + 1,
                    &mut new_bindings,
                    table,
                    seen_queries,
                    results,
                    depth + 1,
                )?;
            }
        } else {
            println!("{}Processing derived predicate", indent);
            let atom_obj = Atom {
                symbol: atom.symbol.clone(),
                terms: atom.terms.clone(),
                sign: atom.sign,
            };

            let subresults =
                self.evaluate_subquery(&atom_obj, &pattern, table, seen_queries, depth + 1)?;
            println!("{}Found {} derived results", indent, subresults.len());

            for subresult in subresults {
                println!("{}Processing derived result: {:?}", indent, subresult);
                let mut new_bindings = bindings.clone();
                let subresult_set = HashSet::from_iter(vec![subresult.clone()]);
                update_bindings(&mut new_bindings, atom, &subresult_set);
                println!("{}Updated bindings: {:?}", indent, new_bindings);

                self.evaluate_body(
                    body,
                    head,
                    pos + 1,
                    &mut new_bindings,
                    table,
                    seen_queries,
                    results,
                    depth + 1,
                )?;
            }
        }

        println!(
            "{}=== Completed body evaluation at position {} ===",
            indent, pos
        );
        Ok(())
    }

    fn match_base_predicate(
        &self,
        atom: &Atom,
        pattern: &[Option<TypedValue>],
    ) -> Result<HashSet<AnonymousGroundAtom>, String> {
        println!("\n=== Matching Base Predicate ===");
        println!("Atom: {:?}", atom);
        println!("Pattern: {:?}", pattern);

        let mut results = HashSet::new();

        if let Some(facts) = self.processed.inner.get(&atom.symbol) {
            println!("Found {} facts in storage for {}", facts.len(), atom.symbol);

            for fact in facts {
                let matches = fact.iter().zip(pattern.iter()).all(|(val, pat)| match pat {
                    Some(bound_val) => {
                        let matches = val == bound_val;
                        if !matches {
                            println!("Value {:?} doesn't match bound value {:?}", val, bound_val);
                        }
                        matches
                    }
                    None => true,
                });

                if matches {
                    println!("Found matching fact: {:?}", fact);
                    results.insert((**fact).clone());
                }
            }
        } else {
            println!("No facts found for predicate {}", atom.symbol);
        }

        if let Some(facts) = self.unprocessed_insertions.inner.get(&atom.symbol) {
            println!("Found {} facts in unprocessed storage for {}", facts.len(), atom.symbol);

            for fact in facts {
                let matches = fact.iter().zip(pattern.iter()).all(|(val, pat)| match pat {
                    Some(bound_val) => {
                        let matches = val == bound_val;
                        if !matches {
                            println!("Value {:?} doesn't match bound value {:?}", val, bound_val);
                        }
                        matches
                    }
                    None => true,
                });

                if matches {
                    println!("Found matching fact: {:?}", fact);
                    results.insert((**fact).clone());
                }
            }
        } else {
            println!("No facts found for predicate {}", atom.symbol);
        }

        println!("Total matches found: {}", results.len());
        Ok(results)
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn setup_storage() -> RelationStorage {
        let mut storage = RelationStorage::default();

        // Insert some test facts into parent relation
        storage
            .inner
            .insert("parent".to_string(), Default::default());
        let parent_facts = vec![
            vec![TypedValue::from("john"), TypedValue::from("mary")],
            vec![TypedValue::from("john"), TypedValue::from("bob")],
            vec![TypedValue::from("mary"), TypedValue::from("ann")],
        ];
        for fact in parent_facts {
            storage
                .inner
                .get_mut("parent")
                .unwrap()
                .insert(Arc::new(fact));
        }
        storage
    }

    #[test]
    fn test_match_base_predicate_exact_match() {
        let evaluator = SubsumptiveEvaluator::new(
            setup_storage(),
            RelationStorage::default(),
            Program::default(),
        );

        let atom = Atom {
            symbol: "parent".to_string(),
            terms: vec![
                Term::Variable("X".to_string()),
                Term::Variable("Y".to_string()),
            ],
            sign: true,
        };

        // Pattern matching "parent(john, mary)"
        let pattern = vec![
            Some(TypedValue::from("john")),
            Some(TypedValue::from("mary")),
        ];

        let results = evaluator.match_base_predicate(&atom, &pattern).unwrap();
        assert_eq!(results.len(), 1);
        assert!(results
            .iter()
            .any(|r| r[0] == TypedValue::from("john") && r[1] == TypedValue::from("mary")));
    }

    #[test]
    fn test_match_base_predicate_partial_match() {
        let evaluator = SubsumptiveEvaluator::new(
            setup_storage(),
            RelationStorage::default(),
            Program::default(),
        );

        let atom = Atom {
            symbol: "parent".to_string(),
            terms: vec![
                Term::Variable("X".to_string()),
                Term::Variable("Y".to_string()),
            ],
            sign: true,
        };

        // Pattern matching "parent(john, _)"
        let pattern = vec![Some(TypedValue::from("john")), None];

        let results = evaluator.match_base_predicate(&atom, &pattern).unwrap();
        assert_eq!(results.len(), 2); // Should match both of John's children
        assert!(results
            .iter()
            .any(|r| r[0] == TypedValue::from("john") && r[1] == TypedValue::from("mary")));
        assert!(results
            .iter()
            .any(|r| r[0] == TypedValue::from("john") && r[1] == TypedValue::from("bob")));
    }

    #[test]
    fn test_match_base_predicate_all_free() {
        let evaluator = SubsumptiveEvaluator::new(
            setup_storage(),
            RelationStorage::default(),
            Program::default(),
        );

        let atom = Atom {
            symbol: "parent".to_string(),
            terms: vec![
                Term::Variable("X".to_string()),
                Term::Variable("Y".to_string()),
            ],
            sign: true,
        };

        // Pattern matching "parent(_, _)"
        let pattern = vec![None, None];

        let results = evaluator.match_base_predicate(&atom, &pattern).unwrap();
        assert_eq!(results.len(), 3); // Should match all parent facts
    }

    #[test]
    fn test_match_base_predicate_no_matches() {
        let evaluator = SubsumptiveEvaluator::new(
            setup_storage(),
            RelationStorage::default(),
            Program::default(),
        );

        let atom = Atom {
            symbol: "parent".to_string(),
            terms: vec![
                Term::Variable("X".to_string()),
                Term::Variable("Y".to_string()),
            ],
            sign: true,
        };

        // Pattern matching "parent(unknown, _)"
        let pattern = vec![Some(TypedValue::from("unknown")), None];

        let results = evaluator.match_base_predicate(&atom, &pattern).unwrap();
        assert_eq!(results.len(), 0); // Should find no matches
    }

    #[test]
    fn test_match_base_predicate_nonexistent_predicate() {
        let evaluator = SubsumptiveEvaluator::new(
            setup_storage(),
            RelationStorage::default(),
            Program::default(),
        );

        let atom = Atom {
            symbol: "nonexistent".to_string(),
            terms: vec![
                Term::Variable("X".to_string()),
                Term::Variable("Y".to_string()),
            ],
            sign: true,
        };

        let pattern = vec![None, None];

        let results = evaluator.match_base_predicate(&atom, &pattern).unwrap();
        assert_eq!(results.len(), 0); // Should return empty set for nonexistent predicate
    }
}
