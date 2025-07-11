use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::engine::storage::RelationStorage;
use crate::helpers::helpers::is_derived_predicate;
use crate::helpers::subsumptive_helpers::{
    create_result, create_subquery_pattern, update_bindings,
};
use datalog_syntax::*;

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

    pub fn evaluate_query<'b>(&self, query: &'b Query) -> (Vec<Vec<TypedValue>>, Duration) {
        println!("Evaluating query: {:?}, {:?}", query.symbol, query.matchers);
        println!("Program: {:?}", self.program.inner);
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

        // Create an Atom object from the query
        let atom = Atom {
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

        // Evaluate the query using subsumptive tabling
        let results: Vec<Vec<TypedValue>> = self.evaluate_subquery(
            &atom,
            &pattern,
            &mut table,
            &mut seen_queries,
            0, // Start with depth 0
        );
        let evaluation_time = start.elapsed();

        // Return the results as an iterator
        return (results, evaluation_time);
    }

    pub fn evaluate_subquery(
        &self,
        subquery_atom: &Atom,
        pattern: &[Option<TypedValue>],
        table: &mut SubsumptiveTable,
        seen_queries: &mut HashSet<(String, Vec<Option<TypedValue>>)>,
        depth: usize,
    ) -> Vec<Vec<TypedValue>> {
        println!("Evaluating subquery: {:?}, {:?}", subquery_atom.symbol, pattern);
        let mut all_results = HashSet::new();
        let query_key = (subquery_atom.symbol.clone(), pattern.to_vec());

        // Prevent infinite recursion by tracking seen queries
        if seen_queries.contains(&query_key) {
            return Vec::new();
        }

        seen_queries.insert(query_key.clone());
        // Check if there are already cached results from a more general (subsuming) query
        if let Some(cached_results) = table.find_subsuming(&subquery_atom.symbol, pattern) {
            return cached_results.iter().cloned().collect();
        }

        // First, process base facts (facts in storage)
        if let Some(facts) = self.unprocessed_insertions.inner.get(&subquery_atom.symbol) {
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

            all_results.extend(matching_facts);
        }

        // Make owned copies of matching rules to avoid borrow checker issues
        let matching_rules: Vec<Rule> = self
            .program
            .inner
            .iter()
            .filter(|rule| rule.head.symbol == subquery_atom.symbol)
            .cloned()
            .collect();

        // Process each matching rule
        for rule in matching_rules {
            let mut rule_results = HashSet::new();
            self.evaluate_rule_subsumptive(
                &rule,
                pattern,
                table,
                seen_queries,
                &mut rule_results,
                depth + 1,
            );
            println!("Rule {:?} results: {:?}", rule, rule_results);
            all_results.extend(rule_results);
        }

        // Remove this query from seen set since we're done processing it
        seen_queries.remove(&query_key);

        // Cache results if we found any
        if !all_results.is_empty() {
            table.insert(
                &atom.symbol,
                pattern.to_vec(),
                all_results.iter().cloned().collect(),
            );
        }

        all_results.into_iter().collect()
    }

    fn evaluate_rule_subsumptive(
        &self,
        rule: &Rule,
        head_pattern: &[Option<TypedValue>],
        table: &mut SubsumptiveTable,
        seen_queries: &mut HashSet<(String, Vec<Option<TypedValue>>)>,
        results: &mut HashSet<AnonymousGroundAtom>,
        depth: usize,
    ) -> () {
        println!("Evaluating rule: {:?}, {:?}", rule.head.symbol, head_pattern);

        // Create a variable binding map to track bound variables
        let mut bindings = HashMap::new();

        // Initialize bindings from the head pattern
        for (i, arg) in rule.head.terms.iter().enumerate() {
            if let (Term::Variable(var), Some(val)) =
                (arg, head_pattern.get(i).and_then(|p| p.as_ref()))
            {
                bindings.insert(var.clone(), val.clone());
            }
        }

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

        result
    }

    fn evaluate_body(
        &self,
        body: &[Atom],
        head: &Atom,
        pos: usize,
        bindings: &mut HashMap<String, TypedValue>,
        table: &mut SubsumptiveTable,
        seen_queries: &mut HashSet<(String, Vec<Option<TypedValue>>)>,
        results: &mut HashSet<AnonymousGroundAtom>,
        depth: usize,
    ) -> () {
        //println!("Evaluating body: {:?}, {:?}", body, head);
        let indent = "  ".repeat(depth);

        // Base case: all body atoms have been processed
        if pos >= body.len() {
            if let Some(result) = create_result(head, bindings) {
                results.insert(result);
            }
            return; // Exit here
        }

        let atom = &body[pos];

        // Create a subquery pattern based on current bindings
        let pattern = create_subquery_pattern(atom, bindings);

        let mut subresults: Vec<Vec<TypedValue>> = Vec::new();

        if is_derived_predicate(&self.program, &atom.symbol) {
            subresults = self.evaluate_subquery(atom, &pattern, table, seen_queries, depth + 1);
        } else {
            subresults = self
                .match_base_predicate(atom, &pattern)
                .into_iter()
                .collect();
        }

        for subresult in subresults {
            let mut new_bindings = bindings.clone();
            let subresult_set = HashSet::from_iter(vec![subresult.clone()]);
            update_bindings(&mut new_bindings, atom, &subresult_set);

            self.evaluate_body(
                body,
                head,
                pos + 1,
                &mut new_bindings,
                table,
                seen_queries,
                results,
                depth + 1,
            );
        }
    }

    fn match_base_predicate(
        &self,
        atom: &Atom,
        pattern: &[Option<TypedValue>],
    ) -> HashSet<AnonymousGroundAtom> {
        let mut results = HashSet::new();

        if let Some(facts) = self.processed.inner.get(&atom.symbol) {
            for fact in facts {
                let matches = fact.iter().zip(pattern.iter()).all(|(val, pat)| match pat {
                    Some(bound_val) => {
                        let matches = val == bound_val;

                        matches
                    }
                    None => true,
                });

                if matches {
                    results.insert((**fact).clone());
                }
            }
        } else {
        }

        if let Some(facts) = self.unprocessed_insertions.inner.get(&atom.symbol) {
            for fact in facts {
                let matches = fact.iter().zip(pattern.iter()).all(|(val, pat)| match pat {
                    Some(bound_val) => {
                        let matches = val == bound_val;

                        matches
                    }
                    None => true,
                });

                if matches {
                    results.insert((**fact).clone());
                }
            }
        }

        results
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

        let results = evaluator.match_base_predicate(&atom, &pattern);
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

        let results = evaluator.match_base_predicate(&atom, &pattern);
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

        let results = evaluator.match_base_predicate(&atom, &pattern);
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

        let results = evaluator.match_base_predicate(&atom, &pattern);
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

        let results = evaluator.match_base_predicate(&atom, &pattern);
        assert_eq!(results.len(), 0); // Should return empty set for nonexistent predicate
    }
}
