use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

use crate::engine::storage::RelationStorage;
use crate::helpers::helpers::is_derived_predicate;
use crate::helpers::subsumptive_helpers::{create_result, update_bindings};
use datalog_syntax::*;

use super::subsumptive_table::SubsumptiveTable;

pub struct SubsumptiveEvaluator {
    processed: RelationStorage,
    unprocessed_insertions: RelationStorage,
    program: Program,
}

impl SubsumptiveEvaluator {
    pub fn new(processed: RelationStorage, unprocessed: RelationStorage, program: Program) -> Self {
        Self {
            processed,
            unprocessed_insertions: unprocessed,
            program,
        }
    }

    pub fn evaluate_query<'b>(&self, query: &'b Query) -> (Vec<Vec<TypedValue>>, Duration) {
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

        // Only need to track queries currently being computed (for infinite recursion prevention)
        let mut computing_queries = HashSet::new();
        let mut table = SubsumptiveTable::new();

        let results: Vec<Vec<TypedValue>> =
            self.evaluate_subquery(&query_atom, &mut computing_queries, &mut table, 0);
        let evaluation_time = start.elapsed();

        (results, evaluation_time)
    }

    pub fn evaluate_subquery(
        &self,
        subquery_atom: &Atom,
        computing_queries: &mut HashSet<Atom>,
        table: &mut SubsumptiveTable,
        depth: usize,
    ) -> Vec<Vec<TypedValue>> {
        // STEP 1: Check for subsuming cached results (core of subsumptive tabling)
        if let Some(cached_results) = table.find_subsuming(&subquery_atom) {
            return cached_results.iter().cloned().collect();
        }

        // STEP 2: Prevent infinite recursion for exact same query
        if computing_queries.contains(&subquery_atom) {
            println!(
                "Subquery atom seen {:?} at depth {:?}",
                subquery_atom, depth
            );
            // We're already computing this exact query - return empty to avoid infinite recursion
            // This is safe because we're using "no early completion" - we'll get the full results
            // when the computation completes
            return Vec::new();
        }

        // STEP 3: Mark this query as being computed
        computing_queries.insert(subquery_atom.clone());

        // STEP 4: Compute ALL results for this subquery (no early completion)
        let mut all_results = HashSet::new();

        // Process base facts first
        self.collect_base_facts(&subquery_atom, &mut all_results);

        // Process all relevant rules (depth-first scheduling)
        for rule in self.program.inner.iter() {
            if rule.head.symbol != subquery_atom.symbol {
                continue;
            }

            self.process_rule_for_subquery(
                &subquery_atom,
                &rule,
                computing_queries,
                table,
                &mut all_results,
                depth,
            );
        }

        // STEP 5: Cache the complete results in the table
        let result_vec: Vec<AnonymousGroundAtom> = all_results.iter().cloned().collect();
        if subquery_atom.terms[0] == Term::Constant(TypedValue::from(2)) {
            println!(
                "Inserting results for subquery atom {:?} at depth {:?}",
                subquery_atom, depth
            );
            println!("Results {:?}", all_results);
        }
        table.insert(&subquery_atom, result_vec.clone());

        // STEP 6: Mark this query as no longer being computed
        computing_queries.remove(&subquery_atom);

        // STEP 7: Return the complete results
        result_vec
    }

    fn collect_base_facts(
        &self,
        subquery_atom: &Atom,
        all_results: &mut HashSet<AnonymousGroundAtom>,
    ) {
        // Collect from unprocessed insertions
        if let Some(facts) = self.unprocessed_insertions.inner.get(&subquery_atom.symbol) {
            let matching_facts: HashSet<_> = facts
                .iter()
                .filter(|fact| self.fact_matches_atom(fact, subquery_atom))
                .map(|arc_fact| (**arc_fact).clone())
                .collect();
            all_results.extend(matching_facts);
        }

        // Collect from processed facts
        if let Some(facts) = self.processed.inner.get(&subquery_atom.symbol) {
            let matching_facts: HashSet<_> = facts
                .iter()
                .filter(|fact| self.fact_matches_atom(fact, subquery_atom))
                .map(|arc_fact| (**arc_fact).clone())
                .collect();
            all_results.extend(matching_facts);
        }
    }

    fn fact_matches_atom(&self, fact: &[TypedValue], atom: &Atom) -> bool {
        fact.iter()
            .zip(atom.terms.iter())
            .all(|(val, term)| match term {
                Term::Constant(bound_val) => val == bound_val,
                Term::Variable(_) => true,
            })
    }

    fn process_rule_for_subquery(
        &self,
        subquery_atom: &Atom,
        rule: &Rule,
        computing_queries: &mut HashSet<Atom>,
        table: &mut SubsumptiveTable,
        all_results: &mut HashSet<AnonymousGroundAtom>,
        depth: usize,
    ) {
        // Create compatible subquery atom for this rule
        let mut new_subquery_terms = Vec::new();
        let mut is_compatible = true;

        for (rule_term, subquery_term) in rule.head.terms.iter().zip(subquery_atom.terms.iter()) {
            match (rule_term, subquery_term) {
                // Both constants must match
                (Term::Constant(rule_val), Term::Constant(subquery_val)) => {
                    if rule_val != subquery_val {
                        is_compatible = false;
                        break;
                    } else {
                        new_subquery_terms.push(rule_term.clone());
                    }
                }
                // If rule has variable, subquery can have anything
                (Term::Variable(_), Term::Constant(_)) => {
                    new_subquery_terms.push(subquery_term.clone());
                }
                // Other cases: use rule term
                (_, _) => {
                    new_subquery_terms.push(rule_term.clone());
                }
            }
        }

        if !is_compatible {
            return;
        }

        let new_subquery_atom = Atom {
            symbol: subquery_atom.symbol.clone(),
            sign: subquery_atom.sign,
            terms: new_subquery_terms,
        };

        // Initialize bindings from head pattern
        let mut bindings = HashMap::new();
        for (i, arg) in rule.head.terms.iter().enumerate() {
            if let (Term::Variable(var), Some(Term::Constant(val))) =
                (arg, new_subquery_atom.terms.get(i))
            {
                bindings.insert(var.clone(), val.clone());
            }
        }

        // Evaluate rule body with depth-first scheduling
        let mut rule_results = HashSet::new();
        self.evaluate_body(
            &rule.body,
            &rule.head,
            0,
            &mut bindings,
            computing_queries,
            table,
            &mut rule_results,
            depth + 1,
        );

        all_results.extend(rule_results);
    }

    fn evaluate_body(
        &self,
        body: &[Atom],
        head: &Atom,
        pos: usize,
        bindings: &mut HashMap<String, TypedValue>,
        computing_queries: &mut HashSet<Atom>,
        table: &mut SubsumptiveTable,
        results: &mut HashSet<AnonymousGroundAtom>,
        depth: usize,
    ) {
        // Base case: all body atoms processed, create result
        if pos >= body.len() {
            if let Some(result) = create_result(head, bindings) {
                results.insert(result);
            }
            return;
        }

        // Create subquery for current body position
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

        // Get all results for this subquery
        let subresults: Vec<Vec<TypedValue>> =
            if is_derived_predicate(&self.program, &subquery_atom.symbol) {
                // Recursive call to subsumptive evaluator
                self.evaluate_subquery(&subquery_atom, computing_queries, table, depth + 1)
            } else {
                // Base predicate - match directly
                self.match_base_predicate(&subquery_atom)
            };

        // For each result, update bindings and continue with next body atom (depth-first)
        for subresult in subresults {
            let mut new_bindings = bindings.clone();
            let subresult_set = HashSet::from_iter(vec![subresult.clone()]);
            update_bindings(&mut new_bindings, &subquery_atom, &subresult_set);

            // Depth-first: immediately recurse to next position
            self.evaluate_body(
                body,
                head,
                pos + 1,
                &mut new_bindings,
                computing_queries,
                table,
                results,
                depth + 1,
            );
        }
    }

    fn match_base_predicate(&self, atom: &Atom) -> Vec<Vec<TypedValue>> {
        let mut results = Vec::new();

        // Check unprocessed insertions
        if let Some(facts) = self.unprocessed_insertions.inner.get(&atom.symbol) {
            for fact in facts.iter() {
                if self.fact_matches_atom(fact, atom) {
                    results.push((**fact).clone());
                }
            }
        }

        // Check processed facts
        if let Some(facts) = self.processed.inner.get(&atom.symbol) {
            for fact in facts.iter() {
                if self.fact_matches_atom(fact, atom) {
                    results.push((**fact).clone());
                }
            }
        }

        results
    }
}
