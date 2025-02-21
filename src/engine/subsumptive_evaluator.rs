use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::engine::storage::RelationStorage;
use datalog_syntax::*;

use super::datalog::MicroRuntime;
use super::subsumptive_table::{create_result, create_subquery_pattern, SubsumptiveTable};

pub struct SubsumptiveEvaluator<'a> {
    processed: &'a mut RelationStorage,
    unprocessed_insertions: &'a mut RelationStorage,
    program: Program,
}

impl<'a> SubsumptiveEvaluator<'a> {
    pub fn new(
        processed: &'a mut RelationStorage,
        unprocessed: &'a mut RelationStorage,
        program: Program,
    ) -> Self {
        Self {
            processed,
            unprocessed_insertions: unprocessed,
            program,
        }
    }

    pub fn evaluate_query<'b>(
        &mut self,
        query: &'b Query,
        program: Program,
    ) -> Result<impl Iterator<Item = AnonymousGroundAtom> + 'a, String> {
        let mut table = SubsumptiveTable::new();

        // Save current base facts
        let mut base_facts = HashMap::new();
        for (rel_name, facts) in &self.processed.inner {
            if !program
                .inner
                .iter()
                .any(|rule| rule.head.symbol == *rel_name)
            {
                let facts_vec: Vec<Arc<AnonymousGroundAtom>> = facts.iter().cloned().collect();
                if !facts_vec.is_empty() {
                    base_facts.insert(rel_name.clone(), facts_vec);
                }
            }
        }

        for (rel_name, facts) in &self.unprocessed_insertions.inner {
            if !program
                .inner
                .iter()
                .any(|rule| rule.head.symbol == *rel_name)
            {
                let facts_vec: Vec<Arc<AnonymousGroundAtom>> = facts.iter().cloned().collect();

                if !facts_vec.is_empty() {
                    base_facts
                        .entry(rel_name.clone())
                        .or_insert_with(Vec::new)
                        .extend(facts_vec);
                }
            }
        }

        // Create new runtime with original program
        let mut runtime = MicroRuntime::new(program);

        // Restore base facts
        for (rel_name, facts) in base_facts {
            runtime
                .processed
                .insert_registered(&rel_name, facts.into_iter());
        }
        // Evaluate using subsumptive tabling and collect into Vec
        let results: Vec<_> = self
            .evaluate_subsumptive(query, &mut table)?
            .into_iter()
            .collect();
        Ok(results.into_iter())
    }

    fn evaluate_rule_subsumptive(
        program: &Program,
        rule: &Rule,
        pattern: &[Option<TypedValue>],
        table: &mut SubsumptiveTable,
        seen_queries: &mut HashSet<(String, Vec<Option<TypedValue>>)>,
        results: &mut HashSet<AnonymousGroundAtom>,
        processed: &RelationStorage,
        depth: usize,
    ) -> Result<(), String> {
        // Track variable bindings through rule evaluation
        let mut bindings: HashMap<String, TypedValue> = HashMap::new();

        // Initialize bindings with any bound values from the head pattern
        for (i, term) in rule.head.terms.iter().enumerate() {
            if let (Term::Variable(var), Some(val)) = (term, pattern.get(i).unwrap()) {
                bindings.insert(var.clone(), val.clone());
            }
        }

        // Recursively evaluate each body predicate
        Self::evaluate_body_predicates(
            program,
            &rule.body,
            0,
            &mut bindings,
            table,
            seen_queries,
            results,
            rule,
            processed,
            depth,
        )?;

        Ok(())
    }

    fn evaluate_body_predicates(
        program: &Program,
        body: &[Atom],
        pos: usize,
        bindings: &mut HashMap<String, TypedValue>,
        table: &mut SubsumptiveTable,
        seen_queries: &mut HashSet<(String, Vec<Option<TypedValue>>)>,
        results: &mut HashSet<AnonymousGroundAtom>,
        rule: &Rule,
        processed: &RelationStorage,
        depth: usize,
    ) -> Result<(), String> {
        // Same implementation as before, but using static method calls
        // Base case: all body predicates processed
        if pos >= body.len() {
            if let Some(result) = create_result(&rule.head, bindings) {
                results.insert(result);
            }
            return Ok(());
        }

        let body_atom = &body[pos];
        let subquery_pattern = create_subquery_pattern(body_atom, bindings);

        let subquery_results = Self::evaluate_subquery_static(
            program,
            body_atom,
            &subquery_pattern,
            table,
            seen_queries,
            processed,
            depth + 1,
        )?;

        for result in subquery_results {
            let mut new_bindings = bindings.clone();
            for (i, term) in body_atom.terms.iter().enumerate() {
                if let Term::Variable(var) = term {
                    new_bindings.insert(var.clone(), result[i].clone());
                }
            }

            Self::evaluate_body_predicates(
                program,
                body,
                pos + 1,
                &mut new_bindings,
                table,
                seen_queries,
                results,
                rule,
                processed,
                depth,
            )?;
        }

        Ok(())
    }

    fn evaluate_subquery_static(
        program: &Program,
        atom: &Atom,
        pattern: &[Option<TypedValue>],
        table: &mut SubsumptiveTable,
        seen_queries: &mut HashSet<(String, Vec<Option<TypedValue>>)>,
        processed: &RelationStorage,
        depth: usize,
    ) -> Result<HashSet<AnonymousGroundAtom>, String> {
        // Similar to evaluate_subquery but as a static method
        let mut all_results = HashSet::new();
        let query_key = (atom.symbol.clone(), pattern.to_vec());

        if seen_queries.contains(&query_key) {
            return Ok(all_results);
        }
        seen_queries.insert(query_key.clone());

        // Check cache first
        if let Some(cached_results) = table.find_subsuming(&atom.symbol, pattern) {
            return Ok(cached_results.iter().cloned().collect());
        }

        // Process base facts
        if let Some(facts) = processed.inner.get(&atom.symbol) {
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

        // Process rules
        for rule in program
            .inner
            .iter()
            .filter(|r| r.head.symbol == atom.symbol)
        {
            let mut rule_results = HashSet::new();
            Self::evaluate_rule_subsumptive(
                program,
                rule,
                pattern,
                table,
                seen_queries,
                &mut rule_results,
                processed,
                depth + 1,
            )?;
            all_results.extend(rule_results);
        }

        seen_queries.remove(&query_key);

        // Cache results
        if !all_results.is_empty() {
            table.insert(
                &atom.symbol,
                pattern.to_vec(),
                all_results.iter().cloned().collect(),
            );
        }

        Ok(all_results)
    }

    fn evaluate_subsumptive(
        &mut self,
        query: &Query,
        table: &mut SubsumptiveTable,
    ) -> Result<Vec<AnonymousGroundAtom>, String> {
        let mut seen_queries = HashSet::new();
        let pattern: Vec<Option<TypedValue>> = query
            .matchers
            .iter()
            .map(|m| match m {
                Matcher::Any => None,
                Matcher::Constant(val) => Some(val.clone()),
            })
            .collect();

        let atom = Atom {
            symbol: query.symbol.to_string(),
            terms: query
                .matchers
                .iter()
                .map(|_| Term::Variable("_".to_string()))
                .collect(),
            sign: true,
        };

        let results = Self::evaluate_subquery_static(
            &self.program,
            &atom,
            &pattern,
            table,
            &mut seen_queries,
            &self.processed,
            0,
        )?;

        Ok(results.into_iter().collect())
    }
}
