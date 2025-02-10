use std::collections::HashSet;

use datalog_syntax::{AnonymousGroundAtom, Atom, Matcher, Query, Term, TypedValue};

use crate::engine::subsumptive_table::SubsumptiveTable;

fn evaluate_subsumptive(
    query: &Query,
    table: &mut SubsumptiveTable
) -> Result<Vec<AnonymousGroundAtom>, String> {

    let mut seen_queries = HashSet::new();
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

    let atom = Atom {
        symbol: query.symbol.to_string(),
        terms: query.matchers
            .iter()
            .map(|_| Term::Variable("_".to_string()))
            .collect(),
        sign: true,
    };

    let results = evaluate_subquery(
        &atom,
        &pattern,
        table,
        &mut seen_queries,
        0 // Start with depth 0
    )?;

    Ok(results.into_iter().collect())
}

pub fn evaluate_subquery(
    atom: &Atom,
    pattern: &[Option<TypedValue>],
    table: &mut SubsumptiveTable,
    seen_queries: &mut HashSet<(String, Vec<Option<TypedValue>>)>,
    depth: usize
) -> Result<HashSet<AnonymousGroundAtom>, String> {
    let indent = "  ".repeat(depth);

    // Check cache first
    if let Some(cached_results) = table.find_subsuming(&atom.symbol, pattern) {
        return Ok(cached_results.iter().cloned().collect());
    }

    let mut all_results = HashSet::new();
    let query_key = (atom.symbol.clone(), pattern.to_vec());

    // Check for cycles in recursion
    if seen_queries.contains(&query_key) {
        return Ok(all_results);
    }
    seen_queries.insert(query_key.clone());

    // Process base facts
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
        all_results.extend(matching_facts);
    }

    // Process rules
    for rule in &self.program.inner {
        if rule.head.symbol == atom.symbol {
            let mut rule_results = HashSet::new();
            self.evaluate_rule_subsumptive(
                rule,
                pattern,
                table,
                seen_queries,
                &mut rule_results,
                depth + 1
            )?;
            all_results.extend(rule_results);
        }
    }

    seen_queries.remove(&query_key);

    // Cache results if we have any
    if !all_results.is_empty() {
        table.insert(&atom.symbol, pattern.to_vec(), all_results.iter().cloned().collect());
    }

    Ok(all_results)
}

