use std::collections::HashSet;
use std::time::{Duration, Instant};

use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::program_transformations::magic_sets::{
    apply_magic_transformation, create_magic_seed_fact,
};
use datalog_syntax::*;

use super::datalog::MicroRuntime;

pub struct MagicEvaluator {
    processed: RelationStorage,
    unprocessed_insertions: RelationStorage,
    program: Program,
}

impl<'a> MagicEvaluator {
    pub fn new(processed: RelationStorage, unprocessed: RelationStorage, program: Program) -> Self {
        Self {
            processed,
            unprocessed_insertions: unprocessed,
            program: program,
        }
    }

    pub fn evaluate_query<'b>(&mut self, query: &Query) -> (Vec<Vec<TypedValue>>, Duration) {
        // Create adorned query symbol by combining original symbol with binding pattern
        let pattern_string: String = query
            .matchers
            .iter()
            .map(|matcher| match matcher {
                Matcher::Constant(_) => 'b',
                Matcher::Any => 'f',
            })
            .collect();

        let adorned_symbol = format!("{}_{}", query.symbol, pattern_string);

        // Create temporary query with adorned symbol
        let query_temp = Query {
            matchers: query.matchers.clone(),
            symbol: &adorned_symbol,
        };

        // Apply magic transformation once
        let magic_program = apply_magic_transformation(&self.program, query);

        // Create runtime with the transformed program
        let mut runtime = MicroRuntime::new(magic_program);

        // Pre-compute base predicates to avoid repeated checks
        let base_predicates: HashSet<_> = self
            .program
            .inner
            .iter()
            .map(|rule| &rule.head.symbol)
            .collect();

        // Initialize all relations in one pass
        let mut all_relations = HashSet::new();
        for rule in &self.program.inner {
            all_relations.insert(rule.head.symbol.clone());
            for body_atom in &rule.body {
                all_relations.insert(body_atom.symbol.clone());
            }
        }

        // Initialize storage for all relations
        for rel_name in all_relations {
            runtime
                .unprocessed_insertions
                .inner
                .entry(rel_name)
                .or_default();
        }

        // Transfer base facts in a single pass
        for (rel_name, facts) in &self.processed.inner {
            if !base_predicates.contains(rel_name) && !facts.is_empty() {
                runtime
                    .processed
                    .insert_registered(rel_name, facts.iter().cloned());
            }
        }

        // Transfer unprocessed facts in a single pass
        for (rel_name, facts) in &self.unprocessed_insertions.inner {
            if !base_predicates.contains(rel_name) && !facts.is_empty() {
                runtime
                    .unprocessed_insertions
                    .insert_registered(rel_name, facts.iter().cloned());
            }
        }

        // Add magic seed fact
        let (magic_pred, seed_fact) = create_magic_seed_fact(query);
        runtime
            .unprocessed_insertions
            .inner
            .entry(magic_pred.clone())
            .or_default();
        runtime.insert(&magic_pred, seed_fact);

        let start = Instant::now();
        // Evaluate the program
        runtime.poll();

        let evaluation_time = start.elapsed();
        let results = runtime
            .processed
            .get_relation(&query_temp.symbol)
            .iter()
            .filter(|fact| pattern_match(&query_temp, fact))
            .map(|fact| (**fact).clone())
            .collect();
        (results, evaluation_time)
    }
}
