use std::collections::HashSet;

use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::helpers::helpers::split_program;
use crate::program_transformations::magic_sets::create_magic_seed_fact;
use crate::program_transformations::sdt::apply_sdt_transformation;
use datalog_syntax::*;

pub struct SdtEvaluator {
    processed: RelationStorage,
    unprocessed_insertions: RelationStorage,
    program: Program,
}

impl SdtEvaluator {
    pub fn new(processed: RelationStorage, unprocessed: RelationStorage, program: Program) -> Self {
        Self {
            processed,
            unprocessed_insertions: unprocessed,
            program,
        }
    }

    pub fn evaluate_query(&mut self, query: &Query) -> HashSet<AnonymousGroundAtom> {
        // Create adorned query symbol
        let pattern_string: String = query
            .matchers
            .iter()
            .map(|matcher| match matcher {
                Matcher::Constant(_) => 'b',
                Matcher::Any => 'f',
            })
            .collect();

        let adorned_symbol = format!("{}_{}", query.symbol, pattern_string);

        let query_temp = Query {
            matchers: query.matchers.clone(),
            symbol: &adorned_symbol,
        };

        // Apply SDT transformation (produces program with negated demand hypotheses)
        let sdt_result = apply_sdt_transformation(&self.program, query);
        let sdt_program = sdt_result.program;

        // Create a fresh runtime-like storage for the transformed program
        let mut relation_storage: RelationStorage = Default::default();

        // Register all relations from the transformed program
        for rule in &sdt_program.inner {
            relation_storage
                .inner
                .entry(rule.head.symbol.clone())
                .or_default();
            for body_atom in &rule.body {
                relation_storage
                    .inner
                    .entry(body_atom.symbol.clone())
                    .or_default();
            }
        }

        // Copy base predicate facts from the original runtime
        for (rel_name, facts) in &self.processed.inner {
            if !self
                .program
                .inner
                .iter()
                .any(|rule| rule.head.symbol == *rel_name)
            {
                if !facts.is_empty() {
                    relation_storage.insert_registered(rel_name, facts.iter().cloned());
                }
            }
        }

        for (rel_name, facts) in &self.unprocessed_insertions.inner {
            if !self
                .program
                .inner
                .iter()
                .any(|rule| rule.head.symbol == *rel_name)
            {
                if !facts.is_empty() {
                    relation_storage.insert_registered(rel_name, facts.iter().cloned());
                }
            }
        }

        // Add magic seed fact
        let (magic_pred, seed_fact) = create_magic_seed_fact(query);
        relation_storage
            .inner
            .entry(magic_pred.clone())
            .or_default();
        relation_storage.insert(&magic_pred, seed_fact);

        // SDT now produces purely positive programs — standard Free Join
        // evaluation suffices. No inflationary negation or demand-first
        // scheduling needed.
        let (nonrecursive_program, recursive_program) = split_program(sdt_program);

        crate::evaluation::free_join_semi_naive::free_join_evaluation(
            &mut relation_storage,
            &nonrecursive_program,
            &recursive_program,
        );

        // Collect results matching the adorned query
        let results: HashSet<AnonymousGroundAtom> = relation_storage
            .get_relation(&query_temp.symbol)
            .iter()
            .filter(|fact| pattern_match(&query_temp, fact))
            .map(|fact| (**fact).clone())
            .collect();

        results
    }
}
