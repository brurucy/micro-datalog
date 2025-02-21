use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::program_transformations::magic_sets::{
    apply_magic_transformation, create_magic_seed_fact,
};
use datalog_syntax::*;

use super::datalog::MicroRuntime;

pub struct MagicEvaluator<'a> {
    processed: &'a mut RelationStorage,
    unprocessed_insertions: &'a mut RelationStorage,
}

impl<'a> MagicEvaluator<'a> {
    pub fn new(processed: &'a mut RelationStorage, unprocessed: &'a mut RelationStorage) -> Self {
        Self {
            processed,
            unprocessed_insertions: unprocessed,
        }
    }

    pub fn evaluate_query<'b>(
        &mut self,
        query: &'b Query,
        program: Program,
    ) -> Result<impl Iterator<Item = AnonymousGroundAtom> + 'a, String> {
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

        let query_temp = Query {
            matchers: query.matchers.clone(),
            symbol: &adorned_symbol,
        };

        let magic_program = apply_magic_transformation(&program, query);

        let mut runtime = MicroRuntime::new(magic_program.clone());

        for (rel_name, facts) in &self.processed.inner {
            if !program
                .inner
                .iter()
                .any(|rule| rule.head.symbol == *rel_name)
            {
                if !facts.is_empty() {
                    runtime
                        .processed
                        .insert_registered(rel_name, facts.iter().cloned());
                }
            }
        }

        // Also collect unprocessed insertions for base predicates
        for (rel_name, facts) in &self.unprocessed_insertions.inner {
            if !program
                .inner
                .iter()
                .any(|rule| rule.head.symbol == *rel_name)
            {
                if !facts.is_empty() {
                    runtime
                        .unprocessed_insertions
                        .insert_registered(&rel_name, facts.iter().cloned());
                }
            }
        }

        // Also initialize storage for all adorned predicates
        for rule in magic_program.inner {
            runtime
                .unprocessed_insertions
                .inner
                .entry(rule.head.symbol.clone())
                .or_default();
            for body_atom in &rule.body {
                runtime
                    .unprocessed_insertions
                    .inner
                    .entry(body_atom.symbol.clone())
                    .or_default();
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

        runtime.poll();

        let result: Vec<_> = runtime
            .processed
            .get_relation(query_temp.symbol)
            .iter()
            .filter(|fact| pattern_match(&query_temp, fact))
            .map(|fact| (**fact).clone())
            .collect();

        return Ok(result.into_iter());
    }
}
