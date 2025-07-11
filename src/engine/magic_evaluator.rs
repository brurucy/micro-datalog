use std::collections::HashSet;
use std::time::{Duration, Instant};

use crate::engine::storage::RelationStorage;
use crate::evaluation::query::pattern_match;
use crate::helpers::helpers::get_queries_with_all_binding_patterns;
use crate::program_transformations::magic_sets::{
    apply_magic_transformation, create_magic_seed_fact,
};
use datalog_rule_macro::program;
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

    pub fn evaluate_query<'b>(&self, query: &Query) -> (Vec<Vec<TypedValue>>, Duration) {
        // Create adorned query symbol by combining original symbol with binding pattern
        let pattern_string: String = query
            .matchers
            .iter()
            .map(|matcher| match matcher {
                Matcher::Constant(_) => 'b',
                Matcher::Any => 'f',
            })
            .collect();

        // Apply magic transformation once
        let (magic_program, magic_seeds) = apply_magic_transformation(&self.program, query);
        //println!("Magic seeds: {:?}", magic_seeds);
        
        println!("Magic program: ====");
        for rule in &magic_program.inner {
            println!("{:?}", rule);
        }

        // Create runtime with the transformed program
        let mut runtime = MicroRuntime::new(magic_program.clone());

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

        // add seed magic_T_fbf("0")
        // add seed magic_T_fbf("3")
        // let query_0 = build_query!(T(_, 0usize, _));
        // let query_3 = build_query!(T(_, 3usize, _));


        // let (magic_pred_0, seed_fact_0) = create_magic_seed_fact(&query_0);
        // println!("Magic pred_0: {:?}", magic_pred_0);
        // println!("Seed fact_0: {:?}", seed_fact_0);
        // let (magic_pred_3, seed_fact_3) = create_magic_seed_fact(&query_3);
        // println!("Magic pred_3: {:?}", magic_pred_3);
        // println!("Seed fact_3: {:?}", seed_fact_3);

        runtime
            .unprocessed_insertions
            .inner
            .entry(magic_pred.clone())
            .or_default();
        runtime.insert(&magic_pred, seed_fact.clone());
        // runtime.insert(&magic_pred_0, seed_fact_0.clone());
        // runtime.insert(&magic_pred_3, seed_fact_3.clone());


        for seed in magic_seeds {
            let seed_symbol = seed.symbol.clone();
            let seed_terms: Vec<TypedValue> = seed.terms.iter().filter_map(|term| {
                if let Term::Constant(val) = term {
                    Some(val.clone())
                } else {
                    None
                }
            }).collect();
     
            runtime
                .unprocessed_insertions
                .inner
                .entry(seed_symbol.clone())
                .or_default();
            runtime.insert(&seed_symbol, seed_terms);
        }

     

        let start = Instant::now();
        // Evaluate the program
        runtime.poll();

        let evaluation_time = start.elapsed();

        let mut results = HashSet::new();
        let queries = get_queries_with_all_binding_patterns(query, &magic_program);
        for query_i in queries {
            let results_i: Vec<Vec<TypedValue>> = runtime
                .processed
                .get_relation(&query_i.symbol)
                .iter()
                .filter(|fact| pattern_match(&query_i, fact))
                .map(|fact| (**fact).clone())
                .collect();

            results.extend(results_i);
        }

        (results.into_iter().collect(), evaluation_time)
    }
}
