use std::time::Instant;
use ahash::HashMap;
use crate::helpers::helpers::{ DELTA_PREFIX, OVERDELETION_PREFIX, REDERIVATION_PREFIX };
use datalog_syntax::{ AnonymousGroundAtom, Program };
use indexmap::IndexSet;
use crate::evaluation::spj_processor::RuleEvaluator;
use rayon::prelude::*;

pub type FactStorage = IndexSet<AnonymousGroundAtom, ahash::RandomState>;
#[derive(Default)]
pub struct RelationStorage {
    pub(crate) inner: HashMap<String, FactStorage>,
    pub(crate) strata: HashMap<usize, Vec<String>>, // Maps stratum ID to relation symbols
}

impl RelationStorage {
    /*
    pub fn get_stratum(&self, stratum_id: usize) -> Vec<String> {
        self.strata.get(&stratum_id).unwrap();
    }
       

    pub fn get_relations_in_stratum(&self, stratum: usize) -> impl Iterator<Item = &FactStorage> {
        self.inner.iter().filter_map(|(symbol, facts)| {
            if symbol.contains(&format!("_stratum_{}", stratum)) {
                Some(facts)
            } else {
                None
            }
        })
    }
         */

    /*
    pub fn materialize_stratum(&mut self, stratum_program: &Program, stratum_id: usize) {
        // Process the rules in the given stratum only
        for rule in stratum_program.inner.iter() {
            if rule.head.symbol.contains(&format!("_stratum_{}", stratum_id)) {
                let evaluator = RuleEvaluator::new(self, rule);
                let evaluation = evaluator.step();
    
                let delta_relation_symbol = rule.head.symbol.clone();
                let current_delta_relation = self.get_relation(&delta_relation_symbol).unwrap();
    
                let diff: FactStorage = evaluation
                    .into_iter()
                    .filter(|fact| !current_delta_relation.contains(fact))
                    .collect();
    
                self.insert_all(&delta_relation_symbol, diff.into_iter());
            }
        }
    }
        */
    
    
/*
    pub fn process_stratum(&mut self, stratum_id: usize, stratum_program: &Program) {
        if let Some(relation_symbols) = self.get_stratum(stratum_id) {
            for symbol in relation_symbols {
                let rules = stratum_program.inner.iter().filter(|rule| rule.head.symbol == *symbol);

                for rule in rules {
                    let evaluator = RuleEvaluator::new(self, rule);
                    let evaluation = evaluator.step();

                    let delta_relation_symbol = rule.head.symbol.clone();
                    let current_delta_relation = self.get_relation(&delta_relation_symbol).unwrap();

                    let diff: FactStorage = evaluation
                        .into_iter()
                        .filter(|fact| !current_delta_relation.contains(fact))
                        .collect();

                    self.insert_all(&delta_relation_symbol, diff.into_iter());
                }
            }
        }
    }
        */
    pub fn get_relation(&self, relation_symbol: &str) -> &FactStorage {
        return self.inner.get(relation_symbol).unwrap();
    }
    pub fn drain_relation(&mut self, relation_symbol: &str) -> Vec<AnonymousGroundAtom> {
        let rel = self.inner.get_mut(relation_symbol).unwrap();

        return rel.drain(..).collect();
    }
    pub fn drain_all_relations(
        &mut self
    ) -> impl Iterator<Item = (String, Vec<AnonymousGroundAtom>)> + '_ {
        let relations_to_be_drained: Vec<_> = self.inner
            .iter()
            .map(|(symbol, _)| symbol.clone())
            .collect();

        relations_to_be_drained.into_iter().map(|relation_symbol| {
            (
                relation_symbol.clone(),
                self.inner
                    .get_mut(&relation_symbol)
                    .unwrap()
                    .drain(..)
                    .collect::<Vec<_>>(),
            )
        })
    }
    pub fn drain_prefix_filter<'a>(
        &'a mut self,
        prefix: &'a str
    ) -> impl Iterator<Item = (String, Vec<AnonymousGroundAtom>)> + '_ {
        let relations_to_be_drained: Vec<_> = self.inner
            .iter()
            .map(|(symbol, _)| symbol.clone())
            .filter(|relation_symbol| relation_symbol.starts_with(prefix))
            .collect();

        relations_to_be_drained.into_iter().map(|relation_symbol| {
            (
                relation_symbol.clone(),
                self.inner
                    .get_mut(&relation_symbol)
                    .unwrap()
                    .drain(..)
                    .collect::<Vec<_>>(),
            )
        })
    }
    pub fn drain_deltas(&mut self) {
        let delta_relation_symbols: Vec<_> = self.inner
            .iter()
            .map(|(symbol, _)| symbol.clone())
            .filter(|relation_symbol| relation_symbol.starts_with(DELTA_PREFIX))
            .collect();

        delta_relation_symbols.into_iter().for_each(|relation_symbol| {
            if relation_symbol.starts_with(DELTA_PREFIX) {
                let delta_facts: Vec<_> = self.drain_relation(&relation_symbol);

                let current_non_delta_relation = self.inner
                    .get_mut(relation_symbol.strip_prefix(DELTA_PREFIX).unwrap())
                    .unwrap();

                delta_facts.into_iter().for_each(|fact| {
                    current_non_delta_relation.insert(fact);
                });
            }
        });
    }
    /// Apply overdeletions to the base relations and reinsert overdeletion facts.
    pub fn overdelete(&mut self) {
        let overdeletion_relations: Vec<_> = self.inner
            .keys()
            .filter(|symbol| symbol.starts_with(OVERDELETION_PREFIX))
            .cloned()
            .collect();

        for overdeletion_symbol in overdeletion_relations {
            let actual_relation_symbol = overdeletion_symbol
                .strip_prefix(OVERDELETION_PREFIX)
                .expect("Invalid overdeletion prefix");

            let overdeletion_relation = self.inner
                .remove(&overdeletion_symbol)
                .expect("Overdeletion relation not found");

            let actual_relation = self.inner
                .get_mut(actual_relation_symbol)
                .expect("Actual relation not found for overdeletion");

            for atom in &overdeletion_relation {
                actual_relation.remove(atom);
            }

            // Reinsert the overdeletion facts for rederivation.
            self.inner.insert(overdeletion_symbol, overdeletion_relation);
        }
    }
    /// Rederive facts by merging the rederivation relation into the base relation.
    pub fn rederive(&mut self) {
        let rederivation_relations: Vec<_> = self
            .inner
            .keys()
            .filter(|symbol| symbol.starts_with(REDERIVATION_PREFIX))
            .cloned()
            .collect();

        for rederivation_symbol in rederivation_relations {
            let actual_relation_symbol = rederivation_symbol
                .strip_prefix(REDERIVATION_PREFIX)
                .expect("Invalid rederivation prefix");

            let rederivation_relation = self
                .inner
                .remove(&rederivation_symbol)
                .expect("Rederivation relation not found");

            let actual_relation = self
                .inner
                .get_mut(actual_relation_symbol)
                .expect("Actual relation not found for rederivation");

            actual_relation.extend(rederivation_relation);
        }
    }
    pub fn clear_relation(&mut self, relation_symbol: &str) {
        self.inner.get_mut(relation_symbol).unwrap().clear();
    }
    pub fn clear_prefix(&mut self, prefix: &str) {
        self.inner.iter_mut().for_each(|ref_mult| {
            let (symbol, relation) = ref_mult;

            if symbol.starts_with(prefix) {
                relation.clear()
            }
        });
    }

    pub fn insert_registered(
        &mut self,
        relation_symbol: &str,
        registrations: impl Iterator<Item = AnonymousGroundAtom>
    ) {
        let mut hashes = vec![];

        registrations.into_iter().for_each(|fact| {
            hashes.push(fact);
        });

        if let Some(relation) = self.inner.get_mut(relation_symbol) {
            relation.extend(hashes)
        } else {
            let mut fresh_fact_storage = FactStorage::default();
            fresh_fact_storage.extend(hashes);

            self.inner.insert(relation_symbol.to_string(), fresh_fact_storage);
        }
    }

    pub fn insert_all(
        &mut self,
        relation_symbol: &str,
        facts: impl Iterator<Item = AnonymousGroundAtom>
    ) {
        if let Some(relation) = self.inner.get_mut(relation_symbol) {
            relation.extend(facts.into_iter())
        } else {
            let mut fresh_fact_storage = FactStorage::default();
            fresh_fact_storage.extend(facts.into_iter());

            self.inner.insert(relation_symbol.to_string(), fresh_fact_storage);
        }
    }
    pub fn insert(&mut self, relation_symbol: &str, ground_atom: AnonymousGroundAtom) -> bool {
        if let Some(relation) = self.inner.get_mut(relation_symbol) {
            return relation.insert(ground_atom);
        }

        let mut fresh_fact_storage = FactStorage::default();
        fresh_fact_storage.insert(ground_atom);

        self.inner.insert(relation_symbol.to_string(), fresh_fact_storage);

        true
    }
    pub fn remove(&mut self, relation_symbol: &str, ground_atom: AnonymousGroundAtom) -> bool {
        if let Some(relation) = self.inner.get_mut(relation_symbol) {
            return relation.remove(&ground_atom);
        }

        false
    }
    pub fn contains(&self, relation_symbol: &str, ground_atom: &AnonymousGroundAtom) -> bool {
        if let Some(relation) = self.inner.get(relation_symbol) {
            return relation.contains(ground_atom);
        }

        false
    }

    // Nonrecursive materialisation can be done sequentially in one pass.
    pub fn materialize_nonrecursive_delta_program(&mut self, nonrecursive_program: &Program) {
        for (idx, rule) in nonrecursive_program.inner.iter().enumerate() {
            let evaluator = RuleEvaluator::new(self, rule);

            let evaluation = evaluator.step();

            let delta_relation_symbol = rule.head.symbol.clone();

            let current_delta_relation = self.get_relation(&delta_relation_symbol);

            let diff: FactStorage = evaluation
                .into_iter()
                .filter(|fact| !current_delta_relation.contains(fact))
                .collect();

            if idx == 0 {
                *self.inner.get_mut(&delta_relation_symbol).unwrap() = diff.clone();
            } else {
                self.insert_all(&delta_relation_symbol, diff.clone().into_iter());
            }

            let relation_symbol = delta_relation_symbol.clone();
            relation_symbol.strip_prefix(DELTA_PREFIX).unwrap();
            self.insert_all(
                delta_relation_symbol.strip_prefix(DELTA_PREFIX).unwrap(),
                diff.into_iter()
            );
        }
    }
    pub fn materialize_recursive_delta_program(&mut self, recursive_program: &Program) {
        let evaluation_setup: Vec<_> = recursive_program.inner
            .iter()
            .map(|rule| (&rule.head.symbol, RuleEvaluator::new(self, rule)))
            .collect();

        let evaluation = evaluation_setup
            .into_iter()
            .map(|(delta_relation_symbol, rule)| {
                let out = rule.step().collect::<Vec<_>>();
                (delta_relation_symbol, out)
            })
            .collect::<Vec<_>>();

        evaluation
            .into_iter()
            .enumerate()
            .for_each(|(idx, (delta_relation_symbol, current_delta_evaluation))| {
                let curr = self.get_relation(delta_relation_symbol);

                let diff: FactStorage = current_delta_evaluation
                    .into_iter()
                    .filter(|fact| !curr.contains(fact))
                    .collect();

                if idx == 0 {
                    *self.inner.get_mut(delta_relation_symbol).unwrap() = diff.clone();
                } else {
                    self.insert_all(delta_relation_symbol, diff.clone().into_iter());
                }

                let relation_symbol = delta_relation_symbol.clone();
                relation_symbol.strip_prefix(DELTA_PREFIX).unwrap();
                self.insert_all(
                    delta_relation_symbol.strip_prefix(DELTA_PREFIX).unwrap(),
                    diff.into_iter()
                );
            });
    }

    pub fn len(&self) -> usize {
        return self.inner
            .iter()
            .filter(|(symbol, _facts)| !symbol.starts_with(DELTA_PREFIX))
            .map(|(_symbol, facts)| facts.len())
            .sum();
    }

    pub fn is_empty(&self) -> bool {
        return self.len() == 0;
    }
}
