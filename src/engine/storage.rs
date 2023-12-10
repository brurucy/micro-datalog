use std::time::Instant;
use ahash::HashMap;
use crate::helpers::helpers::{DELTA_PREFIX, OVERDELETION_PREFIX, REDERIVATION_PREFIX};
use datalog_syntax::{AnonymousGroundAtom, Program};
use indexmap::IndexSet;
use crate::evaluation::spj_processor::RuleEvaluator;
use rayon::prelude::*;

pub type FactStorage = IndexSet<AnonymousGroundAtom, ahash::RandomState>;
#[derive(Default)]
pub struct RelationStorage {
    pub(crate) inner: HashMap<String, FactStorage>,
}

impl RelationStorage {
    pub fn get_relation(&self, relation_symbol: &str) -> &FactStorage {
        return self.inner.get(relation_symbol).unwrap()
    }
    pub fn drain_relation(&mut self, relation_symbol: &str) -> Vec<AnonymousGroundAtom> {
        let rel = self.inner.get_mut(relation_symbol).unwrap();

        return rel.drain(..).collect();
    }
    pub fn drain_all_relations(
        &mut self,
    ) -> impl Iterator<Item = (String, Vec<AnonymousGroundAtom>)> + '_ {
        let relations_to_be_drained: Vec<_> =
            self.inner.iter().map(|(symbol, _)| symbol.clone()).collect();

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
        prefix: &'a str,
    ) -> impl Iterator<Item = (String, Vec<AnonymousGroundAtom>)> + '_ {
        let relations_to_be_drained: Vec<_> = self
            .inner
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
        let delta_relation_symbols: Vec<_> = self
            .inner
            .iter()
            .map(|(symbol, _)| symbol.clone())
            .filter(|relation_symbol| relation_symbol.starts_with(DELTA_PREFIX))
            .collect();

        delta_relation_symbols
            .into_iter()
            .for_each(|relation_symbol| {
                if relation_symbol.starts_with(DELTA_PREFIX) {
                    let delta_facts: Vec<_> = self.drain_relation(&relation_symbol);

                    let current_non_delta_relation = self
                        .inner
                        .get_mut(relation_symbol.strip_prefix(DELTA_PREFIX).unwrap())
                        .unwrap();

                    delta_facts.into_iter().for_each(|fact| {
                        current_non_delta_relation.insert(fact);
                    });
                }
            });
    }
    pub fn overdelete(&mut self) {
        let overdeletion_relations: Vec<_> = self
            .inner
            .iter()
            .filter(|(symbol, _)| symbol.starts_with(OVERDELETION_PREFIX))
            .map(|(symbol, _facts)| {
                (
                    symbol.clone(),
                    symbol
                        .strip_prefix(&OVERDELETION_PREFIX)
                        .unwrap()
                        .to_string(),
                )
            })
            .collect();

        overdeletion_relations.into_iter().for_each(
            |(overdeletion_symbol, actual_relation_symbol)| {
                let overdeletion_relation = self.inner.remove(&overdeletion_symbol).unwrap();
                let actual_relation = self.inner.get_mut(&actual_relation_symbol).unwrap();

                overdeletion_relation.iter().for_each(|atom| {
                    actual_relation.remove(atom);
                });

                // We insert it back because it is necessary for rederivation.
                self.inner
                    .insert(overdeletion_symbol, overdeletion_relation);
            },
        );
    }
    pub fn rederive(&mut self) {
        let rederivation_relations: Vec<_> = self
            .inner
            .iter()
            .filter(|(symbol, _)| symbol.starts_with(REDERIVATION_PREFIX))
            .map(|(symbol, _facts)| {
                (
                    symbol.clone(),
                    symbol
                        .strip_prefix(&REDERIVATION_PREFIX)
                        .unwrap()
                        .to_string(),
                )
            })
            .collect();

        rederivation_relations.into_iter().for_each(
            |(rederivation_symbol, actual_relation_symbol)| {
                let rederivation_relation = self.inner.remove(&rederivation_symbol).unwrap();
                let actual_relation = self.inner.get_mut(&actual_relation_symbol).unwrap();

                rederivation_relation.into_iter().for_each(|atom| {
                    actual_relation.insert(atom);
                });
            },
        );
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
        registrations: impl Iterator<Item = AnonymousGroundAtom>,
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

            self.inner
                .insert(relation_symbol.to_string(), fresh_fact_storage);
        }
    }

    pub fn insert_all(
        &mut self,
        relation_symbol: &str,
        facts: impl Iterator<Item = AnonymousGroundAtom>,
    ) {
        if let Some(relation) = self.inner.get_mut(relation_symbol) {
            relation.extend(facts.into_iter())
        } else {
            let mut fresh_fact_storage = FactStorage::default();
            fresh_fact_storage.extend(facts.into_iter());

            self.inner
                .insert(relation_symbol.to_string(), fresh_fact_storage);
        }
    }
    pub fn insert(&mut self, relation_symbol: &str, ground_atom: AnonymousGroundAtom) -> bool {
        if let Some(relation) = self.inner.get_mut(relation_symbol) {
            return relation.insert(ground_atom);
        }

        let mut fresh_fact_storage = FactStorage::default();
        fresh_fact_storage.insert(ground_atom);

        self.inner
            .insert(relation_symbol.to_string(), fresh_fact_storage);

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

    pub fn materialize_delta_program(&mut self, program: &Program) {
        let evaluation_setup: Vec<_> = program
            .inner
            .iter()
            .map(|rule| (&rule.head.symbol, RuleEvaluator::new(self, rule)))
            .collect();

        let evaluation = evaluation_setup
            // Change the following line to into_iter for it to not run in parallel.
            .into_par_iter()
            .map(|(delta_relation_symbol, rule)| {
                let now = Instant::now();
                let out = rule.step().collect::<Vec<_>>();
                //println!("Rule elapsed: {} milis", now.elapsed().as_millis());

                (delta_relation_symbol, out)
            })
            .collect::<Vec<_>>();

        evaluation.into_iter().enumerate().for_each(
            |(idx, (delta_relation_symbol, current_delta_evaluation))| {
                let curr = self.get_relation(delta_relation_symbol);

                let diff: FactStorage = current_delta_evaluation
                    .into_iter()
                    .filter(|fact| !curr.contains(fact))
                    .collect();

                if idx == 0 {
                    (*self.inner.get_mut(delta_relation_symbol).unwrap()) = diff.clone();
                } else {
                    self.insert_all(delta_relation_symbol, diff.clone().into_iter());
                }

                let relation_symbol = delta_relation_symbol.clone();
                relation_symbol.strip_prefix(DELTA_PREFIX).unwrap();
                self.insert_all(
                    delta_relation_symbol.strip_prefix(DELTA_PREFIX).unwrap(),
                    diff.into_iter(),
                );
            },
        );
    }

    pub fn len(&self) -> usize {
        return self
            .inner
            .iter()
            .filter(|(symbol, _facts)| !symbol.starts_with(DELTA_PREFIX))
            .map(|(_symbol, facts)| facts.len())
            .sum();
    }

    pub fn is_empty(&self) -> bool {
        return self.len() == 0;
    }
}
