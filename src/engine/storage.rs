use crate::evaluation::spj_processor::RuleEvaluator;
use ahash::{HashMap, HashMapExt};
use datalog_syntax::{AnonymousGroundAtom, Program};
use indexmap::IndexSet;
use std::sync::Arc;

use super::index_storage::{EphemeralValue, IndexStorage};
pub type FactStorage = IndexSet<Arc<AnonymousGroundAtom>, ahash::RandomState>;
#[derive(Default)]
pub struct RelationStorage {
    pub(crate) inner: HashMap<String, FactStorage>,
}

impl RelationStorage {
    pub fn get_relation(&self, relation_symbol: &str) -> &FactStorage {
        return self.inner.get(relation_symbol).unwrap();
    }
    pub fn get_relation_safe(&self, relation_symbol: &str) -> Option<&FactStorage> {
        return self.inner.get(relation_symbol);
    }
    pub fn drain_all_relations(
        &mut self,
    ) -> impl Iterator<Item = (String, Vec<Arc<AnonymousGroundAtom>>)> + '_ {
        let relations_to_be_drained: Vec<_> = self
            .inner
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
    pub fn insert_registered(
        &mut self,
        relation_symbol: &str,
        registrations: impl Iterator<Item = Arc<AnonymousGroundAtom>>,
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
        facts: impl Iterator<Item = Arc<AnonymousGroundAtom>>,
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
            return relation.insert(Arc::new(ground_atom));
        }

        let mut fresh_fact_storage = FactStorage::default();
        fresh_fact_storage.insert(Arc::new(ground_atom));

        self.inner
            .insert(relation_symbol.to_string(), fresh_fact_storage);

        true
    }
    pub fn contains(&self, relation_symbol: &str, ground_atom: &AnonymousGroundAtom) -> bool {
        if let Some(relation) = self.inner.get(relation_symbol) {
            return relation.contains(ground_atom);
        }

        false
    }

    // Nonrecursive materialisation can be done sequentially in one pass.
    pub fn materialize_nonrecursive_delta_program<'a>(
        &mut self,
        nonrecursive_program: &Program,
        index_storage: &mut IndexStorage,
    ) {
        let mut new_diff: HashMap<String, Vec<EphemeralValue>> = HashMap::new();

        for (_idx, rule) in nonrecursive_program.inner.iter().enumerate() {
            let evaluator = RuleEvaluator::new(self, rule);

            let evaluation = evaluator.step(index_storage);

            let delta_relation_symbol = rule.head.symbol.clone();

            let current_relation = self.get_relation(&delta_relation_symbol);

            let diff: FactStorage = evaluation
                .into_iter()
                .filter(|fact| !current_relation.contains(fact))
                .map(|fact| Arc::new(fact))
                .collect();

            self.insert_all(&delta_relation_symbol, diff.clone().into_iter());
            new_diff.entry(delta_relation_symbol).or_default().extend(
                diff.into_iter()
                    .map(|x| super::index_storage::EphemeralValue::FactRef(x)),
            );
        }
        
        for diffs in index_storage.diff.values_mut() {
            diffs.clear();
        }
        for (rel_name, new_diffs) in new_diff.clone() {
            index_storage.borrow_all(&rel_name, new_diffs.into_iter());
        }
    }
    pub fn materialize_recursive_delta_program<'a>(
        &mut self,
        recursive_program: &Program,
        index_storage: &mut IndexStorage,
    ) {
        let mut new_diff: HashMap<String, Vec<EphemeralValue>> = HashMap::new();

        let evaluation_setup: Vec<_> = recursive_program
            .inner
            .iter()
            .map(|rule| (&rule.head.symbol, RuleEvaluator::new(self, rule)))
            .collect();

        let evaluation = evaluation_setup
            .into_iter()
            .map(|(delta_relation_symbol, rule)| {
                let out = rule.step(index_storage).collect::<Vec<_>>();
                (delta_relation_symbol, out)
            })
            .collect::<Vec<_>>();

        evaluation.into_iter().enumerate().for_each(
            |(_idx, (delta_relation_symbol, current_delta_evaluation))| {
                let curr = self.get_relation(delta_relation_symbol);

                let diff: FactStorage = current_delta_evaluation
                    .into_iter()
                    .filter(|fact| !curr.contains(fact))
                    .map(|fact| Arc::new(fact))
                    .collect();

                self.insert_all(delta_relation_symbol, diff.clone().into_iter());
                new_diff
                    .entry(delta_relation_symbol.clone())
                    .or_default()
                    .extend(
                        diff.into_iter()
                            .map(|x| super::index_storage::EphemeralValue::FactRef(x)),
                    );
            },
        );

        for diffs in index_storage.diff.values_mut() {
            diffs.clear();
        }
        for (rel_name, new_diffs) in new_diff.clone() {
            index_storage.borrow_all(&rel_name, new_diffs.into_iter());
        }
    }

    pub fn len(&self) -> usize {
        return self.inner.iter().map(|(_symbol, facts)| facts.len()).sum();
    }

    pub fn is_empty(&self) -> bool {
        return self.len() == 0;
    }
}
