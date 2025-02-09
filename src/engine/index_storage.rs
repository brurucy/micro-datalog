use std::sync::Arc;

use ahash::HashMap;
use datalog_syntax::{AnonymousGroundAtom, Program, TypedValue};
use indexmap::IndexSet;

use crate::evaluation::spj_processor::Stack;

use super::storage::RelationStorage;

#[derive(Clone, Hash, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum EphemeralValue {
    FactRef(Arc<AnonymousGroundAtom>),
    JoinResult(Vec<Arc<AnonymousGroundAtom>>),
}

type JoinKey = Vec<(usize, usize)>;
type HashIndex = HashMap<Vec<TypedValue>, Vec<EphemeralValue>>;

#[derive(Default)]
pub struct IndexStorage {
    pub inner: HashMap<String, Vec<EphemeralValue>>,
    pub diff: HashMap<String, Vec<EphemeralValue>>,
    pub hash_indices: HashMap<String, HashMap<JoinKey, HashIndex>>,
}

impl IndexStorage {
    fn build_hash_key(fact: &EphemeralValue, join_keys: &JoinKey) -> Vec<TypedValue> {
        join_keys
            .iter()
            .map(|(col, _)| match fact {
                EphemeralValue::FactRef(f) => f[*col].clone(),
                EphemeralValue::JoinResult(fs) => {
                    let mut cumsum = 0;
                    for f in fs {
                        cumsum += f.len();
                        if *col < cumsum {
                            return f[col - (cumsum - f.len())].clone();
                        }
                    }
                    unreachable!()
                }
            })
            .collect()
    }

    pub fn add_index(&mut self, relation_symbol: &str, join_keys: JoinKey) {
        self.hash_indices
            .entry(relation_symbol.to_string())
            .or_insert(HashMap::default())
            .insert(join_keys, HashMap::default());
    }

    pub fn borrow_all(
        &mut self,
        relation_symbol: &str,
        facts: impl Iterator<Item = EphemeralValue>,
    ) {
        let facts: Vec<_> = facts.collect();

        for fact in facts.iter() {
            for (existing_join_keys, existing_indices) in self
                .hash_indices
                .entry(relation_symbol.to_string())
                .or_insert(HashMap::default())
            {
                let hash_key = Self::build_hash_key(fact, existing_join_keys);
                existing_indices
                    .entry(hash_key)
                    .or_insert_with(Vec::new)
                    .push(fact.clone());
            }
        }

        if let Some(ephemeral_relation) = self.diff.get_mut(relation_symbol) {
            ephemeral_relation.extend(facts);
        } else {
            self.diff
                .insert(relation_symbol.to_string(), Vec::from_iter(facts));
            if self.inner.get(relation_symbol).is_none() {
                self.inner.insert(relation_symbol.to_string(), Vec::new());
            }
        }
    }
}

pub type NonrecursiveProgram = Program;
pub type RecursiveProgram = Program;

impl From<(&NonrecursiveProgram, &RecursiveProgram, &RelationStorage)> for IndexStorage {
    fn from(value: (&NonrecursiveProgram, &RecursiveProgram, &RelationStorage)) -> Self {
        let mut index_storage = IndexStorage::default();

        let (nonrecursive_program, recursive_program, relation_storage) = value;

        let nonrecursive_stack = nonrecursive_program
            .inner
            .iter()
            .map(|r| Stack::from(r.clone()))
            .collect::<Vec<_>>();
        let recursive_stack = recursive_program
            .inner
            .iter()
            .map(|r| Stack::from(r.clone()))
            .collect::<Vec<_>>();

        let nonrecursive_join_keys = nonrecursive_stack
            .iter()
            .flat_map(|s| s.get_all_join_keys())
            .collect::<IndexSet<_>>();
        let recursive_join_keys = recursive_stack
            .iter()
            .flat_map(|s| s.get_all_join_keys())
            .collect::<IndexSet<_>>();

        let all_join_keys = nonrecursive_join_keys
            .union(&recursive_join_keys)
            .collect::<IndexSet<_>>();

        for (rel_name, join_keys) in all_join_keys {
            index_storage.add_index(&rel_name, join_keys.clone());
        }

        let all_moves = nonrecursive_stack
            .iter()
            .chain(recursive_stack.iter())
            .flat_map(|s| s.get_all_moves())
            .collect::<IndexSet<_>>();
        for move_instruction in all_moves {
            if let Some(relation) = relation_storage.get_relation_safe(&move_instruction) {
                index_storage.borrow_all(
                    &move_instruction,
                    relation
                        .into_iter()
                        .map(|f| EphemeralValue::FactRef(f.clone())),
                );
            }
        }

        index_storage
    }
}
