use std::sync::Arc;

use ahash::{HashMap, HashSet};
use datalog_syntax::{AnonymousGroundAtom, TypedValue};

#[derive(Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
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
    pub hash_indices: HashMap<(String, JoinKey), HashIndex>
}

impl IndexStorage {
    fn build_hash_key(fact: &EphemeralValue, join_keys: &JoinKey) -> Vec<TypedValue> {
        join_keys.iter()
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
    
    pub fn borrow_all(
        &mut self,
        relation_symbol: &str,
        facts: impl Iterator<Item = EphemeralValue>,
        join_keys: Option<JoinKey>,
    ) {
        let facts: Vec<_> = facts.collect();
        
        if let Some(join_keys) = join_keys {
            let index = self.hash_indices
                .entry((relation_symbol.to_string(), join_keys.clone()))
                .or_insert_with(HashMap::default);

            for fact in facts.iter() {
                let key = Self::build_hash_key(fact, &join_keys);
                index.entry(key).or_insert_with(Vec::new).push(fact.clone());
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
