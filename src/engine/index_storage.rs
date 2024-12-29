use std::sync::Arc;

use ahash::HashMap;
use datalog_syntax::AnonymousGroundAtom;

#[derive(Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum EphemeralValue {
    FactRef(Arc<AnonymousGroundAtom>),
    JoinResult(Vec<Arc<AnonymousGroundAtom>>),
}

#[derive(Default)]
pub struct IndexStorage {
    pub inner: HashMap<String, Vec<EphemeralValue>>,
    pub diff: HashMap<String, Vec<EphemeralValue>>,
}

impl IndexStorage {
    pub fn borrow_all(
        &mut self,
        relation_symbol: &str,
        facts: impl Iterator<Item = EphemeralValue>,
    ) {
        if let Some(ephemeral_relation) = self.diff.get_mut(relation_symbol) {
            ephemeral_relation.extend(facts);
        } else {
            self.diff
                .insert(relation_symbol.to_string(), Vec::from_iter(facts));
            self.inner.insert(relation_symbol.to_string(), Vec::new());
        }
    }
}
