use ahash::HashMap;
use datalog_syntax::AnonymousGroundAtom;

#[derive(Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum EphemeralValue<'a> {
    FactRef(&'a AnonymousGroundAtom),
    JoinResult(Vec<&'a AnonymousGroundAtom>),
}

#[derive(Default)]
pub struct IndexStorage<'a> {
    pub(crate) inner: HashMap<String, Vec<EphemeralValue<'a>>>,
}

impl<'b, 'a> IndexStorage<'a> {
    pub fn get_relation(&self, relation_symbol: &str) -> &Vec<EphemeralValue<'a>> {
        return self.inner.get(relation_symbol).unwrap();
    }
    pub fn borrow_all(
        &mut self,
        relation_symbol: &str,
        facts: impl Iterator<Item = EphemeralValue<'a>>,
    ) {
        if let Some(ephemeral_relation) = self.inner.get_mut(relation_symbol) {
            ephemeral_relation.extend(facts);
        } else {
            self.inner.insert(relation_symbol.to_string(), Vec::from_iter(facts));
        }
    }
}