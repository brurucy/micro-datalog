use std::collections::{ HashMap, HashSet };
use datalog_syntax::{ AnonymousGroundAtom, Atom, Term, TypedValue };

#[derive(Default)]
pub struct SubsumptiveTable {
    tables: HashMap<String, Vec<(Vec<Option<TypedValue>>, Vec<AnonymousGroundAtom>)>>,
}

impl SubsumptiveTable {
    pub fn new() -> Self {
        Self {
            tables: HashMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        pred: &str,
        pattern: Vec<Option<TypedValue>>,
        facts: Vec<AnonymousGroundAtom>
    ) {
        let entries = self.tables.entry(pred.to_string()).or_default();
        entries.push((pattern, facts));
    }

    pub fn find_subsuming(
        &self,
        predicate: &str,
        pattern: &[Option<TypedValue>]
    ) -> Option<&Vec<AnonymousGroundAtom>> {
        let table = self.tables.get(predicate)?;
        // Look for a table entry that subsumes this pattern
        for (existing_pattern, facts) in table {
            if subsumes(existing_pattern, pattern) {
                return Some(facts);
            }
        }
        None
    }
}

// Helper function to check if one pattern subsumes another
fn subsumes(subsuming: &[Option<TypedValue>], subsumed: &[Option<TypedValue>]) -> bool {
    if subsuming.len() != subsumed.len() {
        return false;
    }

    subsuming
        .iter()
        .zip(subsumed)
        .all(|(s, p)| {
            match (s, p) {
                (None, _) => true, // Free variable subsumes anything
                (Some(s_val), Some(p_val)) => s_val == p_val,
                _ => false,
            }
        })
}

pub fn create_subquery_pattern(
    atom: &Atom,
    bindings: &HashMap<String, TypedValue>
) -> Vec<Option<TypedValue>> {
    atom.terms
        .iter()
        .map(|term| {
            match term {
                Term::Constant(val) => { Some(val.clone()) }
                Term::Variable(var) => {
                    match bindings.get(var) {
                        Some(val) => { Some(val.clone()) }
                        None => { None }
                    }
                }
            }
        })
        .collect()
}

pub fn update_bindings(
    bindings: &mut HashMap<String, TypedValue>,
    atom: &Atom,
    results: &HashSet<AnonymousGroundAtom>
) {
    // Get one result to update bindings (ideally we'd handle multiple results)
    if let Some(result) = results.iter().next() {
        // Map each variable in the atom to its corresponding value in the result
        atom.terms
            .iter()
            .enumerate()
            .for_each(|(i, term)| {
                if let Term::Variable(var) = term {
                    bindings.insert(var.clone(), result[i].clone());
                }
            });
    }
}

pub fn create_result(
    head: &Atom,
    bindings: &HashMap<String, TypedValue>
) -> Option<AnonymousGroundAtom> {
    // Try to create result by substituting variables with their bindings
    let mut result = Vec::new();

    for term in &head.terms {
        match term {
            Term::Constant(val) => {
                result.push(val.clone());
            }
            Term::Variable(var) => {
                if let Some(val) = bindings.get(var) {
                    result.push(val.clone());
                } else {
                    return None; // Can't create result if any variable is unbound
                }
            }
        }
    }

    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_subsumes() {
        // Test that free variables subsume bound ones
        let pattern1 = vec![None, Some(TypedValue::from("x"))];
        let pattern2 = vec![Some(TypedValue::from("y")), Some(TypedValue::from("x"))];
        assert!(subsumes(&pattern1, &pattern2));

        // Test that bound variables must match exactly
        let pattern3 = vec![Some(TypedValue::from("z")), Some(TypedValue::from("x"))];
        assert!(!subsumes(&pattern2, &pattern3));

        // Test patterns of different lengths
        let pattern4 = vec![None];
        assert!(!subsumes(&pattern4, &pattern1));
    }

    #[test]
    fn test_subsumptive_table() {
        let mut table = SubsumptiveTable::new();

        // Insert a fact with a pattern
        let fact = vec![TypedValue::from("john"), TypedValue::from("bob")];
        let pattern = vec![Some(TypedValue::from("john")), None];
        table.insert("parent", pattern.clone(), vec![fact.clone()].into_iter().collect());

        // Test finding subsuming pattern
        let query_pattern = vec![Some(TypedValue::from("john")), Some(TypedValue::from("bob"))];
        let result = table.find_subsuming("parent", &query_pattern);
        assert!(result.is_some());
        assert!(result.unwrap().contains(&fact));
    }
}
