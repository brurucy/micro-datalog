use datalog_syntax::{AnonymousGroundAtom, Atom, Term, TypedValue};
use std::collections::{HashMap, HashSet};
use crate::helpers::subsumptive_helpers::{
    subsumes
};

#[derive(Default, Debug)]
pub struct SubsumptiveTable {
    pub tables: HashMap<String, Vec<(Atom, Vec<AnonymousGroundAtom>)>>,
}

impl SubsumptiveTable {
    pub fn new() -> Self {
        Self {
            tables: HashMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        atom: &Atom,
        facts: Vec<AnonymousGroundAtom>,
    ) {
        let entries = self.tables.entry(atom.symbol.clone()).or_default();
        entries.push((atom.clone(), facts));
    }

    pub fn find_subsuming(
        &self,
        atom: &Atom,
    ) -> Option<&Vec<AnonymousGroundAtom>> {
   
        let table = self.tables.get(atom.symbol.as_str())?;
        // Look for a table entry that subsumes this pattern
        for (cached_atom, facts) in table {
            if subsumes(cached_atom, atom) {
                return Some(facts);
            }
        }

        None
    }

    pub fn print_contents(&self) {
        println!("\nTable Contents:");
        for (pred, entries) in &self.tables {
            println!("Predicate: {}", pred);
            for (pattern, facts) in entries {
                println!("  Pattern: {:?}", pattern);
                println!("  Facts: {:?}", facts);
            }
        }
    }
}


// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_subsumes() {
//         // Test that free variables subsume bound ones
//         let pattern1 = vec![None, Some(TypedValue::from("x"))];
//         let pattern2 = vec![Some(TypedValue::from("y")), Some(TypedValue::from("x"))];
//         assert!(subsumes(&pattern1, &pattern2));

//         // Test that bound variables must match exactly
//         let pattern3 = vec![Some(TypedValue::from("z")), Some(TypedValue::from("x"))];
//         assert!(!subsumes(&pattern2, &pattern3));

//         // Test patterns of different lengths
//         let pattern4 = vec![None];
//         assert!(!subsumes(&pattern4, &pattern1));
//     }

//     #[test]
//     fn test_subsumptive_table() {
//         let mut table = SubsumptiveTable::new();

//         // Insert a fact with a pattern
//         let fact = vec![TypedValue::from("john"), TypedValue::from("bob")];
//         let pattern = vec![Some(TypedValue::from("john")), None];
//         table.insert(
//             "parent",
//             pattern.clone(),
//             vec![fact.clone()].into_iter().collect(),
//         );

//         // Test finding subsuming pattern
//         let query_pattern = vec![
//             Some(TypedValue::from("john")),
//             Some(TypedValue::from("bob")),
//         ];
//         let result = table.find_subsuming("parent", &query_pattern);
//         assert!(result.is_some());
//         assert!(result.unwrap().contains(&fact));
//     }
// }
