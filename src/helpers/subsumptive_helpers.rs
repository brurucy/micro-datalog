use std::collections::{HashMap, HashSet};

use datalog_syntax::{AnonymousGroundAtom, Atom, Term, TypedValue};

pub fn create_subquery_pattern(
    atom: &Atom,
    bindings: &HashMap<String, TypedValue>,
) -> Vec<Option<TypedValue>> {
    // Purpose: Creates a query pattern based on variable bindings
    // - For each term in the atom:
    //   - If constant: use as bound value in pattern
    //   - If variable with binding: use binding as bound value
    //   - If variable without binding: use None (free)
    // - Returns a pattern vector with Some(value) for bound positions, None for free

    atom.terms
        .iter()
        .map(|term| match term {
            Term::Constant(val) => Some(val.clone()),
            Term::Variable(var) => bindings.get(var).cloned(),
        })
        .collect()
}

pub fn update_bindings(
    bindings: &mut HashMap<String, TypedValue>,
    atom: &Atom,
    results: &HashSet<AnonymousGroundAtom>,
) {
    // Purpose: Updates variable bindings based on query results
    // - Takes results from evaluating an atom and extracts variable bindings
    // - For each variable in the atom, if there's a corresponding value in a result,
    //   add it to the bindings map
    // - Note: This function assumes a single result tuple; with multiple results,
    //   it would only use the first one (in practice, this would be called in a loop)

    // Get one result to update bindings (ideally we'd handle multiple results)
    if let Some(result) = results.iter().next() {
        // Map each variable in the atom to its corresponding value in the result
        atom.terms.iter().enumerate().for_each(|(i, term)| {
            if let Term::Variable(var) = term {
                if i < result.len() {
                    // Added safety check
                    bindings.insert(var.clone(), result[i].clone());
                }
            }
        });
    }
}

pub fn create_result(
    head: &Atom,
    bindings: &HashMap<String, TypedValue>,
) -> Option<AnonymousGroundAtom> {
    // Purpose: Creates a result tuple from the head pattern using variable bindings
    // - Attempts to create a result by substituting variables with their bindings
    // - For each term in the head:
    //   - If constant: use that value
    //   - If variable: use its binding if available
    // - Returns None if any variable is unbound (can't create complete result)

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
                    // Can't create result if any variable is unbound
                    return None;
                }
            }
        }
    }

    Some(result)
}

pub fn subsumes(subsuming: &[Option<TypedValue>], subsumed: &[Option<TypedValue>]) -> bool {
    if subsuming.len() != subsumed.len() {
        return false;
    }

    subsuming.iter().zip(subsumed).all(|(s, p)| {
        match (s, p) {
            (None, _) => true, // Free variable subsumes anything
            (Some(s_val), Some(p_val)) => s_val == p_val,
            _ => false,
        }
    })
}
