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
    for result in results.iter() {
        atom.terms.iter().enumerate().for_each(|(i, term)| {
            if let Term::Variable(var) = term {
                if var == "_" { println!("EMPTY VAR {:?}, {:?}", result[i], atom)}
                bindings.insert(var.clone(), result[i].clone());
                
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

pub fn subsumes(subsuming: &Atom, subsumed: &Atom) -> bool {
    if subsuming.terms.len() != subsumed.terms.len() {
        return false;
    }
    let subsumed_terms = subsumed.terms.clone();

    subsuming.terms.iter().zip(subsumed_terms).all(|(s, p)| {
        match (s, p) {
            (Term::Variable(_), _) => true, // Free variable subsumes anything
            (Term::Constant(s_val), Term::Constant(p_val)) => *s_val == p_val,
            _ => false,
        }
    })
}
