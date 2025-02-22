use crate::program_transformations::adorned_atom::*;
use datalog_syntax::*;
use indexmap::IndexSet;
use std::collections::HashSet;

pub fn get_rules_for_predicate<'a>(program: &'a Program, pred_symbol: &str) -> Vec<&'a Rule> {
    program
        .inner
        .iter()
        .filter(|rule| rule.head.symbol == pred_symbol)
        .collect()
}

pub fn is_derived_predicate(program: &Program, pred_symbol: &str) -> bool {
    program
        .inner
        .iter()
        .any(|rule| rule.head.symbol == pred_symbol)
}

pub fn split_program(program: Program) -> (Program, Program) {
    let mut nonrecursive = vec![];
    let mut recursive = vec![];

    let idb_relations = program
        .inner
        .iter()
        .map(|r| r.head.symbol.as_str())
        .collect::<IndexSet<_>>();

    program.inner.iter().for_each(|rule| {
        if rule
            .body
            .iter()
            .map(|body_atom| &body_atom.symbol)
            .any(|body_atom_symbol| idb_relations.contains(body_atom_symbol.as_str()))
        {
            recursive.push(rule.clone());
        } else {
            nonrecursive.push(rule.clone());
        }
    });

    (Program::from(nonrecursive), Program::from(recursive))
}

pub fn compute_bound_vars_at_position(
    program: &Program,
    rule: &Rule,
    pos: usize,
    initial_bound_vars: &HashSet<String>,
) -> HashSet<String> {
    let mut bound_vars = initial_bound_vars.clone();

    // Process predicates sequentially
    for i in 0..pos {
        let atom = &rule.body[i];

        if !is_derived_predicate(program, &atom.symbol) {
            // For base predicates like flat
            let connects_to_bound = atom.terms.iter().any(|term| {
                if let Term::Variable(var) = term {
                    let is_bound = bound_vars.contains(var);
                    is_bound
                } else {
                    false
                }
            });

            if connects_to_bound {
                for term in &atom.terms {
                    if let Term::Variable(var) = term {
                        bound_vars.insert(var.clone());
                    }
                }
            }
        } else {
            // For derived predicates like sg
            let connects_to_bound = atom.terms.iter().any(|term| {
                if let Term::Variable(var) = term {
                    let is_bound = bound_vars.contains(var);
                    is_bound
                } else {
                    false
                }
            });

            if connects_to_bound {
                // For derived predicates with bf pattern:
                // 1. First argument becomes bound (as before)
                if let Some(Term::Variable(first_var)) = atom.terms.first() {
                    bound_vars.insert(first_var.clone());
                }
                // 2. Second argument also becomes bound since we know its value
                //    will be computed through the bf pattern
                if let Some(Term::Variable(second_var)) = atom.terms.get(1) {
                    bound_vars.insert(second_var.clone());
                }
            }
        }
    }

    bound_vars
}

/// Creates an adorned version of the head predicate
pub fn create_adorned_head_predicate(original_head: &Atom, adorned_head: &AdornedAtom) -> Atom {
    Atom {
        symbol: format!(
            "{}_{}",
            original_head.symbol,
            adorned_head.get_pattern_string()
        ),
        terms: original_head.terms.clone(),
        sign: true,
    }
}

pub fn make_magic_predicate_name(adorned_atom: &AdornedAtom) -> String {
    format!(
        "magic_{}_{}",
        adorned_atom.atom.symbol,
        adorned_atom.get_pattern_string()
    )
}

/// Modifies a body predicate with its adornment
pub fn modify_body_predicate(original_body: &Atom, adorned_body: &AdornedAtom) -> Atom {
    Atom {
        symbol: format!(
            "{}_{}",
            original_body.symbol,
            adorned_body.get_pattern_string()
        ),
        terms: original_body.terms.clone(),
        sign: original_body.sign,
    }
}

pub fn get_bound_terms_from_adorned(adorned: &AdornedAtom) -> Vec<Term> {
    adorned
        .atom
        .terms
        .iter()
        .zip(adorned.adornment.iter())
        .filter_map(|(term, adornment)| match adornment {
            Adornment::Bound => Some(term.clone()),
            Adornment::Free => None,
        })
        .collect()
}

// Use when we need variable names as strings
pub fn get_bound_vars_from_adorned(adorned: &AdornedAtom) -> HashSet<String> {
    get_bound_terms_from_adorned(adorned)
        .into_iter()
        .filter_map(|term| match term {
            Term::Variable(var) => Some(var),
            _ => None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::helpers::helpers::split_program;
    use datalog_rule_macro::program;

    #[test]
    fn test_split_program_complex() {
        let stratified_program = program! {
            // Stratum 1: Base rule
            base(?x, ?y) <- [edge(?x, ?y)],

            // Stratum 2: Derived rule depends on Stratum 1
            derived(?x, ?y) <- [base(?x, ?y)],
            derived(?x, ?z) <- [base(?x, ?y), derived(?y, ?z)],

            // Stratum 3: Another level of derivation
            top(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)],
        };

        let expected_nonrecursive_program = program! {
            base(?x, ?y) <- [edge(?x, ?y)],
        };

        let expected_recursive_program = program! {
            derived(?x, ?y) <- [base(?x, ?y)],
            derived(?x, ?z) <- [base(?x, ?y), derived(?y, ?z)],
            top(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)],
        };

        let (nonrecursive_program, recursive_program) = split_program(stratified_program);

        assert_eq!(expected_nonrecursive_program, nonrecursive_program);
        assert_eq!(expected_recursive_program, recursive_program);
    }

    #[test]
    fn test_create_adorned_head_predicate() {
        let original = Atom {
            symbol: "p".to_string(),
            terms: vec![
                Term::Variable("x".to_string()),
                Term::Variable("y".to_string()),
            ],
            sign: true,
        };

        let adorned = AdornedAtom {
            atom: original.clone(),
            adornment: vec![Adornment::Bound, Adornment::Free],
        };

        let result = create_adorned_head_predicate(&original, &adorned);
        assert_eq!(result.symbol, "p_bf");
    }

    #[test]
    fn test_get_bound_vars_from_adorned() {
        let atom = Atom {
            symbol: "p".to_string(),
            terms: vec![
                Term::Variable("x".to_string()),
                Term::Variable("y".to_string()),
            ],
            sign: true,
        };

        let adorned = AdornedAtom {
            atom: atom,
            adornment: vec![Adornment::Bound, Adornment::Free],
        };

        let bound_vars = get_bound_vars_from_adorned(&adorned);
        assert!(bound_vars.contains("x"));
        assert!(!bound_vars.contains("y"));
    }

    #[test]
    fn test_split_program() {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(? x, ?z) <- [e(? x, ?y), tc(? y, ?z)]
        };

        let expected_nonrecursive_program = program! { tc(?x, ?y) <- [e(?x, ?y)] };
        let expected_recursive_program = program! { tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)] };

        let (actual_nonrecursive_program, actual_recursive_program) = split_program(program);

        assert_eq!(expected_nonrecursive_program, actual_nonrecursive_program);
        assert_eq!(expected_recursive_program, actual_recursive_program);
    }
}
