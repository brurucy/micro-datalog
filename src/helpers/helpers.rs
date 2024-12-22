use std::collections::HashSet;
use datalog_syntax::*;
use crate::program_transformations::adorned_atom::*;
use crate::program_transformations::magic_sets::*;

pub const DELTA_PREFIX: &str = "Δ";
pub const OVERDELETION_PREFIX: &str = "delete_";
pub const REDERIVATION_PREFIX: &str = "rederive_";

pub fn get_bound_vars_from_query(query: &Query) -> HashSet<String> {
    query.matchers
        .iter()
        .filter_map(|matcher| {
            match matcher {
                Matcher::Constant(val) =>
                    Some(match val {
                        TypedValue::Str(s) => s.clone(),
                        TypedValue::Int(i) => i.to_string(),
                        TypedValue::Bool(b) => b.to_string(),
                    }),
                Matcher::Any => None,
            }
        })
        .collect()
}

pub fn query_to_terms(query: &Query) -> Vec<Term> {
    query.matchers
        .iter()
        .enumerate()
        .map(|(i, matcher)| {
            match matcher {
                // Keep actual constants
                Matcher::Constant(val) => Term::Constant(val.clone()),
                // Use _i for wildcards
                Matcher::Any => Term::Variable(format!("_{}", i)),
            }
        })
        .collect()
}
pub fn get_rules_for_predicate<'a>(program: &'a Program, pred_symbol: &str) -> Vec<&'a Rule> {
    program.inner
        .iter()
        .filter(|rule| rule.head.symbol == pred_symbol)
        .collect()
}

pub fn is_derived_predicate(rule: &Rule, pred_symbol: &str) -> bool {
    // A predicate is derived if it appears in any rule head
    pred_symbol == rule.head.symbol
}

pub fn add_prefix(symbol: &mut String, prefix: &str) {
    *symbol = format!("{}{}", prefix, symbol);
}

pub fn strip_prefix(symbol: &mut String, prefix: &str) {
    *symbol = symbol.strip_prefix(prefix).unwrap().to_string();
}

pub fn split_program(program: Program) -> (Program, Program) {
    let mut nonrecursive = vec![];
    let mut recursive = vec![];

    program.inner.into_iter().for_each(|rule| {
        let head_symbol = rule.head.symbol.as_str();

        if
            rule.body
                .iter()
                .map(|body_atom| &body_atom.symbol)
                .any(|body_atom_symbol| head_symbol == body_atom_symbol)
        {
            recursive.push(rule);
        } else {
            nonrecursive.push(rule);
        }
    });

    (Program::from(nonrecursive), Program::from(recursive))
}

/// Computes which variables are bound at a given position in a rule body
pub fn compute_bound_vars_at_position(
    rule: &Rule,
    position: usize,
    initial_bound_vars: &HashSet<String>
) -> HashSet<String> {
    let mut bound_vars = initial_bound_vars.clone();

    // For each previous predicate up to position
    for i in 0..position {
        let prev_atom = &rule.body[i];
        
        // A variable becomes bound in a predicate if:
        // 1. Another variable in that predicate is bound AND
        // 2. The predicate is EDB (base predicate)
        if !is_derived_predicate(rule, &prev_atom.symbol) {
            let mut new_bound_vars = HashSet::new();
            
            // Check if any variables in this predicate are already bound
            let has_bound_var = prev_atom.terms.iter().any(|term| {
                if let Term::Variable(var) = term {
                    bound_vars.contains(var)
                } else {
                    false
                }
            });

            // If we have a bound variable, all variables in this predicate become bound
            if has_bound_var {
                for term in &prev_atom.terms {
                    if let Term::Variable(var) = term {
                        new_bound_vars.insert(var.clone());
                    }
                }
            }

            bound_vars.extend(new_bound_vars);
        }
    }

    bound_vars
}

/// Creates the body for a magic rule
pub fn create_magic_rule_body(
    rule: &Rule,
    position: usize,
    adorned_head: &AdornedAtom
) -> Vec<Atom> {
    let mut body = Vec::new();

    // Add magic predicate for the rule head
    body.push(make_magic_predicate(adorned_head));

    // Add all predicates up to this position
    for i in 0..position {
        body.push(rule.body[i].clone());
    }

    body
}

/// Creates an adorned version of the head predicate
pub fn create_adorned_head_predicate(original_head: &Atom, adorned_head: &AdornedAtom) -> Atom {
    Atom {
        symbol: format!("{}_{}", original_head.symbol, adorned_head.get_pattern_string()),
        terms: original_head.terms.clone(),
        sign: true,
    }
}

pub fn make_magic_predicate_name(adorned_atom: &AdornedAtom) -> String {
    format!("magic_{}_{}", adorned_atom.atom.symbol, adorned_atom.get_pattern_string())
}

/// Modifies a body predicate with its adornment
pub fn modify_body_predicate(original_body: &Atom, adorned_body: &AdornedAtom) -> Atom {
    Atom {
        symbol: format!("{}_{}", original_body.symbol, adorned_body.get_pattern_string()),
        terms: original_body.terms.clone(),
        sign: original_body.sign,
    }
}

pub fn get_bound_terms_from_adorned(adorned: &AdornedAtom) -> Vec<Term> {
    adorned.atom.terms
        .iter()
        .zip(adorned.adornment.iter())
        .filter_map(|(term, adornment)| {
            match adornment {
                Adornment::Bound => Some(term.clone()),
                Adornment::Free => None,
            }
        })
        .collect()
}

// Use when we need variable names as strings
pub fn get_bound_vars_from_adorned(adorned: &AdornedAtom) -> HashSet<String> {
    get_bound_terms_from_adorned(adorned)
        .into_iter()
        .filter_map(|term| {
            match term {
                Term::Variable(var) => Some(var),
                _ => None,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::helpers::helpers::split_program;
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use datalog_rule_macro::rule;

    use super::*;

    /* 
    #[test]
    fn test_collect_new_adorned_binary_predicate() {
        // Test basic case: ancestor(X,Z) :- parent(X,Y), ancestor(Y,Z)
        // If X is bound, Y becomes bound through parent
        let rule =
            rule! { 
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)] 
        };

        let adorned_head = AdornedAtom {
            atom: Atom {
                symbol: "ancestor".to_string(),
                terms: vec![Term::Variable("x".to_string()), Term::Variable("z".to_string())],
                sign: true,
            },
            adornment: vec![Adornment::Bound, Adornment::Free],
        };

        let new_adorned = collect_new_adorned_predicates(&rule, &adorned_head);
        assert_eq!(new_adorned.len(), 1);
        // Y should be bound in ancestor(Y,Z) because it's connected to bound X through parent
        assert_eq!(new_adorned[0].adornment, vec![Adornment::Bound, Adornment::Free]);
    }

    #[test]
    fn test_collect_new_adorned_multiple_predicates() {
        // Test chain: p(X,W) :- edge1(X,Y), edge2(Y,Z), edge3(Z,W), p(W,V)
        // X bound -> Y bound through edge1 -> Z bound through edge2 -> W bound through edge3
        let rule =
            rule! {
            p(?x, ?w) <- [edge1(?x, ?y), edge2(?y, ?z), edge3(?z, ?w), p(?w, ?v)]
        };

        let adorned_head = AdornedAtom {
            atom: Atom {
                symbol: "p".to_string(),
                terms: vec![Term::Variable("x".to_string()), Term::Variable("w".to_string())],
                sign: true,
            },
            adornment: vec![Adornment::Bound, Adornment::Free],
        };

        let new_adorned = collect_new_adorned_predicates(&rule, &adorned_head);
        assert_eq!(new_adorned.len(), 1);
        // First argument of p(W,V) should be bound because W is connected to bound X through chain
        assert_eq!(new_adorned[0].adornment, vec![Adornment::Bound, Adornment::Free]);
    }

    #[test]
    fn test_collect_new_adorned_independent_predicates() {
        // Test independent predicates: p(X,W) :- e1(X,Y), e2(Z,W), p(W,V)
        // Z,W are not connected to bound X through e1, so should not be bound
        let rule = rule! {
            p(?x, ?w) <- [e1(?x, ?y), e2(?z, ?w), p(?w, ?v)]
        };

        let adorned_head = AdornedAtom {
            atom: Atom {
                symbol: "p".to_string(),
                terms: vec![Term::Variable("x".to_string()), Term::Variable("w".to_string())],
                sign: true,
            },
            adornment: vec![Adornment::Bound, Adornment::Free],
        };

        let new_adorned = collect_new_adorned_predicates(&rule, &adorned_head);
        assert_eq!(new_adorned.len(), 1);
        // W should not be bound because it's not connected to X
        assert_eq!(new_adorned[0].adornment, vec![Adornment::Free, Adornment::Free]);
    }

    #[test]
    fn test_collect_new_adorned_ternary_predicate() {
        // Test with ternary predicate like triple(X,Y,Z)
        let rule = rule! {
            p(?x, ?w) <- [triple(?x, ?y, ?z), p(?z, ?w)]
        };

        let adorned_head = AdornedAtom {
            atom: Atom {
                symbol: "p".to_string(),
                terms: vec![Term::Variable("x".to_string()), Term::Variable("w".to_string())],
                sign: true,
            },
            adornment: vec![Adornment::Bound, Adornment::Free],
        };

        let new_adorned = collect_new_adorned_predicates(&rule, &adorned_head);
        assert_eq!(new_adorned.len(), 1);
        assert_eq!(new_adorned[0].adornment, vec![Adornment::Bound, Adornment::Free]);
    }

    #[test]
    fn test_collect_new_adorned_no_bound_vars() {
        // Test when no variables are bound
        let rule = rule! {
            p(?x, ?y) <- [edge(?x, ?z), p(?z, ?y)]
        };

        let adorned_head = AdornedAtom {
            atom: Atom {
                symbol: "p".to_string(),
                terms: vec![Term::Variable("x".to_string()), Term::Variable("y".to_string())],
                sign: true,
            },
            adornment: vec![Adornment::Free, Adornment::Free],
        };

        let new_adorned = collect_new_adorned_predicates(&rule, &adorned_head);
        assert_eq!(new_adorned.len(), 1);
        assert_eq!(new_adorned[0].adornment, vec![Adornment::Free, Adornment::Free]);
    }

    #[test]
    fn test_compute_bound_vars_at_position() {
        let rule = rule! { p(?x, ?z) <- [q(?x, ?y), r(?y, ?z)] };
        let mut initial_bound = HashSet::new();
        initial_bound.insert("x".to_string());

        let bound_at_pos_1 = compute_bound_vars_at_position(&rule, 1, &initial_bound);
        assert!(bound_at_pos_1.contains("x"));
        assert!(bound_at_pos_1.contains("y"));
    }
*/
    #[test]
    fn test_create_magic_rule_body() {
        let rule = rule! { p(?x, ?z) <- [q(?x, ?y), r(?y, ?z)] };
        let adorned_head = AdornedAtom::from_atom_and_bound_vars(
            &rule.head,
            &vec!["x".to_string()].into_iter().collect()
        );

        let body = create_magic_rule_body(&rule, 1, &adorned_head);
        assert_eq!(body.len(), 2); // magic predicate + q(?x, ?y)
    }

    #[test]
    fn test_create_adorned_head_predicate() {
        let original = Atom {
            symbol: "p".to_string(),
            terms: vec![Term::Variable("x".to_string()), Term::Variable("y".to_string())],
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
            terms: vec![Term::Variable("x".to_string()), Term::Variable("y".to_string())],
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
        let program =
            program! {
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
