use std::collections::HashSet;
use datalog_syntax::*;
use crate::program_transformations::adorned_atom::*;

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

pub fn split_program(program: Program) -> (Program, Program) {
    let mut nonrecursive = vec![];
    let mut recursive = vec![];

    program.inner.into_iter().for_each(|rule| {
        let head_symbol = rule.head.symbol.as_str();
        
        // A rule is recursive if:
        // 1. It contains the head predicate in its body, OR
        // 2. It contains a magic predicate 
        let is_recursive = rule.body.iter().any(|body_atom| {
            head_symbol == body_atom.symbol ||  // Traditional recursion
            body_atom.symbol.starts_with("magic_") // Magic predicates make it recursive
        });

        if is_recursive {
            recursive.push(rule);
        } else {
            nonrecursive.push(rule);
        }
    });

    println!("Split result:");
    println!("Nonrecursive: {:?}", nonrecursive);
    println!("Recursive: {:?}", recursive);

    (Program::from(nonrecursive), Program::from(recursive))
}

pub fn compute_bound_vars_at_position(
    rule: &Rule,
    pos: usize,
    initial_bound_vars: &HashSet<String>
) -> HashSet<String> {
    println!("\n=== Computing bound vars at position {} ===", pos);
    println!("Initial bound vars: {:?}", initial_bound_vars);

    let mut bound_vars = initial_bound_vars.clone();

    // Process predicates sequentially
    for i in 0..pos {
        let atom = &rule.body[i];
        println!("\nProcessing predicate at position {}: {:?}", i, atom);

        if !is_derived_predicate(rule, &atom.symbol) {
            // For base predicates like flat
            let connects_to_bound = atom.terms.iter().any(|term| {
                if let Term::Variable(var) = term {
                    let is_bound = bound_vars.contains(var);
                    println!("  Checking variable {} - bound? {}", var, is_bound);
                    is_bound
                } else {
                    false
                }
            });

            if connects_to_bound {
                println!("  Base predicate connects to bound vars - binding all variables");
                for term in &atom.terms {
                    if let Term::Variable(var) = term {
                        bound_vars.insert(var.clone());
                        println!("    Added {}", var);
                    }
                }
            }
        } else {
            // For derived predicates like sg
            let connects_to_bound = atom.terms.iter().any(|term| {
                if let Term::Variable(var) = term {
                    let is_bound = bound_vars.contains(var);
                    println!("  Checking variable {} - bound? {}", var, is_bound);
                    is_bound
                } else {
                    false
                }
            });

            if connects_to_bound {
                println!("  Derived predicate connects to bound vars");
                // For derived predicates with bf pattern:
                // 1. First argument becomes bound (as before)
                if let Some(Term::Variable(first_var)) = atom.terms.first() {
                    bound_vars.insert(first_var.clone());
                    println!("    Added first arg {}", first_var);
                }
                // 2. Second argument also becomes bound since we know its value
                //    will be computed through the bf pattern
                if let Some(Term::Variable(second_var)) = atom.terms.get(1) {
                    bound_vars.insert(second_var.clone());
                    println!("    Added second arg {} (from bf pattern)", second_var);
                }
            }
        }

        println!("Current bound vars: {:?}", bound_vars);
    }

    bound_vars
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

pub fn create_adorned_query(query: &Query) -> Query<'static> {
    // Leak the string but it's ok since it lives for the duration of the query
    let symbol = Box::leak(format!("{}_bf", query.symbol).into_boxed_str());
    let mut builder = QueryBuilder::new(symbol);
    
    for matcher in &query.matchers {
        match matcher {
            Matcher::Any => builder.with_any(),
            Matcher::Constant(val) => builder.with_constant(val.clone())
        }
    }
    
    builder.query
}

#[cfg(test)]
mod tests {
    use crate::helpers::helpers::split_program;
    use datalog_rule_macro::program;
    use datalog_syntax::*;

    use super::*;

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
