use crate::helpers::helpers::*;
use crate::program_transformations::adorned_atom::*;
use datalog_rule_macro::program;
use datalog_syntax::*;
use std::collections::HashSet;

/// Applies the magic sets transformation to a Datalog program based on a query.
/// This transformation optimizes the program by restricting the computation to only
/// relevant tuples based on the query's binding pattern.
///
/// # Arguments
/// * `program` - The original Datalog program to transform
/// * `query` - The query that determines the binding pattern
///
/// # Returns
/// A new program with magic sets transformation applied
pub fn apply_magic_transformation(program: &Program, query: &Query) -> Program {
    let mut transformed_rules = Vec::with_capacity(program.inner.len() * 2); // = magic rules + modified rules
    let mut processed_adorned_preds = HashSet::new();
    let mut seen_rules = HashSet::new();
    let mut to_process = Vec::new();

    // Initialize with the query's adorned predicate
    if let Some(initial_rule) = get_rules_for_predicate(&program.inner, query.symbol).first() {
        let adornments = query
            .matchers
            .iter()
            .map(|matcher| match matcher {
                Matcher::Constant(_) => Adornment::Bound,
                Matcher::Any => Adornment::Free,
            })
            .collect();

        let initial_adorned = AdornedAtom {
            atom: initial_rule.head.clone(),
            adornment: adornments,
        };
        to_process.push(initial_adorned);
    }

    // Process adorned predicates in breadth-first order
    while let Some(adorned_pred) = to_process.pop() {
        if !processed_adorned_preds.insert(adorned_pred.clone()) {
            continue;
        }

        for rule in get_rules_for_predicate(&program.inner, &adorned_pred.atom.symbol) {
            // Process new adorned predicates
            for new_adorned_atom in
                collect_new_adorned_atoms(program, rule, &adorned_pred.adornment)
            {
                if new_adorned_atom
                    .adornment
                    .iter()
                    .any(|a| matches!(a, Adornment::Bound))
                {
                    to_process.push(new_adorned_atom);
                }
            }

   
            // Add modified original rule
            let modified_rule = modify_original_rule(program, rule, &adorned_pred);

            for modified_body_rule in modified_rule.body.clone() {
                if !is_magic_predicate(&modified_body_rule.symbol)
                    && get_rules_for_predicate(&transformed_rules, &modified_body_rule.symbol)
                        .is_empty()
                {
                    let adorned_atom = AdornedAtom::from_modified_atom(modified_body_rule);
                    if is_derived_predicate(&program, &adorned_atom.atom.symbol) {
                        to_process.push(adorned_atom);
                    }
                }
            }

            // Add magic rules
            let magic_rules = create_magic_rules(program, &modified_rule, &adorned_pred);

            for magic_rule in magic_rules {
                let rule_str = format!("{:?}", magic_rule);

                // First check if we've seen this exact rule before
                if seen_rules.contains(&rule_str) {
                    continue;
                }

                // Then check if we already have a rule with the same head
                // let has_rule_with_same_head =
                //     transformed_rules.iter().any(|existing_rule: &Rule| {
                //         // Two rules have the same head if they have the same predicate symbol
                //         // and the same terms in the head
                //         existing_rule.head.symbol == magic_rule.head.symbol
                //             && existing_rule.head.terms == magic_rule.head.terms
                //     });

                // if has_rule_with_same_head {
                //     continue;
                // }

                seen_rules.insert(rule_str);
                transformed_rules.push(magic_rule);
            }

            let rule_str = format!("{:?}", modified_rule);
            if !seen_rules.contains(&rule_str) {
                seen_rules.insert(rule_str);
                transformed_rules.push(modified_rule);
            }
        }
    }
    Program::from(transformed_rules)
}

/// Creates a magic seed fact for a given query.
/// Returns a tuple of (magic_predicate_name, seed_fact_values)
///
/// # Arguments
/// * `query` - The query to create a seed fact for
///
/// # Returns
/// A tuple containing the magic predicate name and the seed fact values
pub fn create_magic_seed_fact(query: &Query) -> (String, AnonymousGroundAtom) {
    let pattern: String = query
        .matchers
        .iter()
        .map(|matcher| match matcher {
            Matcher::Constant(_) => 'b',
            Matcher::Any => 'f',
        })
        .collect();

    let magic_pred = format!("magic_{}_{}", query.symbol, pattern);

    let seed_fact: Vec<TypedValue> = query
        .matchers
        .iter()
        .filter_map(|matcher| match matcher {
            Matcher::Constant(val) => Some(val.clone()),
            Matcher::Any => None,
        })
        .collect();

    (magic_pred, seed_fact)
}

fn create_magic_rules(
    program: &Program,
    modified_rule: &Rule,
    adorned_head_atom: &AdornedAtom,
) -> Vec<Rule> {
    let mut magic_rules = Vec::new();
    let mut binding_chain = Vec::new();
    let mut bound_variables = get_bound_vars_from_adorned_atom(adorned_head_atom);

    for (i, body_atom) in modified_rule.body.iter().enumerate() {
        if is_magic_predicate(&body_atom.symbol) {
            binding_chain.push(body_atom.clone());
            continue;
        }

        // let uses_bound_vars = body_atom.terms.iter().any(|term| {
        //     if let Term::Variable(var) = term {
        //         bound_variables.contains(var)
        //     } else {
        //         false
        //     }
        // });

        // if !uses_bound_vars {
        //     continue;
        // }

        let (pred_name, _binding_pattern) = get_pred_name_and_binding_pattern(&body_atom.symbol);
        if !is_derived_predicate(program, &pred_name) {
            binding_chain.push(body_atom.clone());
            // Update bound variables
            for term in &body_atom.terms {
                if let Term::Variable(var) = term {
                    bound_variables.insert(var.into());
                }
            }
            continue;
        } else {

            let magic_head = make_magic_atom(&create_adorned_atom_from_adorned_pred(body_atom));
            if !magic_head.terms.is_empty() {
                let has_magic_atoms_besides_itself_in_binding_chain = (!binding_chain.iter().any(|atom| {
                    atom.symbol == magic_head.symbol && atom.terms == magic_head.terms
                }) || binding_chain.len() > 1);
                // i > 0 because we don't want to create a magic rule with only a magic atom in the body
                if i > 0
                    && has_magic_atoms_besides_itself_in_binding_chain
                {
                    magic_rules.push(Rule {
                        head: magic_head,
                        body: binding_chain.clone(),
                        id: 0,
                    });
                  
                }
            }
        }

        // Add adorned body atom to binding chain
        binding_chain.push(body_atom.clone());

        // Update bound variables
        for term in &body_atom.terms {
            if let Term::Variable(var) = term {
                bound_variables.insert(var.clone());
            }
        }
    }

    magic_rules
}

/// Modifies an original rule by adding magic predicates and updating adornments
pub fn modify_original_rule(
    program: &Program,
    rule: &Rule,
    adorned_head_atom: &AdornedAtom,
) -> Rule {
    // create binding magic predicate for the body of the rule
    let bound_terms: Vec<Term> = rule
        .head
        .terms
        .iter()
        .zip(adorned_head_atom.adornment.iter())
        .filter_map(|(term, adornment)| match adornment {
            Adornment::Bound => Some(term.clone()),
            Adornment::Free => None,
        })
        .collect();

    // create modified body
    let mut new_body = Vec::with_capacity(rule.body.len() + 1);
    if !bound_terms.is_empty() {
        let magic_predicate = Atom {
            symbol: make_magic_predicate_name(adorned_head_atom),
            terms: bound_terms.clone(),
            sign: true,
        };

        new_body.push(magic_predicate);
    }

    let mut current_bound_vars = bound_terms
        .clone()
        .into_iter()
        .filter_map(|term| match term {
            Term::Variable(var) => Some(var),
            _ => None,
        })
        .collect();

    let mut last_derived_pos: usize;
    for (current_pos, body_atom) in rule.body.iter().enumerate() {
        if is_derived_predicate(program, &body_atom.symbol) {
            last_derived_pos = current_pos;
            let bound_vars_at_pos = compute_bound_vars_at_position(
                rule,
                &current_bound_vars,
                current_pos,
                last_derived_pos,
                program,
            );
            let adorned_body_atom =
                AdornedAtom::from_atom_and_bound_vars(body_atom, &bound_vars_at_pos);
            new_body.push(adorn_body_predicate(
                &adorned_head_atom.atom,
                &adorned_body_atom,
            ));

            current_bound_vars.extend(get_bound_vars_from_adorned_atom(&adorned_body_atom));
        } else {
            for term in &body_atom.terms {
                if let Term::Variable(var) = term {
                    current_bound_vars.insert(var.clone());
                }
            }

            new_body.push(body_atom.clone());
        }
    }

    Rule {
        head: create_adorned_head_predicate(AdornedAtom::from_atom_and_bound_vars(
            &rule.head,
            &bound_terms
                .into_iter()
                .filter_map(|term| match term {
                    Term::Variable(var) => Some(var),
                    _ => None,
                })
                .collect(),
        )),
        body: new_body,
        id: 0,
    }
}

/// Creates a magic predicate from an adorned atom
fn make_magic_atom(adorned_atom: &AdornedAtom) -> Atom {
    let bound_terms: Vec<Term> = adorned_atom
        .atom
        .terms
        .iter()
        .zip(adorned_atom.adornment.iter())
        .filter(|(_, adornment)| matches!(adornment, Adornment::Bound))
        .map(|(term, _)| term.clone())
        .collect();

    Atom {
        symbol: make_magic_predicate_name(adorned_atom),
        terms: bound_terms,
        sign: true,
    }
}

/// Creates a new adorned atom with the same adornment pattern as the head
fn create_adorned_body_atom(body_atom: &Atom, head_adornment: &[Adornment]) -> AdornedAtom {
    AdornedAtom {
        atom: body_atom.clone(),
        adornment: head_adornment.to_vec(),
    }
}

fn create_adorned_atom_from_adorned_pred(atom: &Atom) -> AdornedAtom {
    let (pred_name, binding_pattern) = get_pred_name_and_binding_pattern(&atom.symbol);
    AdornedAtom {
        atom: Atom {
            symbol: pred_name,
            terms: atom.terms.clone(),
            sign: true,
        },
        adornment: binding_pattern
            .iter()
            .map(|b| match b.as_str() {
                "b" => Adornment::Bound,
                "f" => Adornment::Free,
                _ => panic!("Invalid binding pattern: {}", b.as_str()),
            })
            .collect(),
    }
}

/// Checks if a predicate is derived (appears in the head of any rule)
fn is_derived_predicate(program: &Program, symbol: &str) -> bool {
    program.inner.iter().any(|rule| rule.head.symbol == symbol)
}

fn is_magic_predicate(symbol: &str) -> bool {
    symbol.starts_with("magic_")
}

fn collect_new_adorned_atoms<'a>(
    program: &'a Program,
    rule: &'a Rule,
    adornment: &'a [Adornment],
) -> Vec<AdornedAtom> {
    let adorned_atom = AdornedAtom {
        atom: rule.head.clone(),
        adornment: adornment.to_vec(),
    };
    let mut new_adorned_atoms = Vec::new();
    let mut current_bound_vars: HashSet<String> = get_bound_vars_from_adorned_atom(&adorned_atom);
    let mut last_derived_pos: usize;

    for (current_pos, body_atom) in rule.body.iter().enumerate() {
        if is_derived_predicate(program, &body_atom.symbol) {
            // Create an adorned atom for this position
            let adorned_body_atom =
                AdornedAtom::from_atom_and_bound_vars(body_atom, &current_bound_vars);

            if adorned_body_atom
                .adornment
                .iter()
                .any(|a| matches!(a, Adornment::Bound))
            {
                for term in &body_atom.terms {
                    if let Term::Variable(var) = term {
                        current_bound_vars.insert(var.clone());
                    }
                }
            }

            // Update bound variables
            current_bound_vars.extend(get_bound_vars_from_adorned_atom(&adorned_body_atom));
            new_adorned_atoms.push(adorned_body_atom);
        } else {
            // Add all variables from this base predicate to bound vars
            for term in &body_atom.terms {
                if let Term::Variable(var) = term {
                    current_bound_vars.insert(var.clone());
                }
            }
        }
    }

    new_adorned_atoms
}

/// Gets all rules that define a given predicate
fn get_rules_for_predicate<'a>(all_rules: &'a Vec<Rule>, symbol: &str) -> Vec<&'a Rule> {
    all_rules
        .iter()
        .filter(|rule| rule.head.symbol == symbol)
        .collect()
}
