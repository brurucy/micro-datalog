use crate::helpers::helpers::*;
use crate::program_transformations::adorned_atom::*;
use datalog_syntax::*;
use std::collections::HashSet;

pub fn apply_magic_transformation(program: &Program, query: &Query) -> Program {
    let mut transformed_rules = Vec::new();
    let mut processed_adorned_preds = HashSet::new();
    let mut seen_rules = HashSet::new();
    let mut to_process = Vec::new();

    if let Some(initial_rule) = get_rules_for_predicate(program, query.symbol).first() {
        let mut adornments = vec![Adornment::Free; query.matchers.len()];
        for (i, matcher) in query.matchers.iter().enumerate() {
            if let Matcher::Constant(_) = matcher {
                adornments[i] = Adornment::Bound;
            }
        }

        let initial_adorned = AdornedAtom {
            atom: initial_rule.head.clone(),
            adornment: adornments,
        };
        to_process.push(initial_adorned);
    }

    while let Some(adorned_pred) = to_process.pop() {
        if processed_adorned_preds.contains(&adorned_pred) {
            continue;
        }
        processed_adorned_preds.insert(adorned_pred.clone());

        for rule in get_rules_for_predicate(program, &adorned_pred.atom.symbol) {
            // Add any new adorned predicates to process
            for new_adorned in collect_new_adorned_predicates(program, rule, &adorned_pred) {
                let has_bound_var = new_adorned
                    .adornment
                    .iter()
                    .any(|a| matches!(a, Adornment::Bound));

                if has_bound_var {
                    to_process.push(new_adorned);
                }
            }

            // Create and deduplicate magic rules
            let magic_rules = create_magic_rules(program, rule, &adorned_pred);
            for magic_rule in magic_rules {
                let rule_str = format!("{:?}", magic_rule);

                // First check if we've seen this exact rule before
                if seen_rules.contains(&rule_str) {
                    continue;
                }

                // Then check if we already have a rule with the same head
                let has_rule_with_same_head =
                    transformed_rules.iter().any(|existing_rule: &Rule| {
                        // Two rules have the same head if they have the same predicate symbol
                        // and the same terms in the head
                        existing_rule.head.symbol == magic_rule.head.symbol
                            && existing_rule.head.terms == magic_rule.head.terms
                    });

                if has_rule_with_same_head {
                    continue;
                }
                seen_rules.insert(rule_str);
                transformed_rules.push(magic_rule);
            }

            // Create and deduplicate modified rule
            let modified_rule = modify_original_rule(program, rule, &adorned_pred);
            let rule_str = format!("{:?}", modified_rule);
            if !seen_rules.contains(&rule_str) {
                seen_rules.insert(rule_str);
                transformed_rules.push(modified_rule);
            }
        }
    }

    Program::from(transformed_rules)
}

/// Creates a magic seed fact for a given query
pub fn create_magic_seed_fact(query: &Query) -> (String, AnonymousGroundAtom) {
    // Create binding pattern string based on actual bindings in query
    let pattern: String = query
        .matchers
        .iter()
        .map(|matcher| match matcher {
            Matcher::Constant(_) => 'b',
            Matcher::Any => 'f',
        })
        .collect();

    // Format is "magic_<pred>_<pattern>" to match the binding pattern
    let magic_pred = format!("magic_{}_{}", query.symbol, pattern);

    // Get the bound values from the query to create seed fact
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

fn create_magic_rules(program: &Program, rule: &Rule, adorned_head: &AdornedAtom) -> Vec<Rule> {
    let mut magic_rules = Vec::new();

    // Track all predicates seen so far that contribute to binding propagation
    let mut binding_chain = vec![make_magic_predicate(adorned_head)];

    // Track variables that can potentially propagate bindings
    let mut bound_variables = get_bound_vars_from_adorned(adorned_head);

    // First pass: Process each predicate in sequence, building up binding chains
    for (_pos, body_atom) in rule.body.iter().enumerate() {
        // If this is a base predicate that uses any bound variables,
        // add it to our binding chain because it contributes to binding propagation
        if !is_derived_predicate(program, &body_atom.symbol) {
            let uses_bound_vars = body_atom.terms.iter().any(|term| {
                if let Term::Variable(var) = term {
                    bound_variables.contains(var)
                } else {
                    false
                }
            });

            if uses_bound_vars {
                binding_chain.push(body_atom.clone());

                // Add any new variables that become bound through this predicate
                for term in &body_atom.terms {
                    if let Term::Variable(var) = term {
                        if bound_variables.contains(var) {
                            // If this predicate uses a bound variable, all its variables
                            // participate in the binding chain
                            for other_term in &body_atom.terms {
                                if let Term::Variable(other_var) = other_term {
                                    bound_variables.insert(other_var.clone());
                                }
                            }
                        }
                    }
                }
            }
            continue;
        }

        let uses_bound_vars = body_atom.terms.iter().any(|term| {
            if let Term::Variable(var) = term {
                bound_variables.contains(var)
            } else {
                false
            }
        });

        if uses_bound_vars {
            let magic_head = make_magic_predicate(
                &(AdornedAtom {
                    atom: body_atom.clone(),
                    adornment: adorned_head.adornment.clone(),
                }),
            );

            if !binding_chain
                .iter()
                .any(|atom| atom.symbol == magic_head.symbol && atom.terms == magic_head.terms)
            {
                let magic_rule = Rule {
                    head: magic_head,
                    body: binding_chain.clone(),
                    id: 0,
                };
                magic_rules.push(magic_rule);
            }

            // Add the adorned version of this predicate to the binding chain
            binding_chain.push(modify_body_predicate(
                body_atom,
                &(AdornedAtom {
                    atom: body_atom.clone(),
                    adornment: adorned_head.adornment.clone(),
                }),
            ));

            // Update bound variables to include outputs from this predicate
            for term in &body_atom.terms {
                if let Term::Variable(var) = term {
                    bound_variables.insert(var.clone());
                }
            }
        }
    }
    magic_rules
}

pub fn collect_new_adorned_predicates(
    program: &Program,
    rule: &Rule,
    adorned_head: &AdornedAtom,
) -> Vec<AdornedAtom> {
    let mut new_adorned = Vec::new();
    let mut current_bound_vars = get_bound_vars_from_adorned(adorned_head);

    for (pos, body_atom) in rule.body.iter().enumerate() {
        if is_derived_predicate(program, &body_atom.symbol) {
            let bound_vars_at_pos =
                compute_bound_vars_at_position(program, rule, pos, &current_bound_vars);

            let adorned_body = AdornedAtom::from_atom_and_bound_vars(body_atom, &bound_vars_at_pos);
            // Update bound variables
            current_bound_vars.extend(get_bound_vars_from_adorned(&adorned_body));

            // Push the adorned body after using it to update bound vars
            new_adorned.push(adorned_body);
        }
    }
    new_adorned
}

pub fn modify_original_rule(program: &Program, rule: &Rule, adorned_head: &AdornedAtom) -> Rule {
    let mut new_body = Vec::new();

    let magic_terms: Vec<Term> = rule
        .head
        .terms
        .iter()
        .zip(adorned_head.adornment.iter())
        .filter_map(|(term, adornment)| match adornment {
            Adornment::Bound => Some(term.clone()),
            Adornment::Free => None,
        })
        .collect();

    let magic_predicate = Atom {
        symbol: make_magic_predicate_name(adorned_head),
        terms: magic_terms.clone(),
        sign: true,
    };
    new_body.push(magic_predicate);

    for (_pos, body_atom) in rule.body.iter().enumerate() {
        if is_derived_predicate(program, &body_atom.symbol) {
            // Use the same adornment pattern as the head for recursive predicates
            let adornment = adorned_head.adornment.clone();
            let adorned_body = AdornedAtom {
                atom: body_atom.clone(),
                adornment: adornment,
            };
            let modified_predicate = modify_body_predicate(body_atom, &adorned_body);
            new_body.push(modified_predicate);
        } else {
            new_body.push(body_atom.clone());
        }
    }

    let modified_head = create_adorned_head_predicate(&rule.head, adorned_head);

    let modified_rule = Rule {
        head: modified_head,
        body: new_body,
        id: 0,
    };

    modified_rule
}

pub fn make_magic_predicate(adorned_atom: &AdornedAtom) -> Atom {
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
