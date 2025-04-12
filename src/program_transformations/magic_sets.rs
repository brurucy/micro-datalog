use crate::helpers::helpers::*;
use crate::program_transformations::adorned_atom::*;
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
    let mut transformed_rules = Vec::with_capacity(program.inner.len() * 2);
    let mut processed_adorned_preds = HashSet::new();
    let mut seen_rules = HashSet::new();
    let mut to_process = Vec::new();

    // Initialize with the query's adorned predicate
    if let Some(initial_rule) = get_rules_for_predicate(program, query.symbol).first() {
        let adornments = query.matchers.iter()
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

        for rule in get_rules_for_predicate(program, &adorned_pred.atom.symbol) {
            // Process new adorned predicates
            for new_adorned in collect_new_adorned_predicates(program, rule, &adorned_pred) {
                if new_adorned.adornment.iter().any(|a| matches!(a, Adornment::Bound)) {
                    to_process.push(new_adorned);
                }
            }

            // Add magic rules
            let magic_rules = create_magic_rules(program, rule, &adorned_pred);
            for magic_rule in magic_rules {
                let rule_str = format!("{:?}", magic_rule);

                // First check if we've seen this exact rule before
                if seen_rules.contains(&rule_str) {
                    continue;
                }

                // Then check if we already have a rule with the same head
                let has_rule_with_same_head = transformed_rules.iter().any(|existing_rule: &Rule| {
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

            // Add modified original rule
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

/// Creates a magic seed fact for a given query.
/// Returns a tuple of (magic_predicate_name, seed_fact_values)
///
/// # Arguments
/// * `query` - The query to create a seed fact for
///
/// # Returns
/// A tuple containing the magic predicate name and the seed fact values
pub fn create_magic_seed_fact(query: &Query) -> (String, AnonymousGroundAtom) {
    let pattern: String = query.matchers.iter()
        .map(|matcher| match matcher {
            Matcher::Constant(_) => 'b',
            Matcher::Any => 'f',
        })
        .collect();

    let magic_pred = format!("magic_{}_{}", query.symbol, pattern);

    let seed_fact: Vec<TypedValue> = query.matchers.iter()
        .filter_map(|matcher| match matcher {
            Matcher::Constant(val) => Some(val.clone()),
            Matcher::Any => None,
        })
        .collect();

    (magic_pred, seed_fact)
}

/// Creates magic rules for a given rule and adorned head
fn create_magic_rules(program: &Program, rule: &Rule, adorned_head: &AdornedAtom) -> Vec<Rule> {
    let mut magic_rules = Vec::new();
    let mut binding_chain = vec![make_magic_predicate(adorned_head)];
    let mut bound_variables = get_bound_vars_from_adorned(adorned_head);

    for body_atom in &rule.body {
        let uses_bound_vars = body_atom.terms.iter().any(|term| {
            if let Term::Variable(var) = term {
                bound_variables.contains(var)
            } else {
                false
            }
        });

        if !uses_bound_vars {
            continue;
        }

        if !is_derived_predicate(program, &body_atom.symbol) {
            binding_chain.push(body_atom.clone());
            // Update bound variables
            for term in &body_atom.terms {
                if let Term::Variable(var) = term {
                    bound_variables.insert(var.clone());
                }
            }
            continue;
        }

        let magic_head = make_magic_predicate(&create_adorned_body_atom(
            body_atom,
            &adorned_head.adornment,
        ));

        if !binding_chain.iter().any(|atom| {
            atom.symbol == magic_head.symbol && atom.terms == magic_head.terms
        }) {
            magic_rules.push(Rule {
                head: magic_head,
                body: binding_chain.clone(),
                id: 0,
            });
        }

        binding_chain.push(modify_body_predicate(
            body_atom,
            &create_adorned_body_atom(body_atom, &adorned_head.adornment),
        ));

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
pub fn modify_original_rule(program: &Program, rule: &Rule, adorned_head: &AdornedAtom) -> Rule {
    let magic_terms: Vec<Term> = rule.head.terms.iter()
        .zip(adorned_head.adornment.iter())
        .filter_map(|(term, adornment)| match adornment {
            Adornment::Bound => Some(term.clone()),
            Adornment::Free => None,
        })
        .collect();

    let magic_predicate = Atom {
        symbol: make_magic_predicate_name(adorned_head),
        terms: magic_terms,
        sign: true,
    };

    let mut new_body = Vec::with_capacity(rule.body.len() + 1);
    new_body.push(magic_predicate);

    for body_atom in &rule.body {
        if is_derived_predicate(program, &body_atom.symbol) {
            let adorned_body = create_adorned_body_atom(body_atom, &adorned_head.adornment);
            new_body.push(modify_body_predicate(body_atom, &adorned_body));
        } else {
            new_body.push(body_atom.clone());
        }
    }

    Rule {
        head: create_adorned_head_predicate(&rule.head, adorned_head),
        body: new_body,
        id: 0,
    }
}

/// Creates a magic predicate from an adorned atom
fn make_magic_predicate(adorned_atom: &AdornedAtom) -> Atom {
    let bound_terms: Vec<Term> = adorned_atom.atom.terms.iter()
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

/// Checks if a predicate is derived (appears in the head of any rule)
fn is_derived_predicate(program: &Program, symbol: &str) -> bool {
    program.inner.iter().any(|rule| rule.head.symbol == symbol)
}

/// Collects new adorned predicates from a rule based on the adorned head
fn collect_new_adorned_predicates<'a>(
    program: &'a Program,
    rule: &'a Rule,
    adorned_head: &'a AdornedAtom,
) -> Vec<AdornedAtom> {
    let mut new_adorned = Vec::new();
    let mut current_bound_vars = get_bound_vars_from_adorned(adorned_head);

    for (pos, body_atom) in rule.body.iter().enumerate() {
        if is_derived_predicate(program, &body_atom.symbol) {
            let bound_vars_at_pos = compute_bound_vars_at_position(program, rule, pos, &current_bound_vars);
            let adorned_body = AdornedAtom::from_atom_and_bound_vars(body_atom, &bound_vars_at_pos);
            
            // Update bound variables
            current_bound_vars.extend(get_bound_vars_from_adorned(&adorned_body));
            new_adorned.push(adorned_body);
        }
    }
    new_adorned
}

/// Gets all rules that define a given predicate
fn get_rules_for_predicate<'a>(program: &'a Program, symbol: &str) -> Vec<&'a Rule> {
    program.inner.iter()
        .filter(|rule| rule.head.symbol == symbol)
        .collect()
}
