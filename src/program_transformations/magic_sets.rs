use crate::helpers::helpers::*;
use crate::program_transformations::adorned_atom::*;
use datalog_syntax::*;
use std::collections::{HashMap, HashSet};

pub fn apply_magic_transformation(program: &Program, query: &Query) -> Program {
    let mut transformed_rules = Vec::new();
    let mut processed_adorned_preds = HashSet::new();
    let mut seen_rules = HashSet::new();
    let mut to_process = Vec::new();

    // Pre-compute rules by predicate for faster lookups
    let rules_by_predicate: HashMap<String, Vec<&Rule>> = program.inner
        .iter()
        .fold(HashMap::new(), |mut acc: HashMap<String, Vec<&Rule>>, rule| {
            acc.entry(rule.head.symbol.clone())
                .or_insert_with(Vec::new)
                .push(rule);
            acc
        });

    // Initialize with query adornments
    if let Some(rules) = rules_by_predicate.get(query.symbol) {
        let adornments: Vec<_> = query.matchers
            .iter()
            .map(|matcher| match matcher {
                Matcher::Constant(_) => Adornment::Bound,
                Matcher::Any => Adornment::Free,
            })
            .collect();

        for rule in rules {
            let initial_adorned = AdornedAtom {
                atom: rule.head.clone(),
                adornment: adornments.clone(),
            };
            to_process.push(initial_adorned);
        }
    }

    // Process adorned predicates
    while let Some(adorned_pred) = to_process.pop() {
        if !processed_adorned_preds.insert(adorned_pred.clone()) {
            continue;
        }

        if let Some(rules) = rules_by_predicate.get(&adorned_pred.atom.symbol) {
            for rule in rules {
                // Collect and process new adorned predicates
                let new_adorned = collect_new_adorned_predicates(program, rule, &adorned_pred);
                to_process.extend(
                    new_adorned.into_iter()
                        .filter(|a| a.adornment.iter().any(|a| matches!(a, Adornment::Bound)))
                );

                // Create and deduplicate magic rules
                let magic_rules = create_magic_rules(program, rule, &adorned_pred);
                for magic_rule in magic_rules {
                    let rule_str = format!("{:?}", magic_rule);
                    if seen_rules.insert(rule_str) {
                        if !transformed_rules.iter().any(|r: &Rule| 
                            r.head.symbol == magic_rule.head.symbol && 
                            r.head.terms == magic_rule.head.terms
                        ) {
                            transformed_rules.push(magic_rule);
                        }
                    }
                }

                // Create and deduplicate modified rule
                let modified_rule = modify_original_rule(program, rule, &adorned_pred);
                let rule_str = format!("{:?}", modified_rule);
                if seen_rules.insert(rule_str) {
                    transformed_rules.push(modified_rule);
                }
            }
        }
    }

    Program::from(transformed_rules)
}

/// Creates a magic seed fact for a given query
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
    let seed_fact: Vec<_> = query
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
    let mut binding_chain = vec![make_magic_predicate(adorned_head)];
    let mut bound_variables = get_bound_vars_from_adorned(adorned_head);

    // Pre-compute derived predicates for faster lookups
    let derived_predicates: HashSet<_> = program
        .inner
        .iter()
        .map(|r| r.head.symbol.clone())
        .collect();

    for body_atom in &rule.body {
        let is_derived = derived_predicates.contains(&body_atom.symbol);
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

        if !is_derived {
            binding_chain.push(body_atom.clone());
            // Update bound variables for all terms in the atom
            for term in &body_atom.terms {
                if let Term::Variable(var) = term {
                    bound_variables.insert(var.clone());
                }
            }
            continue;
        }

        // Handle derived predicates
        let magic_head = make_magic_predicate(&AdornedAtom {
            atom: body_atom.clone(),
            adornment: adorned_head.adornment.clone(),
        });

        if !binding_chain
            .iter()
            .any(|atom| atom.symbol == magic_head.symbol && atom.terms == magic_head.terms)
        {
            magic_rules.push(Rule {
                head: magic_head,
                body: binding_chain.clone(),
                id: 0,
            });
        }

        binding_chain.push(modify_body_predicate(
            body_atom,
            &AdornedAtom {
                atom: body_atom.clone(),
                adornment: adorned_head.adornment.clone(),
            },
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

pub fn collect_new_adorned_predicates(
    program: &Program,
    rule: &Rule,
    adorned_head: &AdornedAtom,
) -> Vec<AdornedAtom> {
    let mut new_adorned = Vec::new();
    let mut current_bound_vars = get_bound_vars_from_adorned(adorned_head);

    // Pre-compute derived predicates for faster lookups
    let derived_predicates: HashSet<_> = program
        .inner
        .iter()
        .map(|r| r.head.symbol.clone())
        .collect();

    for (pos, body_atom) in rule.body.iter().enumerate() {
        if derived_predicates.contains(&body_atom.symbol) {
            let bound_vars_at_pos =
                compute_bound_vars_at_position(program, rule, pos, &current_bound_vars);

            let adorned_body = AdornedAtom::from_atom_and_bound_vars(body_atom, &bound_vars_at_pos);

            current_bound_vars.extend(get_bound_vars_from_adorned(&adorned_body));
            new_adorned.push(adorned_body);
        }
    }

    new_adorned
}

pub fn modify_original_rule(program: &Program, rule: &Rule, adorned_head: &AdornedAtom) -> Rule {
    // Pre-compute derived predicates for faster lookups
    let derived_predicates: HashSet<_> = program
        .inner
        .iter()
        .map(|r| r.head.symbol.clone())
        .collect();

    // Create magic predicate with bound variables
    let magic_terms: Vec<_> = rule
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
        terms: magic_terms,
        sign: true,
    };

    // Create new body with magic predicate and adorned body atoms
    let mut new_body = vec![magic_predicate];

    // Track bound variables from the head
    let mut bound_vars = HashSet::new();
    for (term, adornment) in rule.head.terms.iter().zip(adorned_head.adornment.iter()) {
        if let Term::Variable(var) = term {
            if matches!(adornment, Adornment::Bound) {
                bound_vars.insert(var.clone());
            }
        }
    }

    // Process each body atom
    for body_atom in &rule.body {
        if derived_predicates.contains(&body_atom.symbol) {
            // For derived predicates, create adorned version
            let adorned_body = AdornedAtom::from_atom_and_bound_vars(body_atom, &bound_vars);
            new_body.push(modify_body_predicate(body_atom, &adorned_body));
            
            // Update bound variables with variables from this atom
            for term in &body_atom.terms {
                if let Term::Variable(var) = term {
                    bound_vars.insert(var.clone());
                }
            }
        } else {
            // For base predicates, just clone
            new_body.push(body_atom.clone());
        }
    }

    // Create adorned head predicate
    let adorned_head_pred = create_adorned_head_predicate(&rule.head, adorned_head);

    Rule {
        head: adorned_head_pred,
        body: new_body,
        id: 0,
    }
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
