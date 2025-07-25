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
pub fn apply_magic_transformation(program: &Program, query: &Query) -> (Program, HashSet<Atom>) {
    let mut transformed_rules = Vec::with_capacity(program.inner.len() * 2); // = magic rules + modified rules
    let mut processed_adorned_preds = HashSet::new();
    let mut seen_rules = HashSet::new();
    let mut to_process = Vec::new();
    let mut magic_seeds = HashSet::new();

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
            let (modified_rule, magic_seeds_from_rules) =
                modify_original_rule(program, rule, &adorned_pred);
            magic_seeds.extend(magic_seeds_from_rules);

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
            let (magic_rules, magic_seeds_from_magic_rules) =
                create_magic_rules(program, &modified_rule, &adorned_pred);
            magic_seeds.extend(magic_seeds_from_magic_rules);

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

    // let program_test = program! {
    //     T_bbb(?s, ?p, ?o) <- [magic_T_bbb(?s, ?p, ?o), RDF(?s, ?p, ?o)],
    //     T_bbf(?s, ?p, ?o) <- [magic_T_bbf(?s, ?p), RDF(?s, ?p, ?o)],
    //     T_bfb(?s, ?p, ?o) <- [magic_T_bfb(?s, ?o), RDF(?s, ?p, ?o)],
    //     T_bff(?s, ?p, ?o) <- [magic_T_bff(?s), RDF(?s, ?p, ?o)],
    //     T_fbb(?s, ?p, ?o) <- [magic_T_fbb(?p, ?o), RDF(?s, ?p, ?o)],
    //     T_fbf(?s, ?p, ?o) <- [magic_T_fbf(?p), RDF(?s, ?p, ?o)],
    //     T_ffb(?s, ?p, ?o) <- [magic_T_ffb(?o), RDF(?s, ?p, ?o)],
    //     T_fff(?s, ?p, ?o) <- [RDF(?s, ?p, ?o)],
    //     //magic_T_bff(?x) <- [magic_T_bff(?x), T_fbf(?a, 2, ?b)],
    //     magic_T_bff(?x) <- [magic_T_bbf(?x, ?b), T_fbb(?a, 2, ?b)],
    //     T_bbb(?x, ?b, ?y) <- [magic_T_bbb(?x, ?b, ?y), T_fbb(?a, 2, ?b), T_bfb(?x, ?a, ?y)],
    //     T_bbf(?x, ?b, ?y) <- [magic_T_bbf(?x, ?b), T_fbb(?a, 2, ?b), T_bff(?x, ?a, ?y)],
    //     T_bfb(?x, ?b, ?y) <- [magic_T_bfb(?x, ?y), T_bfb(?x, ?a, ?y), T_fbf(?a, 2, ?b)],
    //     T_bff(?x, ?b, ?y) <- [magic_T_bff(?x), T_bff(?x, ?a, ?y), T_fbf(?a, 2, ?b)],
    //     T_fbb(?x, ?b, ?y) <- [magic_T_fbb(?b, ?y), T_fbb(?a, 2, ?b), T_ffb(?x, ?a, ?y)],
    //     T_fbf(?x, ?b, ?y) <- [magic_T_fbf(?b), T_fbb(?a, 2, ?b), T_fff(?x, ?a, ?y)],
    //     T_ffb(?x, ?b, ?y) <- [magic_T_ffb(?y), T_ffb(?x, ?a, ?y), T_fbf(?a, 2, ?b)],
    //     T_fff(?x, ?b, ?y) <- [T_fbf(?a, 2, ?b), T_fff(?x, ?a, ?y)],
    //     magic_T_bfb(?x, ?y) <- [magic_T_bbb(?x, ?b, ?y), T_fbb(?a, 2, ?b)],
    //     //magic_T_bfb(?x, ?y) <- [magic_T_bfb(?x, ?y), T_fbf(?a, 2, ?b)],
    //     magic_T_bbf(?x, 1) <- [magic_T_bff(?x)],
    //     magic_T_bbf(?x, 1) <- [magic_T_bfb(?x, ?z)],
    //     magic_T_bbf(?x, 1) <- [magic_T_bbb(?x, 1, ?z)],
    //     T_bbb(?x, 1, ?z) <- [magic_T_bfb(?x, ?z), T_bbf(?x, 1, ?y), T_fbb(?y, 1, ?z)],
    //     T_bbb(?x, 1, ?z) <- [magic_T_bbb(?x, 1, ?z), T_bbf(?x, 1, ?y), T_fbb(?y, 1, ?z)],
    //     T_bbf(?x, 1, ?z) <- [magic_T_bff(?x), T_bbf(?x, 1, ?y), T_fbf(?y, 1, ?z)],
    //     T_bbf(?x, 1, ?z) <- [magic_T_bbf(?x, 1), T_bbf(?x, 1, ?y), T_fbf(?y, 1, ?z)],
    //     T_fbb(?x, 1, ?z) <- [magic_T_ffb(?z), T_fbb(?y, 1, ?z),T_fbf(?x, 1, ?y)],
    //     T_fbb(?x, 1, ?z) <- [magic_T_fbb(1, ?z), T_fbb(?y, 1, ?z), T_fbf(?x, 1, ?y)],
    //     T_fbf(?x, 1, ?z) <- [T_fbf(?x, 1, ?y), T_fbf(?y, 1, ?z)],
    //     magic_T_bbf(?x, 2) <- [magic_T_bff(?x)],
    //     magic_T_bbf(?x, 2) <- [magic_T_bfb(?x, ?z)],
    //     magic_T_bbf(?x, 2) <- [magic_T_bbb(?x, 2, ?z)],
    //     T_bbb(?x, 2, ?z) <- [magic_T_bfb(?x, ?z), T_bbf(?x, 2, ?y), T_fbb(?y, 2, ?z)],
    //     T_bbb(?x, 2, ?z) <- [magic_T_bbb(?x, 2, ?z), T_bbf(?x, 2, ?y), T_fbb(?y, 2, ?z)],
    //     T_bbf(?x, 2, ?z) <- [magic_T_bff(?x), T_bbf(?x, 2, ?y), T_fbf(?y, 2, ?z)],
    //     T_bbf(?x, 2, ?z) <- [magic_T_bbf(?x, 2), T_bbf(?x, 2, ?y), T_fbf(?y, 2, ?z)],
    //     T_fbb(?x, 2, ?z) <- [magic_T_ffb(?z), T_fbb(?y, 2, ?z), T_fbf(?x, 2, ?y)], //
    //     T_fbb(?x, 2, ?z) <- [magic_T_fbb(2, ?z), T_fbb(?y, 2, ?z),T_fbf(?x, 2, ?y)], //
    //     T_fbf(?x, 2, ?z) <- [T_fbf(?x, 2, ?y), T_fbf(?y, 2, ?z)],
    //     //magic_T_bff(?y) <- [magic_T_bff(?y), T_fbf(?a, 3, ?x)],
    //     magic_T_bff(?y) <- [magic_T_bfb(?y, ?x), T_fbb(?a, 3, ?x)],
    //     //magic_T_bff(?y) <- [magic_T_bbf(?y, 0), T_fbf(?a, 3, ?x)],
    //     magic_T_bff(?y) <- [magic_T_bbb(?y, 0, ?x), T_fbb(?a, 3, ?x)],
    //     magic_T_ffb(?y) <- [magic_T_fbb(?b, ?y), T_fbb(?a, 2, ?b)],
    //     //magic_T_ffb(?y) <- [magic_T_ffb(?y), T_fbf(?a, 2, ?b)],
    //     T_bbb(?y, 0, ?x) <- [magic_T_bfb(?y, ?x), T_fbb(?a, 3, ?x), T_bff(?y, ?a, ?z)],
    //     T_bbb(?y, 0, ?x) <- [magic_T_bbb(?y, 0, ?x), T_fbb(?a, 3, ?x), T_bff(?y, ?a, ?z)],
    //     T_bbf(?y, 0, ?x) <- [magic_T_bff(?y), T_bff(?y, ?a, ?z), T_fbf(?a, 3, ?x)], //
    //     //T_bbf(?y, 0, ?x) <- [magic_T_bbf(?y, 0), T_fbf(?a, 3, ?x), T_bff(?y, ?a, ?z)],
    //     T_bbf(?y, 0, ?x) <- [magic_T_bbf(?y, 0), T_bff(?y, ?a, ?z),T_fbf(?a, 3, ?x)],
    //     T_fbb(?y, 0, ?x) <- [magic_T_ffb(?x), T_fbb(?a, 3, ?x), T_fff(?y, ?a, ?z)],
    //     T_fbb(?y, 0, ?x) <- [magic_T_fbb(0, ?x), T_fbb(?a, 3, ?x), T_fff(?y, ?a, ?z)],
    //     T_fbf(?y, 0, ?x) <- [T_fbf(?a, 3, ?x), T_fff(?y, ?a, ?z)],
    //     //magic_T_ffb(?z) <- [magic_T_bff(?z), T_fbf(?a, 4, ?x)],
    //     magic_T_ffb(?z) <- [magic_T_bfb(?z, ?x), T_fbb(?a, 4, ?x)],
    //     //magic_T_ffb(?z) <- [magic_T_bbf(?z, 0), T_fbf(?a, 4, ?x)],
    //     magic_T_ffb(?z) <- [magic_T_bbb(?z, 0, ?x), T_fbb(?a, 4, ?x)],
    //     //magic_T_bbf(?z, 0) <- [magic_T_bff(?z), T_fbf(?x, 1, ?y)],
    //     magic_T_bbf(?z, 0) <- [magic_T_bfb(?z, ?y), T_fbb(?x, 1, ?y)],
    //     //magic_T_bbf(?z, 0) <- [magic_T_bbf(?z, 0), T_fbf(?x, 1, ?y)],
    //     magic_T_bbf(?z, 0) <- [magic_T_bbb(?z, 0, ?y), T_fbb(?x, 1, ?y)],
    //     T_bbb(?z, 0, ?x) <- [magic_T_bfb(?z, ?x), T_fbb(?a, 4, ?x), T_ffb(?y, ?a, ?z)],
    //     T_bbb(?z, 0, ?x) <- [magic_T_bbb(?z, 0, ?x), T_fbb(?a, 4, ?x), T_ffb(?y, ?a, ?z)],
    //     //T_bbf(?z, 0, ?x) <- [magic_T_bff(?z), T_fbf(?a, 4, ?x), T_ffb(?y, ?a, ?z)],
    //     T_bbf(?z, 0, ?x) <- [magic_T_bff(?z), T_ffb(?y, ?a, ?z), T_fbf(?a, 4, ?x)],
    //     //T_bbf(?z, 0, ?x) <- [magic_T_bbf(?z, 0), T_fbf(?a, 4, ?x), T_ffb(?y, ?a, ?z)],
    //     T_bbf(?z, 0, ?x) <- [magic_T_bbf(?z, 0), T_ffb(?y, ?a, ?z),T_fbf(?a, 4, ?x)],
    //     T_fbb(?z, 0, ?x) <- [magic_T_ffb(?x), T_fbb(?a, 4, ?x), T_fff(?y, ?a, ?z)],
    //     T_fbb(?z, 0, ?x) <- [magic_T_fbb(0, ?x), T_fbb(?a, 4, ?x), T_fff(?y, ?a, ?z)],
    //     T_fbf(?z, 0, ?x) <- [T_fbf(?a, 4, ?x), T_fff(?y, ?a, ?z)],
    //     T_bbb(?z, 0, ?y) <- [magic_T_bfb(?z, ?y), T_fbb(?x, 1, ?y), T_bbf(?z, 0, ?x)],
    //     T_bbb(?z, 0, ?y) <- [magic_T_bbb(?z, 0, ?y), T_fbb(?x, 1, ?y), T_bbf(?z, 0, ?x)],
    //     //T_bbf(?z, 0, ?y) <- [magic_T_bff(?z), T_bbf(?z, 0, ?x),T_fbf(?x, 1, ?y)],
    //     T_bbf(?z, 0, ?y) <- [magic_T_bff(?z), T_bbf(?z, 0, ?x),T_fbf(?x, 1, ?y)],
    //     //T_bbf(?z, 0, ?y) <- [magic_T_bbf(?z, 0), T_fbf(?x, 1, ?y), T_bbf(?z, 0, ?x)],
    //     T_bbf(?z, 0, ?y) <- [magic_T_bbf(?z, 0),  T_bbf(?z, 0, ?x), T_fbf(?x, 1, ?y)],
    //     T_fbb(?z, 0, ?y) <- [magic_T_ffb(?y), T_fbb(?x, 1, ?y), T_fbf(?z, 0, ?x)],
    //     T_fbb(?z, 0, ?y) <- [magic_T_fbb(0, ?y), T_fbb(?x, 1, ?y), T_fbf(?z, 0, ?x)],
    //     T_fbf(?z, 0, ?y) <- [T_fbf(?x, 1, ?y), T_fbf(?z, 0, ?x)],
    //     magic_T_fbb(1, ?y) <- [magic_T_ffb(?y)],
    //     magic_T_fbb(1, ?y) <- [magic_T_bfb(?z, ?y)],
    //     magic_T_fbb(1, ?y) <- [magic_T_bbb(?z, 0, ?y)],
    //     magic_T_fbb(1, ?y) <- [magic_T_fbb(0, ?y)],
    //     magic_T_fbb(1, ?z) <- [magic_T_bfb(?x, ?z), T_bbf(?x, 1, ?y)],
    //     magic_T_fbb(1, ?z) <- [magic_T_bbb(?x, 1, ?z), T_bbf(?x, 1, ?y)],
    //     //magic_T_fbb(1, ?z) <- [magic_T_ffb(?z), T_fbf(?x, 1, ?y)],
    //     //magic_T_fbb(1, ?z) <- [magic_T_fbb(1, ?z), T_fbf(?x, 1, ?y)],
    //     magic_T_fbb(2, ?b) <- [magic_T_fbf(?b)],
    //     magic_T_fbb(2, ?b) <- [magic_T_fbb(?b, ?y)],
    //     magic_T_fbb(2, ?b) <- [magic_T_bbf(?x, ?b)],
    //     magic_T_fbb(2, ?b) <- [magic_T_bbb(?x, ?b, ?y)],
    //     magic_T_fbb(2, ?z) <- [magic_T_bfb(?x, ?z), T_bbf(?x, 2, ?y)],
    //     magic_T_fbb(2, ?z) <- [magic_T_bbb(?x, 2, ?z), T_bbf(?x, 2, ?y)],
    //     //magic_T_fbb(2, ?z) <- [magic_T_ffb(?z), T_fbf(?x, 2, ?y)],
    //     //magic_T_fbb(2, ?z) <- [magic_T_fbb(2, ?z), T_fbf(?x, 2, ?y)],
    //     magic_T_fbb(3, ?x) <- [magic_T_ffb(?x)],
    //     magic_T_fbb(3, ?x) <- [magic_T_bfb(?y, ?x)],
    //     magic_T_fbb(3, ?x) <- [magic_T_bbb(?y, 0, ?x)],
    //     magic_T_fbb(3, ?x) <- [magic_T_fbb(0, ?x)],
    //     magic_T_fbb(4, ?x) <- [magic_T_ffb(?x)],
    //     magic_T_fbb(4, ?x) <- [magic_T_bfb(?z, ?x)],
    //     magic_T_fbb(4, ?x) <- [magic_T_bbb(?z, 0, ?x)],
    //     magic_T_fbb(4, ?x) <- [magic_T_fbb(0, ?x)],
    // };
    //println!("Transformed rules: {:?}", transformed_rules);
    (Program::from(transformed_rules), magic_seeds)
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
) -> (Vec<Rule>, HashSet<Atom>) {
    let mut magic_rules = Vec::new();
    let mut binding_chain = Vec::new();
    let mut bound_variables = get_bound_vars_from_adorned_atom(adorned_head_atom);
    let mut magic_seeds = HashSet::new();

    for (i, body_atom) in modified_rule.body.iter().enumerate() {
        if is_magic_predicate(&body_atom.symbol) {
            binding_chain.push(body_atom.clone());
            continue;
        }

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
                let has_magic_atoms_besides_itself_in_binding_chain =
                    !binding_chain.iter().any(|atom| {
                        atom.symbol == magic_head.symbol && atom.terms == magic_head.terms
                    }) || binding_chain.len() > 1;

                let has_variables_in_head_terms = magic_head.terms.iter().any(|term| {
                    if let Term::Variable(_) = term {
                        true
                    } else {
                        false
                    }
                });

                if !has_variables_in_head_terms {
                    magic_seeds.insert(magic_head);
                }
                // i > 0 because we don't want to create a magic rule with only a magic atom in the body
                else if i > 0 && has_magic_atoms_besides_itself_in_binding_chain {
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

    (magic_rules, magic_seeds)
}

/// Modifies an original rule by adding magic predicates and updating adornments
pub fn modify_original_rule(
    program: &Program,
    rule: &Rule,
    adorned_head_atom: &AdornedAtom,
) -> (Rule, HashSet<Atom>) {
    let mut magic_seeds = HashSet::new();
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
    let has_variables = bound_terms.iter().any(|term| {
        if let Term::Variable(_) = term {
            true
        } else {
            false
        }
    });

    if !bound_terms.is_empty() {
        let magic_predicate = Atom {
            symbol: make_magic_predicate_name(adorned_head_atom),
            terms: bound_terms.clone(),
            sign: true,
        };
        if has_variables {
            new_body.push(magic_predicate);
        } else {
            magic_seeds.insert(magic_predicate);
        }
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

    let modified_rule = Rule {
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
    };

    (modified_rule, magic_seeds)
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

    for (_current_pos, body_atom) in rule.body.iter().enumerate() {
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
