use datalog_syntax::*;
use std::collections::HashSet;
use crate::program_transformations::adorned_atom::*;
use crate::helpers::helpers::*;

/// Main entry point for magic sets transformation.
/// Takes a Datalog program and a query, returns the transformed program with magic predicates.
pub fn apply_magic_transformation(program: &Program, query: &Query) -> Program {
    println!("\n=== Starting Magic Transformation ===");
    println!("Initial Program: {:?}", program);
    println!("Query symbol: {}", query.symbol);
    println!("Query matchers count: {}", query.matchers.len());

    let mut transformed_rules = Vec::new();
    let mut processed_adorned_preds = HashSet::new();
    let mut seen_rules = HashSet::new(); // Use single HashSet for all rules
    let mut to_process = Vec::new();

    let query_bound_vars = get_bound_vars_from_query(query);
    println!("Query bound vars: {:?}", query_bound_vars);

    if let Some(initial_rule) = get_rules_for_predicate(program, query.symbol).first() {
        println!("Initial rule: {:?}", initial_rule);

        let mut adornments = vec![Adornment::Free; query.matchers.len()];
        for (i, matcher) in query.matchers.iter().enumerate() {
            if let Matcher::Constant(_) = matcher {
                adornments[i] = Adornment::Bound;
            }
        }
        println!("Created adornments: {:?}", adornments);

        let initial_adorned = AdornedAtom {
            atom: initial_rule.head.clone(),
            adornment: adornments,
        };
        println!("Initial adorned atom: {:?}", initial_adorned);
        to_process.push(initial_adorned);
    }

    while let Some(adorned_pred) = to_process.pop() {
        println!("\n--- Processing adorned predicate: {:?}", adorned_pred);

        if processed_adorned_preds.contains(&adorned_pred) {
            println!("Already processed, skipping");
            continue;
        }
        processed_adorned_preds.insert(adorned_pred.clone());
        println!("Added to processed predicates");

        for rule in get_rules_for_predicate(program, &adorned_pred.atom.symbol) {
            println!("\nProcessing rule: {:?}", rule);

            // Add any new adorned predicates to process
            for new_adorned in collect_new_adorned_predicates(
                rule,
                &adorned_pred,
                &query_bound_vars
            ) {
                println!("Got new adorned predicate: {:?}", new_adorned);
                let has_bound_var = new_adorned.adornment
                    .iter()
                    .any(|a| matches!(a, Adornment::Bound));

                if has_bound_var {
                    println!("Adding to processing queue - predicate has bound variables");
                    to_process.push(new_adorned);
                } else {
                    println!("Skipping predicate with no bound variables: {:?}", new_adorned);
                }
            }

            // Create and deduplicate magic rules
            let magic_rules = create_magic_rules(rule, &adorned_pred);
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
                    existing_rule.head.symbol == magic_rule.head.symbol &&
                        existing_rule.head.terms == magic_rule.head.terms
                });

                if has_rule_with_same_head {
                    println!("Skipping magic rule with duplicate head: {:?}", magic_rule);
                    continue;
                }

                println!("Adding new magic rule: {:?}", magic_rule);
                seen_rules.insert(rule_str);
                transformed_rules.push(magic_rule);
            }

            // Create and deduplicate modified rule
            let modified_rule = modify_original_rule(rule, &adorned_pred);
            let rule_str = format!("{:?}", modified_rule);
            if !seen_rules.contains(&rule_str) {
                println!("Adding new modified rule: {:?}", modified_rule);
                seen_rules.insert(rule_str);
                transformed_rules.push(modified_rule);
            }
        }
    }

    Program::from(transformed_rules)
}

fn create_magic_rules(rule: &Rule, adorned_head: &AdornedAtom) -> Vec<Rule> {
    println!("\n=== Creating magic rules ===");
    println!("Rule: {:?}", rule);
    println!("Adorned head: {:?}", adorned_head);

    let mut magic_rules = Vec::new();

    // Track all predicates seen so far that contribute to binding propagation
    let mut binding_chain = vec![make_magic_predicate(adorned_head)];

    // Track variables that can potentially propagate bindings
    let mut bound_variables = get_bound_vars_from_adorned(adorned_head);
    println!("Initial bound variables: {:?}", bound_variables);

    // First pass: Process each predicate in sequence, building up binding chains
    for (pos, body_atom) in rule.body.iter().enumerate() {
        println!("Processing predicate at position {}: {:?}", pos, body_atom);
        println!("Current binding chain: {:?}", binding_chain);

        // If this is a base predicate that uses any bound variables,
        // add it to our binding chain because it contributes to binding propagation
        if !is_derived_predicate(rule, &body_atom.symbol) {
            let uses_bound_vars = body_atom.terms.iter().any(|term| {
                if let Term::Variable(var) = term { bound_variables.contains(var) } else { false }
            });

            if uses_bound_vars {
                binding_chain.push(body_atom.clone());
                println!("Added to binding chain, it is now {:?}", binding_chain);

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

        // For derived predicates, we need to:
        // 1. Create a magic rule using the current binding chain if appropriate
        // 2. Add this predicate to the chain for future magic rules
        println!("Found derived predicate, current binding chain: {:?}", binding_chain);

        // Only create a magic rule if this predicate uses bound variables
        let uses_bound_vars = body_atom.terms.iter().any(|term| {
            if let Term::Variable(var) = term { bound_variables.contains(var) } else { false }
        });

        if uses_bound_vars {
            let magic_head = make_magic_predicate(
                &(AdornedAtom {
                    atom: body_atom.clone(),
                    adornment: adorned_head.adornment.clone(),
                })
            );

            // Skip if this would create a recursive magic rule
            if
                !binding_chain
                    .iter()
                    .any(|atom| atom.symbol == magic_head.symbol && atom.terms == magic_head.terms)
            {
                let magic_rule = Rule {
                    head: magic_head,
                    body: binding_chain.clone(),
                    id: 0,
                };
                println!("Created magic rule: {:?}", magic_rule);
                magic_rules.push(magic_rule);
            } else {
                println!("Skipping recursive magic rule");
            }

            // Add the adorned version of this predicate to the binding chain
            binding_chain.push(
                modify_body_predicate(
                    body_atom,
                    &(AdornedAtom {
                        atom: body_atom.clone(),
                        adornment: adorned_head.adornment.clone(),
                    })
                )
            );

            // Update bound variables to include outputs from this predicate
            for term in &body_atom.terms {
                if let Term::Variable(var) = term {
                    bound_variables.insert(var.clone());
                }
            }
        }
    }

    println!("Final magic rules: {:?}", magic_rules);
    magic_rules
}

pub fn collect_new_adorned_predicates(
    rule: &Rule,
    adorned_head: &AdornedAtom,
    query_bound_vars: &HashSet<String>
) -> Vec<AdornedAtom> {
    println!("\n=== Collecting new adorned predicates ===");
    println!("Rule: {:?}", rule);
    println!("Adorned head: {:?}", adorned_head);
    println!("Query bound vars: {:?}", query_bound_vars);

    let mut new_adorned = Vec::new();
    let mut current_bound_vars = get_bound_vars_from_adorned(adorned_head);
    println!("Initial bound vars: {:?}", current_bound_vars);

    for (pos, body_atom) in rule.body.iter().enumerate() {
        println!("\nProcessing body atom at pos {}: {:?}", pos, body_atom);

        if is_derived_predicate(rule, &body_atom.symbol) {
            let bound_vars_at_pos = compute_bound_vars_at_position(rule, pos, &current_bound_vars);
            println!("Bound vars at pos {}: {:?}", pos, bound_vars_at_pos);

            let adorned_body = AdornedAtom::from_atom_and_bound_vars(body_atom, &bound_vars_at_pos);
            println!("Created adorned body: {:?}", adorned_body);

            // Update bound variables
            current_bound_vars.extend(get_bound_vars_from_adorned(&adorned_body));
            println!("Updated bound vars: {:?}", current_bound_vars);

            // Push the adorned body after using it to update bound vars
            new_adorned.push(adorned_body);
        }
    }

    println!("Returning adorned predicates: {:?}", new_adorned);
    new_adorned
}

fn modify_original_rule(rule: &Rule, adorned_head: &AdornedAtom) -> Rule {
    println!("\n=== Modifying rule ===");
    println!("Original rule: {:?}", rule);
    println!("Adorned head: {:?}", adorned_head);

    let mut new_body = Vec::new();

    // Add magic predicate for the bound arguments of the head
    println!("\nCreating magic predicate for head:");
    let magic_terms: Vec<Term> = rule.head.terms
        .iter()
        .zip(adorned_head.adornment.iter())
        .filter_map(|(term, adornment)| {
            println!("  Checking term {:?} with adornment {:?}", term, adornment);
            match adornment {
                Adornment::Bound => {
                    println!("    Including term (bound)");
                    Some(term.clone())
                }
                Adornment::Free => {
                    println!("    Skipping term (free)");
                    None
                }
            }
        })
        .collect();

    let magic_predicate = Atom {
        symbol: make_magic_predicate_name(adorned_head),
        terms: magic_terms.clone(),
        sign: true,
    };
    println!("Created magic predicate: {:?}", magic_predicate);
    new_body.push(magic_predicate);

    // Process each body predicate
    println!("\nProcessing body predicates:");
    for (pos, body_atom) in rule.body.iter().enumerate() {
        println!("\nBody predicate at position {}: {:?}", pos, body_atom);

        if is_derived_predicate(rule, &body_atom.symbol) {
            println!("This is a derived predicate ({})", body_atom.symbol);
            // For derived predicates, we always use bf pattern for consistency
            let adornment = vec![Adornment::Bound, Adornment::Free];
            println!("Using consistent bf adornment pattern: {:?}", adornment);

            let adorned_body = AdornedAtom {
                atom: body_atom.clone(),
                adornment: adornment,
            };
            println!("Created adorned body: {:?}", adorned_body);

            let modified_predicate = modify_body_predicate(body_atom, &adorned_body);
            println!("Modified predicate: {:?}", modified_predicate);
            new_body.push(modified_predicate);
        } else {
            println!("This is a base predicate - keeping unchanged");
            new_body.push(body_atom.clone());
        }
    }

    let modified_head = create_adorned_head_predicate(&rule.head, adorned_head);
    println!("\nCreated modified head: {:?}", modified_head);

    let modified_rule = Rule {
        head: modified_head,
        body: new_body,
        id: 0,
    };
    println!("\nFinal modified rule: {:?}", modified_rule);

    modified_rule
}

pub fn make_magic_predicate(adorned_atom: &AdornedAtom) -> Atom {
    let bound_terms: Vec<Term> = adorned_atom.atom.terms
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

#[cfg(test)]
mod tests {
    use super::*;
    use datalog_rule_macro::{ program, rule };

    #[test]
    fn test_modify_original_rule() {
        let rule = rule! { p(?x, ?y) <- [q(?x, ?z), p(?z, ?y)] };

        // Create adorned version where first argument is bound
        let mut bound_vars = HashSet::new();
        bound_vars.insert("x".to_string());

        let adorned_head = AdornedAtom::from_atom_and_bound_vars(&rule.head, &bound_vars);

        // Modify the rule
        let modified = modify_original_rule(&rule, &adorned_head);

        // Expected:
        // pbf(X,Y) :- magic_pbf(X), q(X,Z), pbf(Z,Y)
        assert!(modified.body[0].symbol.starts_with("magic_"));
        assert_eq!(modified.head.symbol, "p_bf");
        assert_eq!(modified.body.len(), 3); // magic pred + original 2 body atoms
    }

    #[test]
    fn test_modify_original_rule_with_multiple_bound() {
        let rule = rule! { p(?x, ?y, ?z) <- [q(?x, ?y), r(?y, ?z)] };

        let mut bound_vars = HashSet::new();
        bound_vars.insert("x".to_string());
        bound_vars.insert("y".to_string());

        let adorned_head = AdornedAtom::from_atom_and_bound_vars(&rule.head, &bound_vars);

        let modified = modify_original_rule(&rule, &adorned_head);

        // Expected:
        // pbbf(X,Y,Z) :- magic_pbbf(X,Y), q(X,Y), r(Y,Z)
        assert!(modified.body[0].symbol.starts_with("magic_"));
        assert_eq!(modified.head.symbol, "p_bbf");
        assert_eq!(modified.body.len(), 3);
    }

    #[test]
    fn test_ancestor_magic_transform() {
        // Original program: Linear ancestor computation
        // - First rule: Direct ancestor through parent relationship
        // - Second rule: Transitive ancestor through recursive step
        let program =
            program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        // Query: Find all ancestors of "john" (first arg bound, second free)
        // This creates binding pattern ancestor_bf (b=bound, f=free)
        let query = build_query!(ancestor("john", _));

        // Expected transformed program after magic sets transformation:
        let expected =
            program! {
            // Magic rule to compute relevant bindings:
            // - For each person X who we need ancestors for (magic_ancestor_bf(X))
            // - If X is a parent of Y, then we also need ancestors of Y
            // This follows the recursive structure of the original program
            magic_ancestor_bf(?y) <- [magic_ancestor_bf(?x), parent(?x, ?y)],

            // Modified original rules:
            // 1. Base rule: Only compute ancestor relationships for relevant X
            // where X is marked as relevant by magic_ancestor_bf
            ancestor_bf(?x, ?y) <- [magic_ancestor_bf(?x), parent(?x, ?y)],

            // 2. Recursive rule: Similarly restricted to relevant X values
            // The ancestor_bf in the body uses the same binding pattern
            // since we're passing bound values down the recursion
            ancestor_bf(?x, ?z) <- [magic_ancestor_bf(?x), parent(?x, ?y), ancestor_bf(?y, ?z)]
        };

        let transformed = apply_magic_transformation(&program, &query);
        assert_eq!(transformed, expected);
    }

    #[test]
    fn test_same_generation_magic_transform() {
        // Original program: Find pairs of nodes that are in the same generation in a tree
        // Consider a tree structure like:
        //       john
        //      /    \
        //     a1    a2     <- a1 and a2 are in the same generation
        //    /  \  /  \
        //   b1  b2 b3 b4   <- b1, b2, b3, b4 are in the same generation
        //
        // The program has two ways to find same-generation pairs:
        // 1. Direct/flat relationship: We already know two nodes are in same generation
        //    e.g., flat(a1, a2) or flat(b1, b2) are stored facts
        // 2. Recursive relationship: Find nodes in same generation by going up and down the tree
        //    e.g., to find that b1 and b4 are in same generation:
        //    - go up from b1 to a1 using up(b1, a1)
        //    - use sg to establish a1 and a2 are in same generation
        //    - go down from a2 to b4 using down(a2, b4)
        let program =
            program! {
        // Base case: Nodes we directly know are in the same generation
        sg(?x, ?y) <- [flat(?x, ?y)],
        
        // Recursive case: Nodes are in same generation if:
        // - we can go up from x to z1
        // - z1 is in same generation as z2
        // - we can go down from z2 to y
        sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
    };

        // Query: Find all nodes in the same generation as "john"
        // Creates binding pattern sg_bf (first argument bound, second free)
        let query = build_query!(sg("john", _));

        // Expected transformed program:
        let expected =
            program! {
        // Magic rules to compute relevant bindings:
        // 1. If we need sg for node X, and we can go up from X to Z1,
        //    we need to find same-generation pairs for Z1
        magic_sg_bf(?z1) <- [magic_sg_bf(?x), up(?x, ?z1)],

        // Modified original rules with magic predicates:
        // 1. Base case: Check flat relationships only for relevant X
        //    (nodes we're actually interested in)
        sg_bf(?x, ?y) <- [magic_sg_bf(?x), flat(?x, ?y)],
        
        // 2. Recursive case: Only explore up/down paths for relevant X
        sg_bf(?x, ?y) <- [magic_sg_bf(?x), up(?x, ?z1), sg_bf(?z1, ?z2), down(?z2, ?y)]
    };

        let transformed = apply_magic_transformation(&program, &query);
        assert_eq!(transformed, expected);
    }

    #[test]
    fn test_nonlinear_same_generation_magic_transform() {
        // Original program: Nonlinear same-generation finding nodes in same generation
        // Consider a tree structure where we can use both direct (flat) and recursive paths:
        //       john
        //      /    \
        //     a1    a2      Direct flat path: flat(a1,a2)
        //    /  \  /  \
        //   b1  b2 b3  b4   Complex path to find b1,b4 in same generation:
        //                    - up from b1 to a1
        //                    - flat from a1 to a2
        //                    - down from a2 to b4
        let program =
            program! {
        // Base case: Direct flat relationship between nodes
        sg(?x, ?y) <- [flat(?x, ?y)],
        
        // Recursive case with two sg calls and flat relationship:
        // This allows finding same-generation pairs through:
        // 1. Going up from X to Z1
        // 2. Finding Z1,Z2 in same generation (first recursive sg)
        // 3. Using flat relationship Z2->Z3  
        // 4. Finding Z3,Z4 in same generation (second recursive sg)
        // 5. Going down from Z4 to Y
        sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), flat(?z2, ?z3), 
                       sg(?z3, ?z4), down(?z4, ?y)]
    };

        // Query: Find all nodes in same generation as "john"
        // Creates binding pattern sg_bf (first argument bound, second free)
        let query = build_query!(sg("john", _));

        // Expected transformed program after magic sets transformation:
        let expected =
            program! {
        // Magic rules to compute relevant bindings:
        // 1. If we need sg for node X, and we can go up from X to Z1,
        //    we need to find same-generation pairs for Z1
        magic_sg_bf(?z1) <- [magic_sg_bf(?x), up(?x, ?z1)],
        
        // 2. If we've computed sg(Z1,Z2) and have a flat path Z2->Z3,
        //    we need to find same-generation pairs for Z3
        magic_sg_bf(?z3) <- [magic_sg_bf(?x), up(?x, ?z1), 
                            sg_bf(?z1, ?z2), flat(?z2, ?z3)],

        // Modified original rules:
        // 1. Base case: Only compute flat relationships for relevant X
        sg_bf(?x, ?y) <- [magic_sg_bf(?x), flat(?x, ?y)],
        
        // 2. Recursive case: Only explore paths for relevant X
        // Both sg_bf calls use same binding pattern since bindings flow through
        // the flat relationship
        sg_bf(?x, ?y) <- [magic_sg_bf(?x), up(?x, ?z1), sg_bf(?z1, ?z2),
                          flat(?z2, ?z3), sg_bf(?z3, ?z4), down(?z4, ?y)]
    };

        let transformed = apply_magic_transformation(&program, &query);
        assert_eq!(transformed, expected);
    }

    #[test]
    fn test_path_magic_transform_with_constants() {
        // Original program: Path finding with special target handling
        // - First rule: Direct edge paths
        // - Second rule: Multi-edge paths
        // - Third rule: Special handling for paths to "target"
        let program =
            program! {
            path(?x, ?y) <- [edge(?x, ?y)],
            path(?x, ?y) <- [edge(?x, ?z), path(?z, ?y)],
            path(?x, "target") <- [special_edge(?x)]  // Rule with constant in head
        };

        // Query: Find all paths starting from "john"
        let query = build_query!(path("john", _));

        let expected =
            program! {
            // Magic rule: For each relevant source X, 
            // add intermediate nodes Z as relevant sources
            magic_path_bf(?z) <- [magic_path_bf(?x), edge(?x, ?z)],

            // Modified original rules:
            // 1. Direct edges from relevant sources
            path_bf(?x, ?y) <- [magic_path_bf(?x), edge(?x, ?y)],
            // 2. Multi-edge paths from relevant sources
            path_bf(?x, ?y) <- [magic_path_bf(?x), edge(?x, ?z), path_bf(?z, ?y)],
            // 3. Special target paths from relevant sources
            // Note: Constant "target" remains in the transformed rule
            path_bf(?x, "target") <- [magic_path_bf(?x), special_edge(?x)]
        };

        let transformed = apply_magic_transformation(&program, &query);
        assert_eq!(transformed, expected);
    }
}
