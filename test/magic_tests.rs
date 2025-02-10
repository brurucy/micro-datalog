#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use datalog_rule_macro::{program, rule};
    use datalog_syntax::*;
    use micro_datalog::program_transformations::{adorned_atom::AdornedAtom, magic_sets::*};

    #[test]
    fn test_magic_transformation_ancestor() {
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        let query = build_query!(ancestor("john", _));

        // The expected magic-transformed program
        let expected_transformed_program = program! {
            // Magic rules
            // b - bound, f - free
            magic_ancestor_bf(?y) <- [magic_ancestor_bf(?x), parent(?x, ?y)],

            // Modified original rules
            ancestor_bf(?x, ?y) <- [magic_ancestor_bf(?x), parent(?x, ?y)],
            ancestor_bf(?x, ?z) <- [magic_ancestor_bf(?x), parent(?x, ?y), ancestor_bf(?y, ?z)]
        };

        // Apply the magic transformation to the program
        let transformed_program = apply_magic_transformation(&program, &query);
        assert_eq!(expected_transformed_program, transformed_program);
    }

    #[test]
    fn test_modify_original_rule() {
        let rule = rule! { p(?x, ?y) <- [q(?x, ?z), p(?z, ?y)] };
        let program = program! {p(?x, ?y) <- [q(?x, ?z), p(?z, ?y)]};

        // Create adorned version where first argument is bound
        let mut bound_vars = HashSet::new();
        bound_vars.insert("x".to_string());

        let adorned_head = AdornedAtom::from_atom_and_bound_vars(&rule.head, &bound_vars);
        let modified = modify_original_rule(&program, &rule, &adorned_head);

        assert!(modified.body[0].symbol.starts_with("magic_"));
        assert_eq!(modified.head.symbol, "p_bf");
        assert_eq!(modified.body.len(), 3);
    }

    #[test]
    fn test_modify_original_rule_with_multiple_bound() {
        let rule = rule! { p(?x, ?y, ?z) <- [q(?x, ?y), r(?y, ?z)] };
        let program = program! {p(?x, ?y, ?z) <- [q(?x, ?y), r(?y, ?z)]};

        let mut bound_vars = HashSet::new();
        bound_vars.insert("x".to_string());
        bound_vars.insert("y".to_string());

        let adorned_head = AdornedAtom::from_atom_and_bound_vars(&rule.head, &bound_vars);

        let modified = modify_original_rule(&program, &rule, &adorned_head);

        // Expected:
        // pbbf(X,Y,Z) :- magic_pbbf(X,Y), q(X,Y), r(Y,Z)
        assert!(modified.body[0].symbol.starts_with("magic_"));
        assert_eq!(modified.head.symbol, "p_bbf");
        assert_eq!(modified.body.len(), 3);
    }

    #[test]
    fn test_tc_magic_transform() {
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        let query = build_query!(ancestor(_, _));

        let expected = program! {
            ancestor_ff(?x, ?y) <- [magic_ancestor_ff(), parent(?x, ?y)],
            ancestor_ff(?x, ?z) <- [magic_ancestor_ff(), parent(?x, ?y), ancestor_ff(?y, ?z)]
        };

        let transformed = apply_magic_transformation(&program, &query);
        assert_eq!(transformed, expected);
    }

    #[test]
    fn test_ancestor_magic_transform() {
        // Original program: Linear ancestor computation
        // - First rule: Direct ancestor through parent relationship
        // - Second rule: Transitive ancestor through recursive step
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        // Query: Find all ancestors of "john" (first arg bound, second free)
        // This creates binding pattern ancestor_bf (b=bound, f=free)
        let query = build_query!(ancestor("john", _));

        // Expected transformed program after magic sets transformation:
        let expected = program! {
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
        let program = program! {
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
        let expected = program! {
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
        let program = program! {
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
        let expected = program! {
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
        let program = program! {
            path(?x, ?y) <- [edge(?x, ?y)],
            path(?x, ?y) <- [edge(?x, ?z), path(?z, ?y)],
            path(?x, "target") <- [special_edge(?x)]  // Rule with constant in head
        };

        // Query: Find all paths starting from "john"
        let query = build_query!(path("john", _));

        let expected = program! {
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

    #[test]
    fn test_create_magic_seed_fact() {
        // Test case 1: Single constant
        let query = build_query!(ancestor("john", _));
        let (pred, fact) = create_magic_seed_fact(&query);
        assert_eq!(pred, "magic_ancestor_bf");
        assert_eq!(fact, vec![TypedValue::from("john")]);

        // Test case 2: Multiple constants
        let query = build_query!(path("a", "b"));
        let (pred, fact) = create_magic_seed_fact(&query);
        assert_eq!(pred, "magic_path_bb");
        assert_eq!(fact, vec![TypedValue::from("a"), TypedValue::from("b")]);

        // Test case 3: Mixed constants and variables
        let query = build_query!(edge(3, _));
        let (pred, fact) = create_magic_seed_fact(&query);
        assert_eq!(pred, "magic_edge_bf");
        assert_eq!(fact, vec![TypedValue::from(3)]);

        // Test case 4: All variables (should give empty seed fact)
        let query = build_query!(parent(_, _));
        let (pred, fact) = create_magic_seed_fact(&query);
        assert_eq!(pred, "magic_parent_ff");
        assert!(fact.is_empty());

        // Test case 5: Different types of constants
        let query = build_query!(triple(true, 42, "test"));
        let (pred, fact) = create_magic_seed_fact(&query);
        assert_eq!(pred, "magic_triple_bbb");
        assert_eq!(
            fact,
            vec![
                TypedValue::from(true),
                TypedValue::from(42),
                TypedValue::from("test")
            ]
        );
    }

    // This test verifies how create_magic_seed_fact integrates with the query system
    #[test]
    fn test_magic_seed_integration() {
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        let query = build_query!(ancestor("john", _));
        let magic_program = apply_magic_transformation(&program, &query);

        let (magic_pred, seed_fact) = create_magic_seed_fact(&query);

        // Verify the seed fact matches what the magic program expects
        assert!(magic_program
            .inner
            .iter()
            .any(|rule| rule.body.iter().any(|atom| atom.symbol == magic_pred)));

        // The seed fact should contain "john" which will be used for binding
        assert_eq!(seed_fact, vec![TypedValue::from("john")]);
    }
}
