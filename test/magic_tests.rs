#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use datalog_rule_macro::{program, rule};
    use datalog_syntax::*;
    use micro_datalog::program_transformations::{adorned_atom::AdornedAtom, magic_sets::*};

    // #[test]
    // fn test_magic_transformation_sg() {
    //     let program = program! {
    //         sg(?x, ?y) <- [flat(?x, ?y)],
    //         sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
    //         sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
    //     };

    //     let query = build_query!(sg("john", _));

    //     let expected_transformed_program = program! {
    //         magic_sg_bf(?z1) <- [magic_sg_bf(?x), up(?x, ?z1)],
    //     };

    //     let transformed_program = apply_magic_transformation(&program, &query);
    //     assert_eq!(expected_transformed_program, transformed_program);
    // }

    #[test]
    fn test_magic_transformation_tc_bbb() {
        let program = program! {
            tc(?x, ?y, ?z) <- [e(?x, ?y), e(?y, ?z), e(?z, ?w)],
            tc(?x, ?y, ?w) <- [tc(?x, ?y, ?z), tc(?y, ?z, ?w)],
        };

        let query = build_query!(tc("john", "john", "mark"));

        let expected_transformed_program = program! {

        tc_bbb(?x, ?y, ?z) <- [magic_tc_bbb(?x, ?y, ?z), e(?x, ?y), e(?y, ?z), e(?z, ?w)],
        tc_bbb(?x, ?y, ?w) <- [magic_tc_bbb(?x, ?y, ?w), tc_bbf(?x, ?y, ?z), tc_bfb(?y, ?z, ?w)],

        tc_bbf(?x, ?y, ?z) <- [magic_tc_bbf(?x, ?y), e(?x, ?y), e(?y, ?z), e(?z, ?w)],
        tc_bbf(?x, ?y, ?w) <- [magic_tc_bbf(?x, ?y), tc_bbf(?x, ?y, ?z), tc_bff(?y, ?z, ?w)],

        tc_bfb(?x, ?y, ?z) <- [magic_tc_bfb(?x, ?z), e(?x, ?y), e(?y, ?z), e(?z, ?w)],
        tc_bfb(?x, ?y, ?w) <- [magic_tc_bfb(?x, ?w), tc_bff(?x, ?y, ?z), tc_ffb(?y, ?z, ?w)],

        tc_bff(?x, ?y, ?z) <- [magic_tc_bff(?x), e(?x, ?y), e(?y, ?z), e(?z, ?w)],
        tc_bff(?x, ?y, ?w) <- [magic_tc_bff(?x), tc_bff(?x, ?y, ?z), tc_fff(?y, ?z, ?w)],

        tc_ffb(?x, ?y, ?z) <- [magic_tc_ffb(?z), e(?x, ?y), e(?y, ?z), e(?z, ?w)],
        tc_ffb(?x, ?y, ?w) <- [magic_tc_ffb(?w), tc_fff(?x, ?y, ?z), tc_ffb(?y, ?z, ?w)],

        tc_fff(?x, ?y, ?z) <- [e(?x, ?y), e(?y, ?z), e(?z, ?w)],
        tc_fff(?x, ?y, ?w) <- [tc_fff(?x, ?y, ?z), tc_fff(?y, ?z, ?w)],

        magic_tc_bbf(?x, ?y) <- [magic_tc_bbb(?x, ?y, ?w)],
        magic_tc_bfb(?y, ?w) <- [magic_tc_bbb(?x, ?y, ?w), tc_bbf(?x, ?y, ?z)],

        magic_tc_bff(?y) <- [magic_tc_bbf(?x, ?y), tc_bbf(?x, ?y, ?z)],

        magic_tc_bff(?x) <- [magic_tc_bfb(?x, ?w)],
        magic_tc_ffb(?w) <- [magic_tc_bfb(?x, ?w), tc_bff(?x, ?y, ?z)],

        magic_tc_ffb(?w)  <- [magic_tc_ffb(?w), tc_fff(?x, ?y, ?z)],
        };

        let (transformed_program, _) = apply_magic_transformation(&program, &query);
        println!("transformed_program===");
        for rule in &transformed_program.inner {
            println!("transformed_rule==={:?}", rule);
        }
        assert_eq!(expected_transformed_program, transformed_program);
    }

    #[test]
    fn test_magic_transformation_ancestor_bf() {
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
        let (transformed_program, _) = apply_magic_transformation(&program, &query);
        assert_eq!(expected_transformed_program, transformed_program);
    }

    #[test]
    fn test_magic_transformation_ancestor_bb() {
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        let query = build_query!(ancestor("john", "mary"));

        // The expected magic-transformed program
        let expected_transformed_program = program! {
            ancestor_bb(?x, ?y) <- [magic_ancestor_bb(?x, ?y), parent(?x, ?y)],
            ancestor_bb(?x, ?z) <- [magic_ancestor_bb(?x, ?z), parent(?x, ?y), ancestor_bb(?y, ?z)],
            magic_ancestor_bb(?y, ?z) <- [magic_ancestor_bb(?x, ?z), parent(?x, ?y)]
        };

        // Apply the magic transformation to the program
        let (transformed_program, _) = apply_magic_transformation(&program, &query);
        assert_eq!(expected_transformed_program, transformed_program);
    }

    #[test]
    fn test_magic_transformation_ancestor_fb() {
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        let query = build_query!(ancestor(_, "john"));

        // The expected magic-transformed program
        let expected_transformed_program = program! {
            ancestor_fb(?x, ?y) <- [magic_ancestor_fb(?y), parent(?x, ?y)],
            ancestor_fb(?x, ?z) <- [magic_ancestor_fb(?z), parent(?x, ?y), ancestor_bb(?y, ?z)],


            ancestor_bb(?x, ?y) <- [magic_ancestor_bb(?x, ?y), parent(?x, ?y)],
            ancestor_bb(?x, ?z) <- [magic_ancestor_bb(?x, ?z), parent(?x, ?y), ancestor_bb(?y, ?z)],

             // Magic rules
            magic_ancestor_bb(?y, ?z) <- [magic_ancestor_fb(?z), parent(?x, ?y)],
            magic_ancestor_bb(?y, ?z) <- [magic_ancestor_bb(?x, ?z), parent(?x, ?y)],
        };

        // Apply the magic transformation to the program
        let (transformed_program, _) = apply_magic_transformation(&program, &query);
        assert_eq!(expected_transformed_program, transformed_program);
    }

    #[test]
    fn test_magic_transformation_rdf_abridged_bff() {
        // add seed magic_T_fbf("0")
        // add seed magic_T_fbf("3")
        let program = program! {
            T(?s, ?p, ?o) <- [RDF(?s, ?p, ?o)],
            T(?y, 0usize, ?x) <- [T(?a, 3usize, ?x), RDF(?y, ?a, ?z)],
        };
        let query = build_query!(T("a", _, _));

        let expected = program! {
            T_bff(?s, ?p, ?o) <- [magic_T_bff(?s), RDF(?s, ?p, ?o)],
            T_bbf(?y, 0usize, ?x) <- [magic_T_bff(?y), T_fbf(?a, 3usize, ?x), RDF(?y, ?a, ?z)],
            T_fbf(?s, ?p, ?o) <- [magic_T_fbf(?p), RDF(?s, ?p, ?o)],
            T_fbf(?y, 0usize, ?x) <- [T_fbf(?a, 3usize, ?x), RDF(?y, ?a, ?z)]
        };

        let (transformed, _) = apply_magic_transformation(&program, &query);
        println!("transformed===");
        for rule in &transformed.inner {
            println!("{:?}", rule);
        }
        assert_eq!(expected, transformed);
    }

    #[test]
    fn test_magic_transformation_rdf_abridged_fbf() {
         // add seed magic_T_fbf("3")
        let program = program! {
            T(?s, ?p, ?o) <- [RDF(?s, ?p, ?o)],
            T(?y, 0usize, ?x) <- [T(?a, 3usize, ?x), RDF(?y, ?a, ?z)],
        };
        let query = build_query!(T(_, 0usize, _));

        let expected = program! {
            T_fbf(?s, ?p, ?o) <- [magic_T_fbf(?p), RDF(?s, ?p, ?o)],
            T_fbf(?y, 0usize, ?x) <- [T_fbf(?a, 3usize, ?x), RDF(?y, ?a, ?z)],
        };

        let (transformed, _) = apply_magic_transformation(&program, &query);
        println!("transformed===");
        for rule in &transformed.inner {
            println!("{:?}", rule);
        }
        assert_eq!(expected, transformed);
    }

    #[test]
    fn test_magic_transformation_ancestor_ff() {
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        let query = build_query!(ancestor(_, _));

        let expected = program! {
            ancestor_ff(?x, ?y) <- [parent(?x, ?y)],
            ancestor_ff(?x, ?z) <- [parent(?x, ?y), ancestor_bf(?y, ?z)],
            ancestor_bf(?x, ?y) <- [magic_ancestor_bf(?x), parent(?x, ?y)],
            ancestor_bf(?x, ?z) <- [magic_ancestor_bf(?x), parent(?x, ?y), ancestor_bf(?y, ?z)],
            magic_ancestor_bf(?y) <- [magic_ancestor_bf(?x), parent(?x, ?y)],
            magic_ancestor_bf(?y) <- [parent(?x, ?y)],
        };

        let (transformed, _) = apply_magic_transformation(&program, &query);
        assert_eq!(expected, transformed);
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

        let (transformed, _) = apply_magic_transformation(&program, &query);
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

        let (transformed, _) = apply_magic_transformation(&program, &query);
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

        let (transformed, _) = apply_magic_transformation(&program, &query);
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
        let (magic_program, _) = apply_magic_transformation(&program, &query);

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
