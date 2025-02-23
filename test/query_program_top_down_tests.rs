#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use micro_datalog::{convert_fact, engine::datalog::MicroRuntime};

    #[test]
    fn test_query_program_same_generation() {
        let program = program! {
            sg(?x, ?y) <- [flat(?x, ?y)],
            sg(?y, ?x) <- [sg(?x, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), down(?z1, ?y)],
            sg(?x, ?y) <- [up(?x, ?z1), sg(?z1, ?z2), down(?z2, ?y)]
        };

        let mut runtime = MicroRuntime::new(program.clone());

        // Set up tree structure:
        //       a1    a2   (flat connects these)
        //      /  \  /  \
        //    b1  b2 b3  b4
        runtime.insert("up", ("b1", "a1")); // b1 up to a1
        runtime.insert("up", ("b2", "a1")); // b2 up to a1
        runtime.insert("up", ("b3", "a2")); // b3 up to a2
        runtime.insert("up", ("b4", "a2")); // b4 up to a2

        // Direct same-generation relationships
        runtime.insert("flat", ("a1", "a2")); // a1 same gen as a2

        runtime.insert("down", ("a1", "b1")); // a1 down to b1
        runtime.insert("down", ("a1", "b2")); // a1 down to b2
        runtime.insert("down", ("a2", "b3")); // a2 down to b3
        runtime.insert("down", ("a2", "b4")); // a2 down to b4

        runtime.poll();

        // Query for nodes in same generation as b1 (should find b2, b3, b4)
        let query = build_query!(sg("b1", _));
        let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "Top-down"));

        // b1 should be in same generation as b2, b3, and b4
        let expected: HashSet<_> = vec![
            ("b1", "b2"), // Same parent a1
            ("b1", "b3"), // Through flat a1-a2
            ("b1", "b4"), // Through flat a1-a2
            ("b1", "b1"), // Every node is in same gen with itself
        ]
        .into_iter()
        .collect();

        assert_eq!(expected, results);
    }

    #[test]
    fn test_query_program_basic_ancestor() {
        // Set up a simple ancestor program
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        // Create runtime and add base facts
        let mut runtime = MicroRuntime::new(program.clone());
        runtime.insert("parent", vec!["john", "bob"]);
        runtime.insert("parent", vec!["bob", "mary"]);

        // Query for ancestors of john
        let query = build_query!(ancestor("john", _));
        let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "Top-down"));

        // Expected results - john is ancestor of both bob and mary
        let expected: HashSet<_> = vec![("john", "bob"), ("john", "mary")]
            .into_iter()
            .collect();

        assert_eq!(expected, results);
    }

    #[test]
    fn test_query_program_ff() {
        // Set up a simple ancestor program
        let program = program! {
            ancestor(?x, ?y) <- [parent(?x, ?y)],
            ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
        };

        // Create runtime and add base facts
        let mut runtime = MicroRuntime::new(program.clone());
        runtime.insert("parent", vec!["john", "bob"]);
        runtime.insert("parent", vec!["bob", "mary"]);

        // Query for ancestors of john
        let query = build_query!(ancestor(_, _));
        let results: HashSet<_> = convert_fact!(runtime.query_program(&query, program, "Top-down"));

        // Expected results - john is ancestor of both bob and mary
        let expected: HashSet<_> = vec![("john", "bob"), ("bob", "mary"), ("john", "mary")]
            .into_iter()
            .collect();

        assert_eq!(expected, results);
    }
}
