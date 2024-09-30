#[cfg(test)]
mod tests {
    use micro_datalog::evaluation::semi_positive::semi_positive_evaluation;
    use micro_datalog::engine::storage::RelationStorage;
    use datalog_rule_macro::semipositive_program;
    use datalog_syntax::*;
    use std::collections::HashSet;
    use micro_datalog::helpers::helpers::split_program;
    use common::program_transformations::delta_program::make_delta_program;

    fn insert_into(
        storage: &mut RelationStorage,
        relation_symbol: &str,
        facts: Vec<AnonymousGroundAtom>
    ) {
        facts.into_iter().for_each(|fact| {
            storage.inner.get_mut(relation_symbol).unwrap().insert(fact);
        });
    }

    #[test]
    fn test_one_hop() {
        let mut relation_storage: RelationStorage = Default::default();
        relation_storage.inner.insert("e".to_string(), Default::default());
        relation_storage.inner.insert("Δe".to_string(), Default::default());
        relation_storage.inner.insert("hop".to_string(), Default::default());
        relation_storage.inner.insert("Δhop".to_string(), Default::default());

        insert_into(
            &mut relation_storage,
            "e",
            vec![vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]]
        );
        insert_into(
            &mut relation_storage,
            "Δe",
            vec![vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]]
        );

        let one_hop = semipositive_program! { hop(?x, ?z) <- [e(?x, ?y), e(?y, ?z)] };
        let (nonrecursive_delta_program, recursive_delta_program) = split_program(
            make_delta_program(&one_hop, true)
        );
        let expected: HashSet<AnonymousGroundAtom> = vec![vec!["a".into(), "c".into()]]
            .into_iter()
            .collect();

        semi_positive_evaluation(
            &mut relation_storage,
            &nonrecursive_delta_program,
            &recursive_delta_program
        );
        let actual: HashSet<_> = relation_storage
            .get_relation("hop")
            .into_iter()
            .cloned()
            .collect();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_linear_tc() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("e".to_string(), Default::default());
        storage.inner.insert("Δe".to_string(), Default::default());
        storage.inner.insert("tc".to_string(), Default::default());
        storage.inner.insert("Δtc".to_string(), Default::default());

        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()]
            ]
        );
        insert_into(
            &mut storage,
            "Δe",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()]
            ]
        );

        let tc_program =
            semipositive_program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };
        let (nonrecursive_delta_program, recursive_delta_program) = split_program(
            make_delta_program(&tc_program, true)
        );

        let expected: HashSet<AnonymousGroundAtom> = vec![
            // First iter
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()]
        ]
            .into_iter()
            .collect();

        semi_positive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program
        );

        let actual: HashSet<_> = storage.get_relation("tc").into_iter().cloned().collect();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_nonlinear_tc() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("e".to_string(), Default::default());
        storage.inner.insert("Δe".to_string(), Default::default());
        storage.inner.insert("tc".to_string(), Default::default());
        storage.inner.insert("Δtc".to_string(), Default::default());

        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()]
            ]
        );
        insert_into(
            &mut storage,
            "Δe",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()]
            ]
        );

        let tc_program =
            semipositive_program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
        };
        let (nonrecursive_delta_program, recursive_delta_program) = split_program(
            make_delta_program(&tc_program, true)
        );

        let expected: HashSet<AnonymousGroundAtom> = vec![
            // First iter
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()]
        ]
            .into_iter()
            .collect();
        semi_positive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program
        );

        let actual: HashSet<_> = storage.get_relation("tc").into_iter().cloned().collect();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_empty_program() {
        let mut storage: RelationStorage = Default::default();

        let empty_program = semipositive_program! {};

        let (nonrecursive_delta_program, recursive_delta_program) = split_program(
            make_delta_program(&empty_program, true)
        );

        semi_positive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program
        );

        assert!(storage.inner.is_empty(), "Storage should remain empty for an empty program");
    }

    #[test]
    fn test_simple_non_recursive() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("a".to_string(), Default::default());
        storage.inner.insert("Δa".to_string(), Default::default());
        storage.inner.insert("b".to_string(), Default::default());
        storage.inner.insert("Δb".to_string(), Default::default());

        insert_into(&mut storage, "a", vec![vec!["x".into()]]);
        insert_into(&mut storage, "Δa", vec![vec!["x".into()]]);

        let non_recursive_program = semipositive_program! {
        b(?x) <- [a(?x)]
    };

        let (nonrecursive_delta_program, recursive_delta_program) = split_program(
            make_delta_program(&non_recursive_program, true)
        );

        let expected: HashSet<AnonymousGroundAtom> = vec![vec!["x".into()]].into_iter().collect();

        semi_positive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program
        );

        let actual: HashSet<_> = storage.get_relation("b").into_iter().cloned().collect();

        assert_eq!(expected, actual, "Non-recursive rule evaluation failed");
    }

    #[test]
    fn test_non_recursive_with_negation() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("a".to_string(), Default::default());
        storage.inner.insert("Δa".to_string(), Default::default());
        storage.inner.insert("b".to_string(), Default::default());
        storage.inner.insert("Δb".to_string(), Default::default());

        insert_into(&mut storage, "a", vec![vec!["x".into()]]);
        insert_into(&mut storage, "Δa", vec![vec!["x".into()]]);

        let non_recursive_negation_program = semipositive_program! {
        b(?x) <- [!a(?x)]
    };

        let (nonrecursive_delta_program, recursive_delta_program) = split_program(
            make_delta_program(&non_recursive_negation_program, true)
        );

        // Since "a(x)" exists, "b(x)" should not be derived
        let expected: HashSet<AnonymousGroundAtom> = HashSet::new();

        semi_positive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program
        );

        let actual: HashSet<_> = storage.get_relation("b").into_iter().cloned().collect();

        assert_eq!(expected, actual, "Non-recursive negation rule evaluation failed");
    }

    #[test]
    fn test_redundant_rule() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("p".to_string(), Default::default());
        storage.inner.insert("Δp".to_string(), Default::default());

        insert_into(&mut storage, "p", vec![vec!["a".into()]]);
        insert_into(&mut storage, "Δp", vec![vec!["a".into()]]);

        let redundant_rule_program =
            semipositive_program! {
        p(?x) <- [p(?x)] // Redundant rule: p(x) is already in storage
    };

        let (nonrecursive_delta_program, recursive_delta_program) = split_program(
            make_delta_program(&redundant_rule_program, true)
        );

        let expected: HashSet<AnonymousGroundAtom> = vec![vec!["a".into()]].into_iter().collect();

        semi_positive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program
        );

        let actual: HashSet<_> = storage.get_relation("p").into_iter().cloned().collect();

        assert_eq!(expected, actual, "Redundant rule should not add new facts");
    }

    /* scenario not implemented

    #[test]
    fn test_no_new_facts_derived() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("p".to_string(), Default::default());
        storage.inner.insert("Δp".to_string(), Default::default());
        storage.inner.insert("q".to_string(), Default::default());
        storage.inner.insert("Δq".to_string(), Default::default());

        insert_into(&mut storage, "p", vec![vec!["a".into()], vec!["b".into()]]);
        insert_into(&mut storage, "Δp", vec![vec!["a".into()], vec!["b".into()]]);

        let no_fact_derivation_program =
            semipositive_program! {
        q(?x) <- [p(?y), p(?z)] // No matching facts for this rule
    };

        let (nonrecursive_delta_program, recursive_delta_program) = split_program(
            make_delta_program(&no_fact_derivation_program, true)
        );

        semi_positive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program
        );

        let actual: HashSet<_> = storage.get_relation("q").into_iter().cloned().collect();
        assert!(actual.is_empty(), "No new facts should have been derived");
    }
        */
}
