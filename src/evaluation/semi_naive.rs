use crate::engine::index_storage::IndexStorage;
use crate::engine::storage::RelationStorage;
use datalog_syntax::Program;

pub fn semi_naive_evaluation(
    relation_storage: &mut RelationStorage,
    nonrecursive_program: &Program,
    recursive_program: &Program
) {
    let mut index_storage =
        IndexStorage::from((nonrecursive_program, recursive_program, &*relation_storage));

    relation_storage
        .materialize_nonrecursive_delta_program(nonrecursive_program, &mut index_storage);

    loop {
        let previous_facts_count = relation_storage.len();
        relation_storage.materialize_recursive_delta_program(recursive_program, &mut index_storage);
        let current_facts_count = relation_storage.len();

        let new_fact_count = current_facts_count - previous_facts_count;

        if new_fact_count == 0 {
            return;
        }
    }
}

#[cfg(test)]
mod test {
    use crate::engine::storage::RelationStorage;
    use crate::evaluation::semi_naive::semi_naive_evaluation;
    use crate::helpers::helpers::split_program;
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use std::collections::HashSet;
    use std::sync::Arc;

    fn insert_into(
        storage: &mut RelationStorage,
        relation_symbol: &str,
        facts: Vec<AnonymousGroundAtom>
    ) {
        facts.into_iter().for_each(|fact| {
            storage.inner.get_mut(relation_symbol).unwrap().insert(Arc::new(fact));
        });
    }

    fn register_relations(storage: &mut RelationStorage, names: &[&str]) {
        for name in names {
            storage.inner.insert(name.to_string(), Default::default());
        }
    }

    fn collect_relation(storage: &RelationStorage, name: &str) -> HashSet<AnonymousGroundAtom> {
        storage
            .get_relation(name)
            .into_iter()
            .map(|x| (**x).clone())
            .collect()
    }

    // ========================================================================
    // Existing positive tests (unchanged)
    // ========================================================================

    #[test]
    fn test_one_hop() {
        let mut storage: RelationStorage = Default::default();
        register_relations(&mut storage, &["e", "hop"]);
        insert_into(
            &mut storage,
            "e",
            vec![vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]]
        );

        let one_hop = program! { hop(?x, ?z) <- [e(?x, ?y), e(?y, ?z)] };
        let (nonrecursive_delta_program, recursive_delta_program) = split_program(one_hop);

        let expected: HashSet<AnonymousGroundAtom> = vec![vec!["a".into(), "c".into()]]
            .into_iter()
            .collect();
        semi_naive_evaluation(&mut storage, &nonrecursive_delta_program, &recursive_delta_program);

        assert_eq!(expected, collect_relation(&storage, "hop"));
    }

    #[test]
    fn test_linear_tc() {
        let mut storage: RelationStorage = Default::default();
        register_relations(&mut storage, &["e", "tc"]);
        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()]
            ]
        );

        let tc_program =
            program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };
        let (nonrecursive_delta_program, recursive_delta_program) = split_program(tc_program);

        let expected: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            vec!["a".into(), "d".into()]
        ]
            .into_iter()
            .collect();
        semi_naive_evaluation(&mut storage, &nonrecursive_delta_program, &recursive_delta_program);

        assert_eq!(expected, collect_relation(&storage, "tc"));
    }

    #[test]
    fn test_nonlinear_tc() {
        let mut storage: RelationStorage = Default::default();
        register_relations(&mut storage, &["e", "tc"]);
        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()]
            ]
        );

        let tc_program =
            program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
        };
        let (nonrecursive_delta_program, recursive_delta_program) = split_program(tc_program);

        let expected: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            vec!["a".into(), "d".into()]
        ]
            .into_iter()
            .collect();
        semi_naive_evaluation(&mut storage, &nonrecursive_delta_program, &recursive_delta_program);

        assert_eq!(expected, collect_relation(&storage, "tc"));
    }

    // ========================================================================
    // Cross product tests
    // ========================================================================

    #[test]
    fn test_cross_product() {
        // pair(X, Y) <- p(X), q(Y)  — no shared variables, cross product
        let mut storage: RelationStorage = Default::default();
        register_relations(&mut storage, &["p", "q", "pair"]);
        insert_into(&mut storage, "p", vec![
            vec!["a".into()], vec!["b".into()],
        ]);
        insert_into(&mut storage, "q", vec![
            vec!["1".into()], vec!["2".into()], vec!["3".into()],
        ]);

        let prog = program! {
            pair(?x, ?y) <- [p(?x), q(?y)]
        };
        let (nonrecursive, recursive) = split_program(prog);
        semi_naive_evaluation(&mut storage, &nonrecursive, &recursive);

        let result = collect_relation(&storage, "pair");
        // Should be full cross product: 2 × 3 = 6 pairs
        let expected: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "1".into()],
            vec!["a".into(), "2".into()],
            vec!["a".into(), "3".into()],
            vec!["b".into(), "1".into()],
            vec!["b".into(), "2".into()],
            vec!["b".into(), "3".into()],
        ].into_iter().collect();
        assert_eq!(expected, result);
    }

}
