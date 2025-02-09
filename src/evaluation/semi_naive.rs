use crate::engine::index_storage::IndexStorage;
use crate::engine::storage::RelationStorage;
use datalog_syntax::Program;

pub fn semi_naive_evaluation(
    relation_storage: &mut RelationStorage,
    nonrecursive_program: &Program,
    recursive_program: &Program,
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
        facts: Vec<AnonymousGroundAtom>,
    ) {
        facts.into_iter().for_each(|fact| {
            storage
                .inner
                .get_mut(relation_symbol)
                .unwrap()
                .insert(Arc::new(fact));
        });
    }

    #[test]
    fn test_one_hop() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("e".to_string(), Default::default());
        storage.inner.insert("hop".to_string(), Default::default());
        insert_into(
            &mut storage,
            "e",
            vec![vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]],
        );

        let one_hop = program! { hop(?x, ?z) <- [e(?x, ?y), e(?y, ?z)] };
        let (nonrecursive_delta_program, recursive_delta_program) = split_program(one_hop);

        let expected: HashSet<AnonymousGroundAtom> =
            vec![vec!["a".into(), "c".into()]].into_iter().collect();
        semi_naive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program,
        );
        let actual: HashSet<_> = storage
            .get_relation("hop")
            .into_iter()
            .map(|x| (**x).clone())
            .collect();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_linear_tc() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("e".to_string(), Default::default());
        storage.inner.insert("tc".to_string(), Default::default());

        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()],
            ],
        );

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };
        let (nonrecursive_delta_program, recursive_delta_program) = split_program(tc_program);

        let expected: HashSet<AnonymousGroundAtom> = vec![
            // First iter
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
        ]
        .into_iter()
        .collect();

        semi_naive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program,
        );

        let actual: HashSet<_> = storage
            .get_relation("tc")
            .into_iter()
            .map(|x| (**x).clone())
            .collect();

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_nonlinear_tc() {
        let mut storage: RelationStorage = Default::default();
        storage.inner.insert("e".to_string(), Default::default());
        storage.inner.insert("tc".to_string(), Default::default());

        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()],
            ],
        );

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
        };
        let (nonrecursive_delta_program, recursive_delta_program) = split_program(tc_program);

        let expected: HashSet<AnonymousGroundAtom> = vec![
            // First iter
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            // Second iter
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            // Third iter
            vec!["a".into(), "d".into()],
        ]
        .into_iter()
        .collect();
        semi_naive_evaluation(
            &mut storage,
            &nonrecursive_delta_program,
            &recursive_delta_program,
        );

        let actual: HashSet<_> = storage
            .get_relation("tc")
            .into_iter()
            .map(|x| (**x).clone())
            .collect();

        assert_eq!(expected, actual);
    }
}
