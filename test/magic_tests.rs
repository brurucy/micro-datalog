#[test]
fn test_magic_transformation_ancestor() {
    let program =
        program! {
        ancestor(?x, ?y) <- [parent(?x, ?y)],
        ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)]
    };

    // The expected magic-transformed program
    let expected_transformed_program =
        program! {
        // Magic rules
        // b - bound, f - free
        magic_ancestor_bf(?y) <- [magic_ancestor_bf(?x), parent(?x, ?y)],
        
        // Modified original rules
        ancestor_bf(?x, ?y) <- [magic_ancestor_bf(?x), parent(?x, ?y)],
        ancestor_bf(?x, ?z) <- [magic_ancestor_bf(?x), parent(?x, ?y), ancestor_bf(?y, ?z)]
    };

    // Apply the magic transformation to the program
    let transformed_program = apply_magic_transformation(&program);
    assert_eq!(expected_transformed_program, transformed_program);
}

#[test]
fn test_magic_transformation_tc() {
    let program =
        program! {
        tc(?x, ?y) <- [edge(?x, ?y)],
        tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
    };

    // The expected magic-transformed program
    let expected_transformed_program =
        program! {
        // Magic rules
        magic_tc_bf(?y) <- [magic_tc_bf(?x), edge(?x, ?y)],
        magic_tc_bf(?y) <- [magic_tc_bf(?x), tc_bf(?x, ?y)],
        magic_tc_bf(?z) <- [magic_tc_bf(?x), tc_bf(?x, ?y), tc_bf(?y, ?z)],
        
        // Modified original rules
        tc_bf(?x, ?y) <- [magic_tc_bf(?x), edge(?x, ?y)],
        tc_bf(?x, ?z) <- [magic_tc_bf(?x), tc_bf(?x, ?y), tc_bf(?y, ?z)]
    };

    // Apply the magic transformation to the program
    let transformed_program = apply_magic_transformation(&program);
    assert_eq!(expected_transformed_program, transformed_program);
}

#[test]
fn test_top_down_evaluation_ancestor() {
    let program =
        program! {
        ancestor(?x, ?y) <- [parent(?x, ?y)],
        ancestor(?x, ?z) <- [parent(?x, ?y), ancestor(?y, ?z)],
    };

    let mut runtime = TopDownRuntime::new(program);

    vec![
        vec!["john".into(), "mary".into()],
        vec!["mary".into(), "alice".into()],
        vec!["alice".into(), "bob".into()]
    ]
        .into_iter()
        .for_each(|edge| {
            runtime.insert("parent", edge);
        });

    // Query for ancestor("john", ?z)
    let query = build_query!(ancestor("john", _));
    let expected_results: HashSet<AnonymousGroundAtom> = vec![
        vec!["john".into(), "mary".into()],
        vec!["john".into(), "alice".into()],
        vec!["john".into(), "bob".into()]
    ]
        .into_iter()
        .collect();

    let actual_results: HashSet<_> = runtime.query(&query).unwrap().collect();

    assert_eq!(expected_results, actual_results);
}
#[test]
fn test_top_down_evaluation_tc() {
    let program =
        program! {
        tc(?x, ?y) <- [edge(?x, ?y)],
        tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
    };

    // Create a runtime with the program
    let mut runtime = TopDownRuntime::new(program);

    vec![vec!["a".into(), "b".into()], vec!["b".into(), "c".into()], vec!["c".into(), "d".into()]]
        .into_iter()
        .for_each(|edge| {
            runtime.insert("edge", edge);
        });

    // Query for tc("a", ?z)
    let query = build_query!(tc("a", _));
    let expected_results: HashSet<AnonymousGroundAtom> = vec![
        vec!["a".into(), "b".into()],
        vec!["a".into(), "c".into()],
        vec!["a".into(), "d".into()]
    ]
        .into_iter()
        .collect();

    let actual_results: HashSet<_> = runtime.query(&query).unwrap().collect();

    assert_eq!(expected_results, actual_results);
}
