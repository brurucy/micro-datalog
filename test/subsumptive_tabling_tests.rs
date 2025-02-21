use std::collections::HashSet;

use datalog_rule_macro::program;
use datalog_syntax::*;
use micro_datalog::convert_fact;
use micro_datalog::engine::datalog::MicroRuntime;
use micro_datalog::engine::subsumptive_evaluator::*;

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

    let mut evaluator = SubsumptiveEvaluator::new(
        &mut runtime.processed,
        &mut runtime.unprocessed_insertions,
        program.clone(),
    );

    let query = build_query!(ancestor("john", _));
    let results = convert_fact!(evaluator.evaluate_query(&query, program));

    let expected: HashSet<_> = vec![("john", "bob"), ("john", "mary")]
        .into_iter()
        .collect();

    assert_eq!(expected, results);
}
