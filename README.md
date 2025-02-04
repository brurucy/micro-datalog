# Micro Datalog

Micro Datalog is a minimal **incremental** semi-positive datalog reasoner. It is primarily meant to be correct and easy to use.

It compiles datalog rules into a sequence of relational algebra operations that are run incrementally with a four-instruction
__select-project-join__ relational algebra interpreter.

In essence, it is a hand-compiled pseudo [DBSP](https://github.com/brurucy/pydbsp) circuit.

The following snippets showcase the engine in action:
```rust
#[cfg(test)]
mod tests {
   use crate::engine::datalog::MicroRuntime;
   use datalog_rule_macro::program;
   use datalog_syntax::*;
   use std::collections::HashSet;

   #[test]
    fn integration_test_insertions_only() {
        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };

        let mut runtime = MicroRuntime::new(tc_program);
        vec![("a", "b"), ("b", "c"), ("c", "d")]
            .into_iter()
            .for_each(|xy| {
                runtime.insert("e", xy);
            });

        runtime.poll();

        // This query reads as: "Get all in tc with any values in any positions"
        let all = build_query!(tc(_, _));
        // And this one as: "Get all in tc with the first term being a"
        // There also is a QueryBuilder, if you do not want to use a macro.
        let all_from_a = build_query!(tc("a", _));

        let actual_all: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all));
        let expected_all: HashSet<(&str, &str)> = vec![
            ("a", "b"),
            ("b", "c"),
            ("c", "d"),
            // Second iter
            ("a", "c"),
            ("b", "d"),
            // Third iter
            ("a", "d"),
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all, actual_all);

        let actual_all_from_a: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all_from_a));
        let expected_all_from_a: HashSet<(&str, &str)> = vec![("a", "b"), ("a", "c"), ("a", "d")]
            .into_iter()
            .collect();
        assert_eq!(expected_all_from_a, actual_all_from_a);

        expected_all.iter().for_each(|fact| {
            assert!(runtime.contains("tc", *fact).unwrap());
        });

        expected_all_from_a.iter().for_each(|fact| {
            assert!(runtime.contains("tc", *fact).unwrap());
        });

        // Update
        runtime.insert("e", ("d", "e"));
        assert!(!runtime.safe());
        runtime.poll();
        assert!(runtime.safe());

        let actual_all_after_update: HashSet<(&str, &str)> = convert_fact!(runtime.query(&all));
        let expected_all_after_update: HashSet<(&str, &str)> = vec![
            ("a", "b"),
            ("b", "c"),
            ("c", "d"),
            // Second iter
            ("a", "c"),
            ("b", "d"),
            // Third iter
            ("a", "d"),
            // Update
            ("d", "e"),
            ("c", "e"),
            ("b", "e"),
            ("a", "e"),
        ]
        .into_iter()
        .collect();
        assert_eq!(expected_all_after_update, actual_all_after_update);

        let actual_all_from_a_after_update: HashSet<(&str, &str)> =
            convert_fact!(runtime.query(&all_from_a));
        let expected_all_from_a_after_update: HashSet<(&str, &str)> =
            vec![("a", "b"), ("a", "c"), ("a", "d"), ("a", "e")]
                .into_iter()
                .collect();
        assert_eq!(
            expected_all_from_a_after_update,
            actual_all_from_a_after_update
        );
    }
}
```