# Micro Datalog

Micro Datalog is a minimal incremental datalog reasoner. It is primarily meant to be correct and easy to use.

It compiles datalog rules into a sequence of relational algebra operations that are run with an efficient four-instruction
__select-project-join__ relational algebra interpreter.

The following snippets showcase the engine in action:
```rust
#[cfg(test)]
mod tests {
   use crate::engine::datalog::MicroRuntime;
   use datalog_rule_macro::program;
   use datalog_syntax::*;
   use std::collections::HashSet;

   #[test]
   fn integration_test_deletions() {
      let all = build_query!(tc(_, _));
      let all_from_a = build_query!(tc("a", _));

      let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
        };

      let mut runtime = MicroRuntime::new(tc_program);
      vec![
         vec!["a".into(), "b".into()],
         // this extra fact (a, e) will help to test that rederivation works, since it has multiple valid ways of
         // being derived.
         vec!["a".into(), "e".into()],
         vec!["b".into(), "c".into()],
         vec!["c".into(), "d".into()],
         vec!["d".into(), "e".into()],
      ]
          .into_iter()
          .for_each(|edge| {
              runtime.insert("e", edge);
          });

      runtime.poll();

      let actual_all: HashSet<&AnonymousGroundAtom> = runtime.query(&all).unwrap().collect();
      let expected_all: HashSet<AnonymousGroundAtom> = vec![
         vec!["a".into(), "b".into()],
         vec!["a".into(), "e".into()],
         vec!["b".into(), "c".into()],
         vec!["c".into(), "d".into()],
         // Second iter
         vec!["a".into(), "c".into()],
         vec!["b".into(), "d".into()],
         // Third iter
         vec!["a".into(), "d".into()],
         // Fourth iter
         vec!["d".into(), "e".into()],
         vec!["c".into(), "e".into()],
         vec!["b".into(), "e".into()],
      ]
          .into_iter()
          .collect();
      assert_eq!(expected_all, actual_all.into_iter().cloned().collect());

      let actual_all_from_a = runtime.query(&all_from_a).unwrap();
      let expected_all_from_a: HashSet<AnonymousGroundAtom> = vec![
         vec!["a".into(), "b".into()],
         vec!["a".into(), "c".into()],
         vec!["a".into(), "d".into()],
         vec!["a".into(), "e".into()],
      ]
          .into_iter()
          .collect();
      assert_eq!(
         expected_all_from_a,
         actual_all_from_a.into_iter().cloned().collect()
      );

      // Update
      // Point removals are a bit annoying, since they incur creating a query.
      let d_to_e = build_query!(e("d", "e"));
      runtime.remove(&d_to_e);
      assert!(!runtime.safe());
      runtime.poll();
      assert!(runtime.safe());

      let actual_all_after_update: HashSet<&AnonymousGroundAtom> =
          runtime.query(&all).unwrap().collect();
      let expected_all_after_update: HashSet<AnonymousGroundAtom> = vec![
         vec!["a".into(), "b".into()],
         vec!["b".into(), "c".into()],
         vec!["c".into(), "d".into()],
         // Second iter
         vec!["a".into(), "c".into()],
         vec!["b".into(), "d".into()],
         // Third iter
         vec!["a".into(), "d".into()],
         // This remains
         vec!["a".into(), "e".into()],
      ]
          .into_iter()
          .collect();
      assert_eq!(
         expected_all_after_update,
         actual_all_after_update.into_iter().cloned().collect()
      );

      let actual_all_from_a_after_update = runtime.query(&all_from_a).unwrap();
      let expected_all_from_a_after_update: HashSet<AnonymousGroundAtom> = vec![
         vec!["a".into(), "b".into()],
         vec!["a".into(), "c".into()],
         vec!["a".into(), "d".into()],
         vec!["a".into(), "e".into()],
      ]
          .into_iter()
          .collect();
      assert_eq!(expected_all_from_a_after_update, actual_all_from_a_after_update.into_iter().cloned().collect());
   }
}
```

In case you are interested in performance, there is a very simple benchmark under `./src/bin.rs`. It compares `MicroDatalog`
with [ascent](https://github.com/s-arash/ascent) and [crepe](https://github.com/ekzhang/crepe)

`MicroDatalog` is ~10-20% faster than `crepe`.

To run it, clone the project, extract `./data/lubm1.nt.gz`, and then:
```shell
cargo run --release
```