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

# Benchmark Commands

## Basic Usage
```bash
# Run all benchmarks
cargo run --release -- --micro-streaming --micro-magic --micro-tabling --crepe --ascent

# Run only micro magic and tabling
cargo run --release -- --micro-magic --micro-tabling

# Run with custom edge count and batch size
cargo run --release -- --edges 10000 --batch-size 500 --micro-magic --micro-tabling

# Run benchmarks without visualization
cargo run --release -- --micro-magic --micro-tabling --skip-visualization
```

## Advanced Usage
```bash
# Run with all available data
cargo run --release -- --use-all-data --micro-magic --micro-tabling

# Find all paths from a specific source node
cargo run --release -- --query-source 443 --micro-magic --micro-tabling --ascent

# Find all paths to a specific target node
cargo run --release -- --query-target 5678 --micro-magic --micro-tabling

# Find a specific path between two nodes
cargo run --release -- --query-source 1234 --query-target 5678 --micro-magic --micro-tabling

# Find all paths in the graph (both source and target are wildcards)
cargo run --release -- --micro-magic --micro-tabling

# Combine options
cargo run --release -- --use-all-data --query-source 1234 --micro-magic --micro-tabling
```

## Command Line Options
- `--edges <N>`: Number of edges to process (default: 20000)
- `--batch-size <N>`: Batch size for processing edges (default: 1000)
- `--use-all-data`: Use all available data instead of limiting to specified number of edges
- `--query-source <N>`: Source node for the query (if not specified, acts as a wildcard)
- `--query-target <N>`: Target node for the query (if not specified, acts as a wildcard)
- `--micro-streaming`: Run micro streaming benchmark
- `--micro-magic`: Run micro magic benchmark
- `--micro-tabling`: Run micro tabling benchmark
- `--crepe`: Run crepe benchmark
- `--ascent`: Run ascent benchmark
- `--skip-visualization`: Skip generating visualizations
- `--visualize-results <PATH>`: Generate visualizations from an existing results JSON file
- `--y-scale-performance <N>`: Maximum value for performance y-axis in visualization (default: 3000.0)
- `--y-scale-tuples <N>`: Maximum value for tuples y-axis in visualization (default: 509000.0)

## Visualization Commands
```bash
# Generate visualizations from an existing results file
cargo run --release -- --visualize-results results_20240418_123456.json

# Generate visualizations with custom y-axis scales
cargo run --release -- --visualize-results results_20240418_123456.json --y-scale-performance 5000.0 --y-scale-tuples 1000000.0

# Generate visualizations after running benchmarks
cargo run --release -- --micro-magic --micro-tabling --y-scale-performance 5000.0
```

cargo run --release -- --visualize-results results_20250502_160851.json --y-scale-performance 33.0