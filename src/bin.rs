use ascent::ascent;
use crepe::crepe;
use datalog_rule_macro::program;
use datalog_syntax::*;
use itertools::*;
use micro_datalog::engine::datalog::{MicroRuntime, Strategy};
use std::time::{Duration, Instant};

#[derive(Debug)]
struct BenchmarkResult {
    strategy: String,
    batch_size: usize,
    cumulative_edges: usize,
    execution_time_micros: u128,
    inferred_tuples: usize,
}

impl BenchmarkResult {
    fn new(strategy: &str, batch_size: usize, edges: usize, time: Duration, tuples: usize) -> Self {
        Self {
            strategy: strategy.to_string(),
            batch_size,
            cumulative_edges: edges,
            execution_time_micros: time.as_micros(),
            inferred_tuples: tuples,
        }
    }
}

// Define Datalog programs
crepe! {
    @input
    struct E(usize, usize);

    @output
    struct TC(usize, usize);

    TC(x, y) <- E(x, y);
    TC(x, z) <- E(x, y), TC(y, z);
}

ascent! {
    relation e(usize, usize);
    relation tc(usize, usize);

    tc(x, y) <-- e(x, y);
    tc(x, z) <-- e(x, y), tc(y, z);
}

fn parse_edge(line: &str) -> Result<(usize, usize), Box<dyn std::error::Error>> {
    let parts: Vec<_> = line.split('\t').collect();
    if parts.len() != 2 {
        return Err("Invalid edge format".into());
    }
    let from = parts[0].parse()?;
    let to = parts[1].parse()?;
    Ok((from, to))
}

fn run_micro_benchmark(
    runtime: &mut MicroRuntime,
    edges: &[(usize, usize)],
    strategy: Option<Strategy>,
) -> (Duration, usize) {
    let start = Instant::now();
    
    if let Some(s) = strategy {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let query = build_query!(tc(_, _));
        let results: Vec<_> = runtime
            .query_program(&query, program, &s)
            .into_iter()
            .collect();
        (start.elapsed(), results.len())
    } else {
        for &(from, to) in edges {
            runtime.insert("e", (from, to));
        }
        runtime.poll();
        let query = build_query!(tc(_, _));
        let results: Vec<_> = runtime.query(&query).into_iter().collect();
        (start.elapsed(), results.len())
    }
}

fn run_crepe_benchmark(edges: &[(usize, usize)]) -> (Duration, usize) {
    let start = Instant::now();
    let mut runtime = Crepe::new();
    
    for &(from, to) in edges {
        runtime.e.push(E(from, to));
    }
    
    let results = runtime.run();
    (start.elapsed(), results.0.len())
}

fn run_ascent_benchmark(edges: &[(usize, usize)]) -> (Duration, usize) {
    let start = Instant::now();
    let mut runtime = AscentProgram::default();
    
    for &(from, to) in edges {
        runtime.e.push((from, to));
    }
    
    runtime.run();
    (start.elapsed(), runtime.tc.len())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
    };

    let mut streaming_micro = MicroRuntime::new(program.clone());
    let mut streaming_micro_magic = MicroRuntime::new(program.clone());
    let mut streaming_micro_tabling = MicroRuntime::new(program.clone());

    let batch_size = 10;
    let data = include_str!("../data/soc-Epinions1.txt");
    let mut integral = Vec::new();
    let mut results = Vec::new();

    for line_batch in &data.lines().chunks(batch_size) {
        let batch: Vec<_> = line_batch
            .map(|line| parse_edge(line))
            .collect::<Result<Vec<_>, _>>()?;
        
        integral.extend_from_slice(&batch);

        // Run benchmarks
        let (time, tuples) = run_micro_benchmark(&mut streaming_micro, &batch, None);
        results.push(BenchmarkResult::new("micro-streaming", batch_size, integral.len(), time, tuples));

        let (time, tuples) = run_micro_benchmark(&mut streaming_micro_magic, &batch, Some(Strategy::BottomUp));
        results.push(BenchmarkResult::new("micro-magic", batch_size, integral.len(), time, tuples));

        let (time, tuples) = run_micro_benchmark(&mut streaming_micro_tabling, &batch, Some(Strategy::TopDown));
        results.push(BenchmarkResult::new("micro-tabling", batch_size, integral.len(), time, tuples));

        // Run integral benchmarks
        let mut micro_runtime = MicroRuntime::new(program.clone());
        let (time, tuples) = run_micro_benchmark(&mut micro_runtime, &integral, None);
        results.push(BenchmarkResult::new("micro-integral", integral.len(), integral.len(), time, tuples));

        let (time, tuples) = run_crepe_benchmark(&integral);
        results.push(BenchmarkResult::new("crepe", integral.len(), integral.len(), time, tuples));

        let (time, tuples) = run_ascent_benchmark(&integral);
        results.push(BenchmarkResult::new("ascent", integral.len(), integral.len(), time, tuples));

        // Print results
        for result in &results {
            println!(
                "{:15} | batch: {:4} | edges: {:6} | time: {:8}μs | tuples: {:6}",
                result.strategy,
                result.batch_size,
                result.cumulative_edges,
                result.execution_time_micros,
                result.inferred_tuples
            );
        }
        println!();
    }

    Ok(())
}

