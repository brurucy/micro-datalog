use crate::args::Args;
use crate::benchmark::BenchmarkResult;
use crate::engine::datalog::{MicroRuntime, Strategy};
use ascent::ascent;
use datalog_rule_macro::program;
use datalog_syntax::*;
use itertools::*;
use std::error::Error;
use std::time::{Duration, Instant};

ascent! {
    relation e(usize, usize);
    relation tc(usize, usize);

    tc(x, y) <-- e(x, y);
    tc(x, z) <-- tc(x, y), tc(y, z);
}

fn parse_edge(line: &str) -> Result<(usize, usize), Box<dyn std::error::Error>> {
    let parts: Vec<_> = line.split(' ').collect();
    if parts.len() != 2 {
        return Err("Invalid edge format".into());
    }
    let from = parts[0].parse()?;
    let to = parts[1].parse()?;
    Ok((from, to))
}

fn run_micro_benchmark_facebook(
    runtime: &mut MicroRuntime,
    edges: &Vec<(usize, usize)>,
    strategy: Option<Strategy>,
    program: Program,
    query_source: Option<usize>,
    query_target: Option<usize>,
) -> (Duration, usize, Vec<Vec<TypedValue>>) {
    if let Some(s) = strategy {
        for &(from, to) in edges {
            runtime.insert("e", (from, to));
        }
        let query = match (query_source, query_target) {
            (Some(src), Some(tgt)) => build_query!(tc(src, tgt)),
            (Some(src), None) => build_query!(tc(src, _)),
            (None, Some(tgt)) => build_query!(tc(_, tgt)),
            (None, None) => build_query!(tc(_, _)),
        };
        let (results, evaluation_time): (Vec<Vec<TypedValue>>, Duration) =
            runtime.query_program(&query, program, &s);
        (evaluation_time, results.len(), results)
    } else {
        for &(from, to) in edges {
            runtime.insert("e", (from, to));
        }
        let query = match (query_source, query_target) {
            (Some(src), Some(tgt)) => build_query!(tc(src, tgt)),
            (Some(src), None) => build_query!(tc(src, _)),
            (None, Some(tgt)) => build_query!(tc(_, tgt)),
            (None, None) => build_query!(tc(_, _)),
        };
        let start = Instant::now();
        runtime.poll();
        let execution_time = start.elapsed();
        let results: Vec<Vec<TypedValue>> = runtime.query(&query).into_iter().flatten().collect();
        (execution_time, results.len(), results)
    }
}

fn run_ascent_benchmark_facebook(
    runtime: &mut AscentProgram,
    edges: &[(usize, usize)],
    query_source: Option<usize>,
    query_target: Option<usize>,
) -> (Duration, usize, Vec<(usize, usize)>) {
    for &(from, to) in edges {
        runtime.e.push((from, to));
    }

    let start = Instant::now();
    runtime.run();
    let elapsed_time = start.elapsed();
    // Query tuples based on source and target
    let results: Vec<_> = runtime
        .tc
        .iter()
        .cloned()
        .filter(|&(from, to)| match (query_source, query_target) {
            (Some(src), Some(tgt)) => from == src && to == tgt,
            (Some(src), None) => from == src,
            (None, Some(tgt)) => to == tgt,
            (None, None) => true,
        })
        .collect();
    (elapsed_time, results.len(), results)
}

pub fn run_benchmarks_tc(
    batch_size: usize,
    args: &Args,
) -> Result<Vec<BenchmarkResult>, Box<dyn Error>> {

    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
    };

    let data = include_str!("../data/facebook_combined.txt");

    //Process data based on whether we want to use all data or limited data
    let data_to_process = if args.use_all_data {
        println!("Using all available data...");
        data.to_string()
    } else {
        println!("Using first {} edges...", args.edges);
        data.lines().take(args.edges).collect::<Vec<_>>().join("\n")
    };

    let mut integral = Vec::new();
    let mut results = Vec::new();

    let mut streaming_micro = MicroRuntime::new(program.clone());
    let mut streaming_micro_magic = MicroRuntime::new(program.clone());
    let mut streaming_micro_tabling = MicroRuntime::new(program.clone());
    let mut ascent_runtime = AscentProgram::default();
    
    let chunk_size = if args.no_batching { data_to_process.len() } else { batch_size };
    
    for line_batch in &data_to_process.lines().chunks(chunk_size) {
        let batch: Vec<_> = line_batch
            .map(|line| parse_edge(line))
            .collect::<Result<Vec<_>, _>>()?;
        integral.extend_from_slice(&batch);

        // Run selected benchmarks on just the new batch
        if args.micro_streaming {
            let (time, tuples, result_tuples) = run_micro_benchmark_facebook(
                &mut streaming_micro,
                &batch,
                None,
                program.clone(),
                args.query_source,
                args.query_target,
            );

            results.push(BenchmarkResult::new(
                "micro-streaming",
                batch.len(),
                integral.len(),
                time,
                tuples,
                result_tuples.clone(),
            ));

            println!("Micro-streaming tuples len: {:?}", result_tuples.len());
        }

        if args.micro_magic {
            let (time, tuples, result_tuples) = run_micro_benchmark_facebook(
                &mut streaming_micro_magic,
                &batch,
                Some(Strategy::BottomUp),
                program.clone(),
                args.query_source,
                args.query_target,
            );
            results.push(BenchmarkResult::new(
                "micro-magic",
                batch.len(),
                integral.len(),
                time,
                tuples,
                result_tuples.clone(),
            ));
            println!("Micro-magic tuples len: {:?}", result_tuples.len());
        }

        if args.micro_tabling {
            let (time, tuples, result_tuples) = run_micro_benchmark_facebook(
                &mut streaming_micro_tabling,
                &batch,
                Some(Strategy::TopDown),
                program.clone(),
                args.query_source,
                args.query_target,
            );
            results.push(BenchmarkResult::new(
                "micro-tabling",
                batch.len(),
                integral.len(),
                time,
                tuples,
                result_tuples.clone(),
            ));
            println!("Micro-tabling tuples len: {:?}", result_tuples.len());
        }

        if args.ascent {
            let (time, tuples, result_tuples) = run_ascent_benchmark_facebook(
                &mut ascent_runtime,
                &integral,
                args.query_source,
                args.query_target,
            );
            let converted_result_tuples: Vec<Vec<TypedValue>> = result_tuples
                .into_iter()
                .map(|(a, b)| vec![TypedValue::from(a), TypedValue::from(b)])
                .collect();

            results.push(BenchmarkResult::new(
                "ascent",
                batch.len(),
                integral.len(),
                time,
                tuples,
                converted_result_tuples.clone(),
            ));

            println!("Ascent tuples len: {:?}", converted_result_tuples.len());
        }

        // Print progress
        println!("Processed {} edges", integral.len());
    }

    Ok(results)
}
