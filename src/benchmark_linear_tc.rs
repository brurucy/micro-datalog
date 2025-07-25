use crate::args::Args;
use crate::benchmark::BenchmarkResult;
use crate::engine::datalog::{MicroRuntime, Strategy};
use ascent::ascent;
use datalog_rule_macro::program;
use datalog_syntax::*;
use itertools::*;
use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::time::{Duration, Instant};

ascent! {
    relation e(usize, usize);
    relation tc(usize, usize);

    tc(x, y) <-- e(x, y);
    tc(x, z) <-- e(x, y), tc(y, z);
}

// fn save_benchmark_results_to_txt(
//     results: &[Vec<TypedValue>],
//     filename: &str,
// ) -> Result<(), Box<dyn Error>> {
//     println!("Saving benchmark results to {}", filename);
//     let mut file = File::create(filename)?;
//     for result in results {
//         let values: Vec<String> = result
//             .iter()
//             .map(|v| match v {
//                 TypedValue::Int(n) => n.to_string(),
//                 TypedValue::Str(s) => s.clone(),
//                 TypedValue::Bool(b) => b.to_string(),
//             })
//             .collect();
//         writeln!(file, "{}", values.join(" "))?;
//     }
//     println!("Benchmark results saved to {}", filename);
//     Ok(())
// }

fn parse_edge(line: &str, args: &Args) -> Result<(usize, usize), Box<dyn std::error::Error>> {
    let parts: Vec<_> = line.split(' ').collect();
    if args.fb && parts.len() != 2 {
        return Err("Invalid edge format for fb".into());
    } else if args.dense && parts.len() != 3 {
        return Err("Invalid edge format for dense".into());
    } else if args.sparse && parts.len() != 3 {
        return Err("Invalid edge format for sparse".into());
    }
    let from = parts[0].parse()?;
    let to = parts[1].parse()?;
    Ok((from, to))
}

fn run_micro_benchmark(
    runtime: &mut MicroRuntime,
    edges: &Vec<(usize, usize)>,
    strategy: Option<Strategy>,
    program: Program,
    query_source: Option<usize>,
    query_target: Option<usize>,
) -> (Duration, usize, Vec<Vec<TypedValue>>) {
    for &(from, to) in edges {
        runtime.insert("e", (from, to));
    }
    let query = match (query_source, query_target) {
        (Some(src), Some(tgt)) => build_query!(tc(src, tgt)),
        (Some(src), None) => build_query!(tc(src, _)),
        (None, Some(tgt)) => build_query!(tc(_, tgt)),
        (None, None) => build_query!(tc(_, _)),
    };
    if let Some(s) = strategy {
        //println!("Running micro-streaming with strategy: {:?}", s);
        let (results, evaluation_time): (Vec<Vec<TypedValue>>, Duration) =
            runtime.query_program(&query, program, &s);
        (evaluation_time, results.len(), results)
    } else {
        //println!("Running micro-streaming without strategy");
        let start = Instant::now();
        runtime.poll();
        let execution_time = start.elapsed();
        let results: Vec<Vec<TypedValue>> = runtime.query(&query).into_iter().flatten().collect();
        (execution_time, results.len(), results)
    }
}

fn run_ascent_benchmark(
    runtime: &mut AscentProgram,
    edges: &[(usize, usize)],
    query_source: Option<usize>,
    query_target: Option<usize>,
) -> (Duration, usize, Vec<(usize, usize)>) {
    //println!("Running ascent benchmark...");
    //println!("Number of edges: {:?}", edges.len());
    for &(from, to) in edges {
        runtime.e.push((from, to));
    }
    // println!("Starting ascent runtime...");
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

pub fn run_benchmarks_tc_linear(
    batch_size: usize,
    args: &Args,
) -> Result<Vec<BenchmarkResult>, Box<dyn Error>> {
    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
    };

    let data = if args.fb {
        println!("Using facebook data...");
        include_str!("../data/facebook_combined.txt")
    } else if args.dense {
        println!("Using dense data...");
        include_str!("../data/graph_dense.txt")
    } else if args.sparse {
        println!("Using sparse data...");
        include_str!("../data/graph_sparse.txt")
    } else {
        println!("Using abridged fb data...");
        include_str!("../data/random_edges_facebook_combined.txt")
    };

    let data_to_process = if let Some(edges) = args.edges {
        println!("Using first {} edges...", edges);
        data.lines().take(edges).collect::<Vec<_>>().join("\n")
    } else {
        println!("Using all available data...");
        data.to_string()
    };

    let mut integral = Vec::new();
    let mut results = Vec::new();

    let mut streaming_micro = MicroRuntime::new(program.clone());
    let mut streaming_micro_magic = MicroRuntime::new(program.clone());
    let mut streaming_micro_tabling = MicroRuntime::new(program.clone());
    let mut ascent_runtime = AscentProgram::default();

    let chunk_size = if args.no_batching {
        data_to_process.len()
    } else {
        batch_size
    };
    println!("Chunk size: {:?}", chunk_size);
    for line_batch in &data_to_process.lines().chunks(chunk_size) {
        let batch: Vec<_> = line_batch
            .map(|line| parse_edge(line, args))
            .collect::<Result<Vec<_>, _>>()?;
        integral.extend_from_slice(&batch);

        // Run selected benchmarks on just the new batch
        if args.micro_streaming {
            let (time, tuples, _result_tuples) = run_micro_benchmark(
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
                vec![],
            ));

            //println!("Micro-streaming tuples len: {:?}", result_tuples.len());
        }

        if args.micro_magic {
            let (time, tuples, _result_tuples) = run_micro_benchmark(
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
                vec![],
            ));
            //println!("Micro-magic tuples len: {:?}", result_tuples.len());
        }

        if args.micro_tabling {
            let (time, tuples, result_tuples) = run_micro_benchmark(
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
            let (time, tuples, result_tuples) = run_ascent_benchmark(
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
