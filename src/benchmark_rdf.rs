use ascent::ascent;
use datalog_rule_macro::program;
use datalog_syntax::*;
use itertools::*;
use crate::benchmark::BenchmarkResult;
use crate::engine::datalog::{MicroRuntime, Strategy};
use lasso::Rodeo;
use lasso::Key;
use std::error::Error;
use std::time::{Duration, Instant};
use std::fs::File;
use std::io::Write;
use crate::args::Args;

ascent! {
    relation RDF(usize, usize, usize);
    relation T(usize, usize, usize);

    T(s, p, o) <-- RDF(s, p, o); 
    T(y, 0usize, x) <-- T(a, 3usize, x), T(y, a, z);
    T(z, 0usize, x) <-- T(a, 4usize, x), T(y, a, z);
    T(x, 2usize, z) <-- T(x, 2usize, y), T(y, 2usize, z);
    T(x, 1usize, z) <-- T(x, 1usize, y), T(y, 1usize, z);
    T(z, 0usize, y) <-- T(x, 1usize, y), T(z, 0usize, x);
    T(x, b, y) <-- T(a, 2usize, b), T(x, a, y);
}
    
const TYPE: &'static str = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>";
const SUB_CLASS_OF: &'static str = "<http://www.w3.org/2000/01/rdf-schema#subClassOf>";
const SUB_PROPERTY_OF: &'static str = "<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>";
const DOMAIN: &'static str = "<http://www.w3.org/2000/01/rdf-schema#domain>";
const RANGE: &'static str = "<http://www.w3.org/2000/01/rdf-schema#range>";
const PROPERTY: &'static str = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#Property>";
const PREFIX: &'static str = "http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#";

fn save_benchmark_results_to_txt(results: &[Vec<TypedValue>], filename: &str) -> Result<(), Box<dyn Error>> {
    let mut file = File::create(filename)?;
    for result in results {
        let values: Vec<String> = result.iter().map(|v| match v {
            TypedValue::Int(n) => n.to_string(),
            TypedValue::Str(s) => s.clone(),
            TypedValue::Bool(b) => b.to_string(),
        }).collect();
        writeln!(file, "{}", values.join(" "))?;
    }
    println!("Benchmark results saved to {}", filename);
    Ok(())
}

fn run_ascent_benchmark_lubm1(
    runtime: &mut AscentProgram,
    edges: &[(usize, usize, usize)],
    query_source: Option<usize>,
    query_target: Option<usize>,
    query_middle: Option<usize>,
) -> (Duration, usize, Vec<(usize, usize, usize)>) {

    for &(x, y, z) in edges {
        runtime.RDF.push((x, y, z));
    }

    let start = Instant::now();
    runtime.run();
    let elapsed_time = start.elapsed();
    // Query tuples based on source and target
    let results: Vec<_> = runtime
       .T
        .iter()
        .cloned()
        .filter(|&(x, y, z)| match (query_source, query_middle, query_target) {
            (Some(src), Some(middle), Some(tgt)) => x == src && z == tgt && y == middle,
            (Some(src), None, Some(tgt)) => x == src && z == tgt,
            (None, Some(middle), Some(tgt)) => y == middle && z == tgt,
            (Some(src), None, None) => x == src,
            (None, Some(middle), None) => y == middle,
            (None, None, Some(tgt)) => z == tgt,
            (Some(src), Some(middle), None) => x == src && y == middle,
            (None, None, None) => true,
        })
        .collect();
    (elapsed_time, results.len(), results)
}

fn run_micro_benchmark_lubm1(
    runtime: &mut MicroRuntime,
    edges: &Vec<(usize, usize, usize)>,
    strategy: Option<Strategy>,
    program: Program,
    query_source: Option<usize>,
    query_target: Option<usize>,
    query_middle: Option<usize>,
) -> (Duration, usize, Vec<Vec<TypedValue>>) {
    println!("Running micro benchmark with query: {:?}, {:?}, {:?}", query_source, query_middle, query_target);
    if let Some(s) = strategy {
        for &(from, middle, to) in edges {
            runtime.insert("RDF", (from, middle, to));
        }
        let query = match (query_source, query_middle, query_target) {
            (Some(src), Some(middle), Some(tgt)) => build_query!(T(src, middle, tgt)),
            (Some(src), None, Some(tgt)) => build_query!(T(src, _, tgt)),
            (None, Some(middle), Some(tgt)) => build_query!(T(_, middle, tgt)),
            (None, None, Some(tgt)) => build_query!(T(_, _, tgt)),
            (Some(src), Some(middle), None) => build_query!(T(src, middle, _)),
            (Some(src), None, None) => build_query!(T(src, _, _)),
            (None, Some(middle), None) => build_query!(T(_, middle, _)),
            (None, None, None) => build_query!(T(_, _, _)),
        };
        let (results, evaluation_time): (Vec<Vec<TypedValue>>, Duration) =
            runtime.query_program(&query, program, &s);
        (evaluation_time, results.len(), results)
    } else {
        for &(from, middle, to) in edges {
            runtime.insert("RDF", (from, middle, to));
        }
        let query = match (query_source, query_middle, query_target) {
            (Some(src), Some(middle), Some(tgt)) => build_query!(T(src, middle, tgt)),
            (Some(src), None, Some(tgt)) => build_query!(T(src, _, tgt)),
            (None, Some(middle), Some(tgt)) => build_query!(T(_, middle, tgt)),
            (None, None, Some(tgt)) => build_query!(T(_, _, tgt)),
            (Some(src), Some(middle), None) => build_query!(T(src, middle, _)),
            (Some(src), None, None) => build_query!(T(src, _, _)),
            (None, Some(middle), None) => build_query!(T(_, middle, _)),
            (None, None, None) => build_query!(T(_, _, _)),
        };
        let start = Instant::now();
        runtime.poll();
        let execution_time = start.elapsed();
        let results: Vec<Vec<TypedValue>> = runtime.query(&query).into_iter().flatten().collect();
        (execution_time, results.len(), results)
    }
}

pub fn run_benchmarks_rdf(
    batch_size: usize,
    args: &Args,
) -> Result<Vec<BenchmarkResult>, Box<dyn Error>> {
    let data = include_str!("../data/lubm1.nt");
    let program = program! { 
        T(?s, ?p, ?o) <- [RDF(?s, ?p, ?o)], 
        T(?y, 0usize, ?x) <- [T(?a, 3usize, ?x), T(?y, ?a, ?z)], 
        T(?z, 0usize, ?x) <- [T(?a, 4usize, ?x), T(?y, ?a, ?z)], 
        T(?x, 2usize, ?z) <- [T(?x, 2usize, ?y), T(?y, 2usize, ?z)], 
        T(?x, 1usize, ?z) <- [T(?x, 1usize, ?y), T(?y, 1usize, ?z)], 
        T(?z, 0usize, ?y) <- [T(?x, 1usize, ?y), T(?z, 0usize, ?x)], 
        T(?x, ?b, ?y) <- [T(?a, 2usize, ?b), T(?x, ?a, ?y)] 
    };

    // let program = program! {
    //     T(?s, ?p, ?o) <- [RDF(?s, ?p, ?o)],
    //     T(?x, ?y, ?z) <- [T(?x, ?y, ?z), T(?y, ?z, ?w)],
    // };

    // let program = program! { 
    //     T(?s, ?p, ?o) <- [RDF(?s, ?p, ?o)], 
    //     T(?a, ?b, ?c) <- [T(?d, ?e, ?c), T(?a, ?b, ?o)], 
    //     //T(?z, ?q, ?x) <- [T(?a, ?q, ?x), T(?y, ?a, ?z)], 
    //     //T(?z, ?q, ?x) <- [T(?a, ?q, ?x), T(?y, ?a, ?z)], 
    //     //T(?x, ?q, ?z) <- [T(?x, ?q, ?y), T(?y, ?q, ?z)], 
    //     //T(?x, ?q, ?z) <- [T(?x, ?q, ?y), T(?y, ?q, ?z)], 
    //     //T(?z, ?q, ?y) <- [T(?x, ?q, ?y), T(?z, ?q, ?x)], 
    //     //T(?x, ?b, ?y) <- [T(?a, ?q, ?b), T(?x, ?a, ?y)]
    // };

    // let program = program! {
    //     T(?s, ?p, ?o) <- [RDF(?s, ?p, ?o)],
    //     T(?y, 0usize, ?x) <- [T(?a, 3usize, ?x), RDF(?y, ?a, ?z)],
    // };

    let mut integral = Vec::new();
    let mut results = Vec::new();

    let mut streaming_micro = MicroRuntime::new(program.clone());
    let mut streaming_micro_magic = MicroRuntime::new(program.clone());
    let mut streaming_micro_tabling = MicroRuntime::new(program.clone());
    let mut ascent_runtime = AscentProgram::default();

    let mut rodeo = Rodeo::default();
    rodeo.get_or_intern_static(TYPE).into_usize();
    rodeo.get_or_intern_static(SUB_CLASS_OF);
    rodeo.get_or_intern_static(SUB_PROPERTY_OF);
    rodeo.get_or_intern_static(DOMAIN);
    rodeo.get_or_intern_static(RANGE);
    rodeo.get_or_intern_static(PROPERTY);

    let mut parsed_data = Vec::new();

    data.lines().into_iter().for_each(|line| {
        if !line.contains("genid") {
            let triple: Vec<_> = line
                .split_whitespace()
                .map(|resource| resource.trim().to_string())
                .collect();
            println!("Triple: {:?}", triple);
            let s = rodeo.get_or_intern(&triple[0]).into_usize();
            let p = rodeo.get_or_intern(&triple[1]).into_usize();
            let o = rodeo.get_or_intern(&triple[2]).into_usize();

            parsed_data.push((s, p, o));
        }
    });

    // Save parsed data to file
    //save_parsed_data_to_file(&parsed_data, "parsed_lubm1_data.txt")?;
    
    let chunk_size = if args.no_batching { parsed_data.len() } else { batch_size };

    for line_batch in &parsed_data.iter().chunks(chunk_size) {
        let batch: Vec<_> = line_batch
            .map(|(s, p, o)| (*s, *p, *o))
            .collect::<Vec<_>>();
        integral.extend_from_slice(&batch);

        // Run selected benchmarks on just the new batch
        if args.micro_streaming {
            let (time, tuples, result_tuples) = run_micro_benchmark_lubm1(
                &mut streaming_micro,
                &batch,
                None,
                program.clone(),
                args.query_source,
                args.query_target,
                args.query_middle,
            );

            results.push(BenchmarkResult::new(
                "micro-streaming",
                batch.len(),
                integral.len(),
                time,
                tuples,
                result_tuples.clone(),
            ));
            println!("Micro-streaming result tuples number: {:?}", result_tuples.len());
        }

        if args.micro_magic {
            let (time, tuples, result_tuples) = run_micro_benchmark_lubm1(
                &mut streaming_micro_magic,
                &batch,
                Some(Strategy::BottomUp),
                program.clone(),
                args.query_source,
                args.query_target,
                args.query_middle,
            );
            results.push(BenchmarkResult::new(
                "micro-magic",
                batch.len(),
                integral.len(),
                time,
                tuples,
                vec![],
            ));
            println!("Micro-magic result tuples number: {:?}", result_tuples.len());
        }

        if args.micro_tabling {
            let (time, tuples, result_tuples) = run_micro_benchmark_lubm1(
                &mut streaming_micro_tabling,
                &batch,
                Some(Strategy::TopDown),
                program.clone(),
                args.query_source,
                args.query_target,
                args.query_middle,
            );
            results.push(BenchmarkResult::new(
                "micro-tabling",
                batch.len(),
                integral.len(),
                time,
                tuples,
                result_tuples.clone(),
            ));

            println!("Micro-tabling result tuples number: {:?}", result_tuples.len());
        }

        if args.ascent {
            let (time, tuples, result_tuples) = run_ascent_benchmark_lubm1(
                &mut ascent_runtime,
                &integral,
                args.query_source,
                args.query_target,
                args.query_middle,
            );
            let converted_result_tuples: Vec<Vec<TypedValue>> = result_tuples
                .into_iter()
                .map(|(a, b, c)| vec![TypedValue::from(a), TypedValue::from(b), TypedValue::from(c)])
                .collect();

            results.push(BenchmarkResult::new(
                "ascent",
                batch.len(),
                integral.len(),
                time,
                tuples,
                converted_result_tuples.clone(),
            ));
            println!("Ascent result tuples number: {:?}", converted_result_tuples.len());
        }

        // Print progress
        println!("Processed {} edges", integral.len());
    }

    // Save benchmark results to text file
    if let Some(last_result) = results.last() {
        save_benchmark_results_to_txt(&last_result.result_tuples, "benchmark_results.txt")?;
    }

    Ok(results)
}
