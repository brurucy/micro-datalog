use ascent::ascent;
use chrono::Local;
use clap::Parser;
use crepe::crepe;
use datalog_rule_macro::program;
use datalog_syntax::*;
use itertools::*;
use micro_datalog::benchmark::BenchmarkResult;
use micro_datalog::engine::datalog::{MicroRuntime, Strategy};
use micro_datalog::visualization::visualize_results;
use plotters::prelude::*;
use serde::{Deserialize, Serialize};
use std::error::Error;
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;
use std::time::{Duration, Instant};

/// Command line arguments for the benchmark tool
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Number of edges to process
    #[arg(short, long, default_value_t = 20000)]
    edges: usize,

    /// Batch size for processing edges
    #[arg(short, long, default_value_t = 1000)]
    batch_size: usize,

    /// Run micro streaming benchmark
    #[arg(long)]
    micro_streaming: bool,

    /// Run micro magic benchmark
    #[arg(long)]
    micro_magic: bool,

    /// Run micro tabling benchmark
    #[arg(long)]
    micro_tabling: bool,

    /// Run crepe benchmark
    #[arg(long)]
    crepe: bool,

    /// Run ascent benchmark
    #[arg(long)]
    ascent: bool,

    /// Skip visualization
    #[arg(long)]
    skip_visualization: bool,
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
    program: Program,
) -> (Duration, usize) {
    if let Some(s) = strategy {
       
        for &(from, to) in edges {
            runtime.insert("e", (from, to));
        }
        let query = build_query!(tc(_, _));
        let start = Instant::now();
        let results: Vec<Vec<TypedValue>> = runtime
            .query_program(&query, program, &s)
            .into_iter()
            .flatten()
            .collect();
        (start.elapsed(), results.len())
    } else {
        for &(from, to) in edges {
            runtime.insert("e", (from, to));
        }
        let query = build_query!(tc(_, _));
        let start = Instant::now();
        runtime.poll();
        let execution_time = start.elapsed();
        let results: Vec<_> = runtime.query(&query).into_iter().collect();
        (execution_time, results.len())
    }
}

fn run_crepe_benchmark(edges: &[(usize, usize)]) -> (Duration, usize) {
    let mut runtime = Crepe::new();
    for &(from, to) in edges {
        runtime.e.push(E(from, to));
    }

    let start = Instant::now();
    let results = runtime.run();
    (start.elapsed(), results.0.len())
}

fn run_ascent_benchmark(
    runtime: &mut AscentProgram,
    edges: &[(usize, usize)],
) -> (Duration, usize) {
    let start = Instant::now();

    for &(from, to) in edges {
        runtime.e.push((from, to));
    }

    runtime.run();
    (start.elapsed(), runtime.tc.len())
}

fn save_benchmark_results(results: &[BenchmarkResult], path: &Path) -> Result<(), Box<dyn Error>> {
    let file = File::create(path)?;
    let writer = BufWriter::new(file);
    serde_json::to_writer(writer, results)?;
    Ok(())
}

fn load_benchmark_results(path: &Path) -> Result<Vec<BenchmarkResult>, Box<dyn Error>> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let results = serde_json::from_reader(reader)?;
    Ok(results)
}

fn run_benchmarks(
    program: &Program,
    data: &str,
    batch_size: usize,
    args: &Args,
) -> Result<Vec<BenchmarkResult>, Box<dyn Error>> {
    let mut integral = Vec::new();
    let mut results = Vec::new();

    let mut streaming_micro = MicroRuntime::new(program.clone());
    let mut streaming_micro_magic = MicroRuntime::new(program.clone());
    let mut streaming_micro_tabling = MicroRuntime::new(program.clone());
    let mut ascent_runtime = AscentProgram::default();

    for line_batch in &data.lines().chunks(batch_size) {
        let batch: Vec<_> = line_batch
            .map(|line| parse_edge(line))
            .collect::<Result<Vec<_>, _>>()?;

        // Run selected benchmarks on just the new batch
        if args.micro_streaming {
            let (time, tuples) = run_micro_benchmark(&mut streaming_micro, &batch, None, program.clone());
            results.push(BenchmarkResult::new(
                "micro-streaming",
                integral.len() + batch.len(),
                integral.len() + batch.len(),
                time,
                tuples,
            ));
        }

        if args.micro_magic {
            let (time, tuples) = run_micro_benchmark(
                &mut streaming_micro_magic,
                &batch,
                Some(Strategy::BottomUp),
                program.clone(),
            );
            results.push(BenchmarkResult::new(
                "micro-magic",
                integral.len() + batch.len(),
                integral.len() + batch.len(),
                time,
                tuples,
            ));
        }

        if args.micro_tabling {
            let (time, tuples) = run_micro_benchmark(
                &mut streaming_micro_tabling,
                &batch,
                Some(Strategy::TopDown),
                program.clone(),
            );
            results.push(BenchmarkResult::new(
                "micro-tabling",
                integral.len() + batch.len(),
                integral.len() + batch.len(),
                time,
                tuples,
            ));
        }

        // Run integral benchmarks
        if args.crepe {
            let (time, tuples) = run_crepe_benchmark(&batch);
            results.push(BenchmarkResult::new(
                "crepe",
                integral.len() + batch.len(),
                integral.len() + batch.len(),
                time,
                tuples,
            ));
        }

        if args.ascent {
            let (time, tuples) = run_ascent_benchmark(&mut ascent_runtime, &batch);
            results.push(BenchmarkResult::new(
                "ascent",
                integral.len() + batch.len(),
                integral.len() + batch.len(),
                time,
                tuples,
            ));
        }

        // Add the new batch to the integral for the next iteration
        integral.extend_from_slice(&batch);

        // Print progress
        println!("Processed {} edges", integral.len());
    }

    Ok(results)
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
    };

    let data = include_str!("../data/soc-Epinions1.txt");
    let vis_dir = Path::new("visualizations");

    // Take only the specified number of edges
    let limited_data: String = data.lines().take(args.edges).collect::<Vec<_>>().join("\n");

    // Create timestamped results file
    let timestamp = Local::now().format("%Y%m%d_%H%M%S").to_string();
    let res_path_string = format!("results_{}.json", timestamp);
    let results_path = Path::new(&res_path_string);

    //Run benchmarks and save results
    println!("Running benchmarks on first {} edges...", args.edges);
    let results = run_benchmarks(&program, &limited_data, args.batch_size, &args)?;
    save_benchmark_results(&results, results_path)?;
    println!(
        "Benchmarks completed and saved to {}",
        results_path.display()
    );

    if !args.skip_visualization {
        // Load results and generate visualizations
        println!("Generating visualizations...");
        //let results = load_benchmark_results(Path::new("results_20250415_154341.json"))?;
        let results = load_benchmark_results(results_path)?;
        // Create visualization options based on selected benchmarks
        let vis_options = micro_datalog::visualization::VisualizationOptions {
            show_micro_streaming: args.micro_streaming,
            show_micro_magic: args.micro_magic,
            show_micro_tabling: args.micro_tabling,
            show_crepe: args.crepe,
            show_ascent: args.ascent,
            x_scale: Some((0.0, args.edges as f64)), // Set x-axis from 0 to total edges
            y_scale_performance: Some((0.0, 150000.0)), // Set performance y-axis from 0 to 5000ms
            y_scale_tuples: Some((0.0, 509000.0)), // Set tuples y-axis from 0 to 100000 tuples
        };

        visualize_results(&results, vis_dir, &vis_options)?;
        println!("Visualizations saved to {}", vis_dir.display());
    }

    Ok(())
}
