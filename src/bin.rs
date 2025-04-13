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
    let mut streaming_micro = MicroRuntime::new(program.clone());
    let mut streaming_micro_magic = MicroRuntime::new(program.clone());
    let mut streaming_micro_tabling = MicroRuntime::new(program.clone());

    let mut integral = Vec::new();
    let mut results = Vec::new();

    for line_batch in &data.lines().chunks(batch_size) {
        let batch: Vec<_> = line_batch
            .map(|line| parse_edge(line))
            .collect::<Result<Vec<_>, _>>()?;

        integral.extend_from_slice(&batch);

        // Run selected benchmarks
        if args.micro_streaming {
            let (time, tuples) = run_micro_benchmark(&mut streaming_micro, &batch, None);
            results.push(BenchmarkResult::new(
                "micro-streaming",
                batch_size,
                integral.len(),
                time,
                tuples,
            ));
        }

        if args.micro_magic {
            let (time, tuples) =
                run_micro_benchmark(&mut streaming_micro_magic, &batch, Some(Strategy::BottomUp));
            results.push(BenchmarkResult::new(
                "micro-magic",
                batch_size,
                integral.len(),
                time,
                tuples,
            ));
        }

        if args.micro_tabling {
            let (time, tuples) = run_micro_benchmark(
                &mut streaming_micro_tabling,
                &batch,
                Some(Strategy::TopDown),
            );
            results.push(BenchmarkResult::new(
                "micro-tabling",
                batch_size,
                integral.len(),
                time,
                tuples,
            ));
        }

        // Run integral benchmarks
        if args.micro_streaming {
            let mut micro_runtime = MicroRuntime::new(program.clone());
            let (time, tuples) = run_micro_benchmark(&mut micro_runtime, &integral, None);
            results.push(BenchmarkResult::new(
                "micro-integral",
                integral.len(),
                integral.len(),
                time,
                tuples,
            ));
        }

        if args.crepe {
            let (time, tuples) = run_crepe_benchmark(&integral);
            results.push(BenchmarkResult::new(
                "crepe",
                integral.len(),
                integral.len(),
                time,
                tuples,
            ));
        }

        if args.ascent {
            let (time, tuples) = run_ascent_benchmark(&integral);
            results.push(BenchmarkResult::new(
                "ascent",
                integral.len(),
                integral.len(),
                time,
                tuples,
            ));
        }

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

    // Run benchmarks and save results
    // println!("Running benchmarks on first {} edges...", args.edges);
    // let results = run_benchmarks(&program, &limited_data, args.batch_size, &args)?;
    // save_benchmark_results(&results, results_path)?;
    // println!(
    //     "Benchmarks completed and saved to {}",
    //     results_path.display()
    // );

    if !args.skip_visualization {
        // Load results and generate visualizations
        println!("Generating visualizations...");
        let results = load_benchmark_results(Path::new("results_20250413_180035.json"))?;

        // Create visualization options based on selected benchmarks
        let vis_options = micro_datalog::visualization::VisualizationOptions {
            show_micro_streaming: args.micro_streaming,
            show_micro_magic: args.micro_magic,
            show_micro_tabling: args.micro_tabling,
            show_crepe: args.crepe,
            show_ascent: args.ascent,
            x_scale: Some((0.0, 509000.0)), // Set x-axis from 0 to total edges
            y_scale_performance: Some((0.0, 0.45)),   // Set performance y-axis from 0 to 5000ms
            y_scale_tuples: Some((0.0, 509000.0)),   // Set tuples y-axis from 0 to 100000 tuples
        };

        visualize_results(&results, vis_dir, &vis_options)?;
        println!("Visualizations saved to {}", vis_dir.display());
    }

    Ok(())
}
