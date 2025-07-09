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
use lasso::Rodeo;
use lasso::Key;
use std::error::Error;
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;
use std::path::PathBuf;
use std::time::{Duration, Instant};

// lubm1.nt
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

    /// Use all available data instead of limiting to specified number of edges
    #[arg(long)]
    use_all_data: bool,

    /// Source node for the query
    #[arg(long)]
    query_source: Option<usize>,

    /// Target node for the query
    #[arg(long)]
    query_target: Option<usize>,

    /// Middle node for the query
    #[arg(long)]
    query_middle: Option<usize>,

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

    /// Path to results JSON file for visualization
    #[arg(long)]
    visualize_results: Option<PathBuf>,

    /// Maximum value for performance y-axis in visualization
    #[arg(long, default_value_t = 3000.0)]
    y_scale_performance: f64,

    /// Maximum value for tuples y-axis in visualization
    #[arg(long, default_value_t = 509000.0)]
    y_scale_tuples: f64,
}

// Define Datalog programs
// crepe! {
//     @input
//     struct E(usize, usize);

//     @output
//     struct TC(usize, usize);

//     TC(x, y) <- E(x, y);
//     TC(x, z) <- E(x, y), TC(y, z);
// }

// ascent! {
//     relation e(usize, usize);
//     relation tc(usize, usize);

//     tc(x, y) <-- e(x, y);
//     tc(x, z) <-- e(x, y), tc(y, z);
// }

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

fn parse_triple(line: &str) -> (&str, &str, &str) {
    let triple: Vec<_> = line.split(">").collect();

    return (triple[0], triple[1], triple[2]);
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

fn run_micro_benchmark_lubm1(
    runtime: &mut MicroRuntime,
    edges: &Vec<(usize, usize, usize)>,
    strategy: Option<Strategy>,
    program: Program,
    query_source: Option<usize>,
    query_target: Option<usize>,
    query_middle: Option<usize>,
) -> (Duration, usize, Vec<Vec<TypedValue>>) {
    if let Some(s) = strategy {
        for &(from, middle, to) in edges {
            runtime.insert("RDF", (from, middle,to));
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
            runtime.insert("e", (from,to));
        }
        let query = match (query_source, query_target) {
            (Some(src), Some(tgt)) => build_query!(T(src, tgt)),
            (Some(src), None) => build_query!(T(src, _)),
            (None, Some(tgt)) => build_query!(T(_, tgt)),
            (None, None) => build_query!(T(_, _)),
        };
        let (results, evaluation_time): (Vec<Vec<TypedValue>>, Duration) =
            runtime.query_program(&query, program, &s);
        (evaluation_time, results.len(), results)
    } else {
        for &(from, to) in edges {
            runtime.insert("e", (from, to));
        }
        let query = match (query_source, query_target) {
            (Some(src), Some(tgt)) => build_query!(T(src, tgt)),
            (Some(src), None) => build_query!(T(src, _)),
            (None, Some(tgt)) => build_query!(T(_, tgt)),
            (None, None) => build_query!(T(_, _)),
        };
        let start = Instant::now();
        runtime.poll();
        let execution_time = start.elapsed();
        let results: Vec<Vec<TypedValue>> = runtime.query(&query).into_iter().flatten().collect();
        (execution_time, results.len(), results)
    }
}

// fn run_crepe_benchmark(edges: &[(usize, usize)]) -> (Duration, usize) {
//     let mut runtime = Crepe::new();
//     for &(from, to) in edges {
//         runtime.e.push(E(from, to));
//     }

//     let start = Instant::now();
//     let results = runtime.run();
//     (start.elapsed(), results.0.len())
// }

fn run_ascent_benchmark_lubm1(
    runtime: &mut AscentProgram,
    // edges: &[(usize, usize)],
    edges: &[(usize, usize, usize)],
    query_source: Option<usize>,
    query_target: Option<usize>,
    query_middle: Option<usize>,
) -> (Duration, usize, Vec<(usize, usize, usize)>) {
    // for &(from, to) in edges {
    //     runtime.e.push((from, to));
    // }

    for &(x, y, z) in edges {
        runtime.RDF.push((x, y, z));
    }

    let start = Instant::now();
    runtime.run();
    let elapsed_time = start.elapsed();
    // Query tuples based on source and target
    let results: Vec<_> = runtime
        //.tc
       .T
        .iter()
        .cloned()
        // .filter(|&(x, y, z)| match (query_source, middle, query_target) {
        //     (Some(src), Some(tgt)) => from == src && to == tgt,
        //     (Some(src), None) => from == src,
        //     (None, Some(tgt)) => to == tgt,
        //     (None, None) => true,
        // })
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

// fn run_ascent_benchmark_facebook(
//     runtime: &mut AscentProgram,
//     edges: &[(usize, usize)],
//     query_source: Option<usize>,
//     query_target: Option<usize>,
// ) -> (Duration, usize, Vec<(usize, usize, usize)>) {
//     for &(from, to) in edges {
//         runtime.e.push((from, to));
//     }

//     let start = Instant::now();
//     runtime.run();
//     let elapsed_time = start.elapsed();
//     // Query tuples based on source and target
//     let results: Vec<_> = runtime
//         .tc
//         .iter()
//         .cloned()
//         .filter(|&(from, to)| match (query_source, query_target) {
//             (Some(src), Some(tgt)) => from == src && to == tgt,
//             (Some(src), None) => from == src,
//             (None, Some(tgt)) => to == tgt,
//             (None, None) => true,
//         }) 
//         .collect();
//     (elapsed_time, results.len(), results)
// }

fn save_benchmark_results(results: &[BenchmarkResult], path: &Path) -> Result<(), Box<dyn Error>> {
    // Create results directory if it doesn't exist
    std::fs::create_dir_all("results")?;

    // Create the full path in the results directory
    let full_path = Path::new("results").join(path);

    let file = File::create(full_path)?;
    let writer = BufWriter::new(file);
    serde_json::to_writer(writer, results)?;
    Ok(())
}

fn load_benchmark_results(path: &Path) -> Result<Vec<BenchmarkResult>, Box<dyn Error>> {
    // Create the full path in the results directory
    let full_path = Path::new("results").join(path);

    let file = File::open(full_path)?;
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
            let s = rodeo.get_or_intern(&triple[0]).into_usize();
            let p = rodeo.get_or_intern(&triple[1]).into_usize();
            let o = rodeo.get_or_intern(&triple[2]).into_usize();

            parsed_data.push((s, p, o));
        }
    });


    //for line_batch in &data.lines().chunks(batch_size) {
    for line_batch in &parsed_data.iter().chunks(batch_size) {
        let batch: Vec<_> = line_batch
            //.map(|line| parse_edge(line))
            .map(|(s, p, o)| (*s, *p, *o))
            .collect::<Vec<_>>();
        // Add the new batch to the integral for the next iteration
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
                result_tuples,
            ));
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
                result_tuples,
            ));
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
                result_tuples,
            ));
        }

        // Run integral benchmarks
        // if args.crepe {
        //     let (time, tuples) = run_crepe_benchmark(&integral);
        //     results.push(BenchmarkResult::new(
        //         "crepe",
        //         batch.len(),
        //         integral.len(),
        //         time,
        //         tuples,
        //     ));
        // }

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
                converted_result_tuples,
            ));
        }

        // Print progress
        println!("Processed {} edges", integral.len());
    }

    Ok(results)
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    // If visualize_results is specified, just run visualization and exit
    if let Some(results_path) = &args.visualize_results {
        println!(
            "Generating visualizations from {}...",
            results_path.display()
        );
        let results = load_benchmark_results(results_path)?;
        let vis_options = micro_datalog::visualization::VisualizationOptions {
            show_micro_streaming: true,
            show_micro_magic: true,
            show_micro_tabling: true,
            show_crepe: true,
            show_ascent: true,
            x_scale: None, // Let it be determined by the data
            y_scale_performance: Some((0.0, args.y_scale_performance)),
            y_scale_tuples: Some((0.0, args.y_scale_tuples)),
        };
        visualize_results(
            &results,
            &Path::new("visualizations"),
            &vis_options,
            results_path.file_name().unwrap().to_str().unwrap(),
        )?;
        println!("Visualizations saved to visualizations/");
        return Ok(());
    }

    // let program = program! {
    //     tc(?x, ?y) <- [e(?x, ?y)],
    //     tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
    // };

    let program = program! { T(?s, ?p, ?o) <- [RDF(?s, ?p, ?o)], T(?y, 0usize, ?x) <- [T(?a, 3usize, ?x), T(?y, ?a, ?z)], T(?z, 0usize, ?x) <- [T(?a, 4usize, ?x), T(?y, ?a, ?z)], T(?x, 2usize, ?z) <- [T(?x, 2usize, ?y), T(?y, 2usize, ?z)], T(?x, 1usize, ?z) <- [T(?x, 1usize, ?y), T(?y, 1usize, ?z)], T(?z, 0usize, ?y) <- [T(?x, 1usize, ?y), T(?z, 0usize, ?x)], T(?x, ?b, ?y) <- [T(?a, 2usize, ?b), T(?x, ?a, ?y)] };

    let mut rodeo = Rodeo::default();
    rodeo.get_or_intern(TYPE).into_usize();
    rodeo.get_or_intern(SUB_CLASS_OF);
    rodeo.get_or_intern(SUB_PROPERTY_OF);
    rodeo.get_or_intern(DOMAIN);
    rodeo.get_or_intern(RANGE);
    rodeo.get_or_intern(PROPERTY);
    //let data = include_str!("../data/facebook_combined.txt");
    let data = include_str!("../data/lubm1.nt");
    let vis_dir = Path::new("visualizations");

    //Process data based on whether we want to use all data or limited data
    // let data_to_process = if args.use_all_data {
    //     println!("Using all available data...");
    //     data.to_string()
    // } else {
    //     println!("Using first {} edges...", args.edges);
    //     data.lines().take(args.edges).collect::<Vec<_>>().join("\n")
    // };

    //Create timestamped results file
    let timestamp = Local::now().format("%Y%m%d_%H%M%S").to_string();
    let mut res_path_string = String::new();
    // match (args.query_source, args.query_target) {
    //     (None, Some(tgt)) => {
    //         res_path_string = format!("tc(_, {})_results_{}.json", tgt, timestamp);
    //     }
    //     (Some(src), None) => {
    //         res_path_string = format!("tc({}, _)_results_{}.json", src, timestamp);
    //     }
    //     (Some(src), Some(tgt)) => {
    //         res_path_string = format!("tc({}, {})_results_{}.json", src, tgt, timestamp);
    //     }
    //     (None, None) => {
    //         res_path_string = format!("tc(_, _)_results_{}.json", timestamp);
    //     }
    // }

    match (args.query_source, args.query_middle, args.query_target) {
        (None, Some(middle), Some(tgt)) => {
            res_path_string = format!("RDF(_, {}, {})_results_{}.json", middle, tgt, timestamp);
        }
        (Some(src), None, Some(tgt)) => {
            res_path_string = format!("RDF({}, _, {})_results_{}.json", src, tgt, timestamp);
        }
        
        (None, Some(middle), None) => {
            res_path_string = format!("RDF(_, {}, _)_results_{}.json", middle, timestamp);
        }
        (None, None, Some(tgt)) => {
            res_path_string = format!("RDF(_, _, {})_results_{}.json", tgt, timestamp);
        }
        (Some(src), Some(middle), None) => {
            res_path_string = format!("RDF({}, {}, _)_results_{}.json", src, middle, timestamp);
        }
        (Some(src), None, None) => {
            res_path_string = format!("RDF({}, _, _)_results_{}.json", src, timestamp);
        }
        (Some(src), Some(middle), Some(tgt)) => {
            res_path_string = format!("RDF({}, {}, {})_results_{}.json", src, middle, tgt, timestamp);
        }
        (None, None, None) => {
            res_path_string = format!("RDF(_, _)_results_{}.json", timestamp);
        }
    }
    let results_path = Path::new(&res_path_string);

    //Run benchmarks and save results
    let results = run_benchmarks(&program, &data, args.batch_size, &args)?;
    save_benchmark_results(&results, results_path)?;
    println!(
        "Benchmarks completed and saved to {}",
        results_path.display()
    );

    if !args.skip_visualization {
        // Load results and generate visualizations
        println!("Generating visualizations...");
        let results = load_benchmark_results(results_path)?;
        // Create visualization options based on selected benchmarks
        let vis_options = micro_datalog::visualization::VisualizationOptions {
            show_micro_streaming: args.micro_streaming,
            show_micro_magic: args.micro_magic,
            show_micro_tabling: args.micro_tabling,
            show_crepe: args.crepe,
            show_ascent: args.ascent,
            x_scale: None, // Set x-axis from 0 to total edges
            y_scale_performance: None,
            y_scale_tuples: None,
        };

        visualize_results(
            &results,
            vis_dir,
            &vis_options,
            results_path.file_name().unwrap().to_str().unwrap(),
        )?;
        println!("Visualizations saved to {}", vis_dir.display());
    }

    Ok(())
}
