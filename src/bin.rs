use ascent::ascent;
use chrono::Local;
use clap::Parser;
use micro_datalog::args::Args;
use micro_datalog::benchmark::BenchmarkResult;
use micro_datalog::benchmark_rdf::run_benchmarks_rdf;
use micro_datalog::benchmark_tc::run_benchmarks_tc;
use micro_datalog::benchmark_university::run_benchmarks_university;
use micro_datalog::benchmark_university_all::run_benchmarks_university_all;
use micro_datalog::visualization::visualize_results;
use std::error::Error;
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;
use std::path::PathBuf;

fn save_benchmark_results(results: &[BenchmarkResult], path: &Path, args: &Args) -> Result<(), Box<dyn Error>> {
    // Create results directory if it doesn't exist
 
    let full_path = if args.university_all {
        std::fs::create_dir_all("results/university_all")?;
        Path::new("results/university_all").join(path)
    } else if args.rdf {
        std::fs::create_dir_all("results/rdf")?;
        Path::new("results/rdf").join(path)
    } else if args.tc {
        std::fs::create_dir_all("results/tc")?;
        Path::new("results/tc").join(path)
    } else if args.university {
        std::fs::create_dir_all("results/university")?;
        Path::new("results/university").join(path)
    } else {
        Path::new("results").join(path)
    };

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

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    //If visualize_results is specified, just run visualization and exit
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

    let vis_dir = Path::new("visualizations");

    //Create timestamped results file
    let timestamp = Local::now().format("%Y%m%d_%H%M%S").to_string();
    let mut res_path_string = String::new();
    let mut results = Vec::new();
    let mut results_path: PathBuf = PathBuf::new();

    if args.rdf {
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
                res_path_string = format!(
                    "RDF({}, {}, {})_results_{}.json",
                    src, middle, tgt, timestamp
                );
            }
            (None, None, None) => {
                res_path_string = format!("RDF(_, _, _)_results_{}.json", timestamp);
            }
        }
        results_path = PathBuf::from(&res_path_string);

        //Run benchmarks and save results
        results = run_benchmarks_rdf(args.batch_size, &args)?;
    } else if args.tc {
        match (args.query_source, args.query_target) {
            (None, Some(tgt)) => {
                res_path_string = format!("tc(_, {})_results_{}.json", tgt, timestamp);
            }
            (Some(src), None) => {
                res_path_string = format!("tc({}, _)_results_{}.json", src, timestamp);
            }
            (Some(src), Some(tgt)) => {
                res_path_string = format!("tc({}, {})_results_{}.json", src, tgt, timestamp);
            }
            (None, None) => {
                res_path_string = format!("tc(_, _)_results_{}.json", timestamp);
            }
        }
        results_path = PathBuf::from(&res_path_string);
        results = run_benchmarks_tc(args.batch_size, &args)?;
    } else if args.university {
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
                res_path_string = format!(
                    "RDF({}, {}, {})_results_{}.json",
                    src, middle, tgt, timestamp
                );
            }
            (None, None, None) => {
                res_path_string = format!("RDF(_, _, _)_results_{}.json", timestamp);
            }
        }
        results_path = PathBuf::from(&res_path_string);
        results = run_benchmarks_university(&args)?;
    } else if args.university_all {
       
        res_path_string = format!("Uni T(_, _, _)_results_{}.json", timestamp);
        
        results_path = PathBuf::from(&res_path_string);
        results = run_benchmarks_university_all(&args)?;
    }

    save_benchmark_results(&results, &results_path, &args)?;
    println!(
        "Benchmarks completed and saved to {}",
        results_path.display()
    );

    if !args.skip_visualization {
        // Load results and generate visualizations
        println!("Generating visualizations...");
        let results = load_benchmark_results(&results_path)?;
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
