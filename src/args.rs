use clap::Parser;
use std::path::PathBuf;

/// Command line arguments for the benchmark tool
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Number of edges to process
    #[arg(short, long, default_value_t = 20000)]
    pub edges: usize,

    /// Batch size for processing edges
    #[arg(short, long, default_value_t = 1000)]
    pub batch_size: usize,

    /// Use all available data instead of limiting to specified number of edges
    #[arg(long)]
    pub use_all_data: bool,

    /// Do not use batching
    #[arg(long)]
    pub no_batching: bool,

    /// Source node for the query
    #[arg(long)]
    pub query_source: Option<usize>,

    /// Source node for the query
    #[arg(long)]
    pub query_source_str: Option<String>,

    /// Target node for the query
    #[arg(long)]
    pub query_target_str: Option<String>,

    /// Target node for the query
    #[arg(long)]
    pub query_target: Option<usize>,

    /// Middle node for the query
    #[arg(long)]
    pub query_middle: Option<usize>,

    /// Query predicate
    #[arg(long)]
    pub query_predicate: Option<String>,

    /// Run micro streaming benchmark
    #[arg(long)]
    pub micro_streaming: bool,

    /// Run micro magic benchmark
    #[arg(long)]
    pub micro_magic: bool,

    /// Run micro tabling benchmark
    #[arg(long)]
    pub micro_tabling: bool,

    /// Run crepe benchmark
    #[arg(long)]
    pub crepe: bool,

    /// Run ascent benchmark
    #[arg(long)]
    pub ascent: bool,

    /// Skip visualization
    #[arg(long)]
    pub skip_visualization: bool,

    /// Path to results JSON file for visualization
    #[arg(long)]
    pub visualize_results: Option<PathBuf>,

    /// Maximum value for performance y-axis in visualization
    #[arg(long, default_value_t = 3000.0)]
    pub y_scale_performance: f64,

    /// Maximum value for tuples y-axis in visualization
    #[arg(long, default_value_t = 509000.0)]
    pub y_scale_tuples: f64,

    /// Run rdf benchmark
    #[arg(long)]
    pub rdf: bool,

    /// Run tc benchmark
    #[arg(long)]
    pub tc: bool,

    /// Run university benchmark
    #[arg(long)]
    pub university: bool,

    /// Run university all benchmark
    #[arg(long)]
    pub university_all: bool,

    /// Arity of the query
    #[arg(long, default_value_t = 2)]
    pub arity: usize,

    /// Use facebook data
    #[arg(long)]
    pub fb: bool,

    /// Use dense data
    #[arg(long)]
    pub dense: bool,

    /// Use sparse data
    #[arg(long)]
    pub sparse: bool,
} 