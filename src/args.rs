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

    /// Source node for the query
    #[arg(long)]
    pub query_source: Option<usize>,

    /// Target node for the query
    #[arg(long)]
    pub query_target: Option<usize>,

    /// Middle node for the query
    #[arg(long)]
    pub query_middle: Option<usize>,

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

    /// Run lubm1lla benchmark
    #[arg(long)]
    pub lubm1lla: bool,

    /// Run facebook benchmark
    #[arg(long)]
    pub facebook: bool,

    /// Do not use batching for lubm1lla
    #[arg(long)]
    pub bigchunky: bool,
} 