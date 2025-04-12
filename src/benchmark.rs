use serde::{Serialize, Deserialize};
use std::time::Duration;

#[derive(Debug, Serialize, Deserialize)]
pub struct BenchmarkResult {
    pub strategy: String,
    pub batch_size: usize,
    pub cumulative_edges: usize,
    pub execution_time_micros: u128,
    pub inferred_tuples: usize,
}

impl BenchmarkResult {
    pub fn new(strategy: &str, batch_size: usize, edges: usize, time: Duration, tuples: usize) -> Self {
        Self {
            strategy: strategy.to_string(),
            batch_size,
            cumulative_edges: edges,
            execution_time_micros: time.as_micros(),
            inferred_tuples: tuples,
        }
    }
} 