use plotters::prelude::*;
use std::error::Error;
use std::path::Path;
use crate::benchmark::BenchmarkResult;

pub fn create_performance_plot(
    results: &[BenchmarkResult],
    output_path: &Path,
) -> Result<(), Box<dyn Error>> {
    let root = BitMapBackend::new(output_path, (1024, 768)).into_drawing_area();
    root.fill(&WHITE)?;

    let max_edges = results
        .iter()
        .map(|r| r.cumulative_edges as f64)
        .max_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
        .unwrap_or(0.0);

    let max_time = results
        .iter()
        .map(|r| r.execution_time_micros as f64)
        .max_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
        .unwrap_or(0.0);

    let mut chart = ChartBuilder::on(&root)
        .caption("Performance Comparison", ("sans-serif", 50).into_font())
        .margin(10)
        .x_label_area_size(30)
        .y_label_area_size(50)
        .build_cartesian_2d(0f64..max_edges, 0f64..max_time)?;

    chart
        .configure_mesh()
        .x_desc("Cumulative Edges")
        .y_desc("Execution Time (μs)")
        .draw()?;

    let strategies: Vec<_> = results.iter().map(|r| r.strategy.clone()).collect();
    const COLORS: [&RGBColor; 6] = [&RED, &BLUE, &GREEN, &MAGENTA, &CYAN, &BLACK];

    for (strategy, color) in strategies.iter().zip(COLORS.iter()) {
        let data: Vec<_> = results
            .iter()
            .filter(|r| r.strategy == *strategy)
            .map(|r| (r.cumulative_edges as f64, r.execution_time_micros as f64))
            .collect();

        let color_clone = color.clone();
        chart
            .draw_series(LineSeries::new(data, color))?
            .label(strategy)
            .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color_clone));
    }

    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .draw()?;

    Ok(())
}

pub fn create_tuples_plot(
    results: &[BenchmarkResult],
    output_path: &Path,
) -> Result<(), Box<dyn Error>> {
    let root = BitMapBackend::new(output_path, (1024, 768)).into_drawing_area();
    root.fill(&WHITE)?;

    let max_edges = results
        .iter()
        .map(|r| r.cumulative_edges as f64)
        .max_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
        .unwrap_or(0.0);

    let max_tuples = results
        .iter()
        .map(|r| r.inferred_tuples as f64)
        .max_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
        .unwrap_or(0.0);

    let mut chart = ChartBuilder::on(&root)
        .caption("Inferred Tuples Comparison", ("sans-serif", 50).into_font())
        .margin(10)
        .x_label_area_size(30)
        .y_label_area_size(50)
        .build_cartesian_2d(0f64..max_edges, 0f64..max_tuples)?;

    chart
        .configure_mesh()
        .x_desc("Cumulative Edges")
        .y_desc("Inferred Tuples")
        .draw()?;

    let strategies: Vec<_> = results.iter().map(|r| r.strategy.clone()).collect();
    const COLORS: [&RGBColor; 6] = [&RED, &BLUE, &GREEN, &MAGENTA, &CYAN, &BLACK];

    for (strategy, color) in strategies.iter().zip(COLORS.iter()) {
        let data: Vec<_> = results
            .iter()
            .filter(|r| r.strategy == *strategy)
            .map(|r| (r.cumulative_edges as f64, r.inferred_tuples as f64))
            .collect();

        let color_clone = color.clone();
        chart
            .draw_series(LineSeries::new(data, color))?
            .label(strategy)
            .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color_clone));
    }

    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .draw()?;

    Ok(())
}

pub fn visualize_results(results: &[BenchmarkResult], vis_dir: &Path) -> Result<(), Box<dyn Error>> {
    // Create visualization directory if it doesn't exist
    if !vis_dir.exists() {
        std::fs::create_dir(vis_dir)?;
    }

    // Generate performance plot
    create_performance_plot(
        results,
        &vis_dir.join("performance_comparison.png"),
    )?;

    // Generate tuples plot
    create_tuples_plot(
        results,
        &vis_dir.join("tuples_comparison.png"),
    )?;

    Ok(())
} 