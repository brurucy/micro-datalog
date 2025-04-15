use chrono::Local;
use plotters::prelude::*;
use plotters::coord::types::RangedCoordf64;
use std::error::Error;
use std::path::Path;
use std::ops::Range;
use crate::benchmark::BenchmarkResult;

pub struct VisualizationOptions {
    pub show_micro_streaming: bool,
    pub show_micro_magic: bool,
    pub show_micro_tabling: bool,
    pub show_crepe: bool,
    pub show_ascent: bool,
    pub x_scale: Option<(f64, f64)>,
    pub y_scale_performance: Option<(f64, f64)>,
    pub y_scale_tuples: Option<(f64, f64)>,
}

fn create_performance_plot(
    results: &[BenchmarkResult],
    vis_dir: &Path,
    options: &VisualizationOptions,
    timestamp: &str,
) -> Result<(), Box<dyn Error>> {
    let path = vis_dir.join(format!("performance_{}.png", timestamp));
    let root = BitMapBackend::new(&path, (1024, 768)).into_drawing_area();
    root.fill(&WHITE)?;

    let max_edges = results.iter().map(|r| r.cumulative_edges as f64).max_by(|a, b| a.partial_cmp(b).unwrap()).unwrap_or(0.0);
    let max_time = results.iter().map(|r| r.execution_time_micros as f64 / 1000.0).max_by(|a, b| a.partial_cmp(b).unwrap()).unwrap_or(0.0);

    let x_scale = options.x_scale.unwrap_or((0.0, max_edges));
    let y_scale = options.y_scale_performance.unwrap_or((0.0, max_time));

    let mut chart = ChartBuilder::on(&root)
        .caption("Performance Comparison", ("sans-serif", 50).into_font())
        .margin(5)
        .x_label_area_size(30)
        .y_label_area_size(30)
        .build_cartesian_2d(
            RangedCoordf64::from(Range { start: x_scale.0, end: x_scale.1 }),
            RangedCoordf64::from(Range { start: y_scale.0, end: y_scale.1 }),
        )?;

    chart.configure_mesh().draw()?;

    let mut strategies = vec![];
    if options.show_micro_streaming {
        strategies.push("micro-streaming");
    }
    if options.show_micro_magic {
        strategies.push("micro-magic");
    }
    if options.show_micro_tabling {
        strategies.push("micro-tabling");
    }
    if options.show_crepe {
        strategies.push("crepe");
    }
    if options.show_ascent {
        strategies.push("ascent");
    }

    for (i, strategy) in strategies.iter().enumerate() {
        let strategy_results: Vec<_> = results
            .iter()
            .filter(|r| r.strategy == *strategy)
            .collect();

        if !strategy_results.is_empty() {
            let color = Palette99::pick(i);
            chart
                .draw_series(LineSeries::new(
                    strategy_results.iter().map(|r| {
                        (r.cumulative_edges as f64, r.execution_time_micros as f64 / 1000.0)
                    }),
                    &color,
                ))?
                .label(*strategy)
                .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], &color));
        }
    }

    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .draw()?;

    Ok(())
}

fn create_tuples_plot(
    results: &[BenchmarkResult],
    vis_dir: &Path,
    options: &VisualizationOptions,
    timestamp: &str,
) -> Result<(), Box<dyn Error>> {
    let path = vis_dir.join(format!("tuples_{}.png", timestamp));
    let root = BitMapBackend::new(&path, (1024, 768)).into_drawing_area();
    root.fill(&WHITE)?;

    let max_edges = results.iter().map(|r| r.cumulative_edges as f64).max_by(|a, b| a.partial_cmp(b).unwrap()).unwrap_or(0.0);
    let max_tuples = results.iter().map(|r| r.inferred_tuples as f64).max_by(|a, b| a.partial_cmp(b).unwrap()).unwrap_or(0.0);

    let x_scale = options.x_scale.unwrap_or((0.0, max_edges));
    let y_scale = options.y_scale_tuples.unwrap_or((0.0, max_tuples));

    let mut chart = ChartBuilder::on(&root)
        .caption("Inferred Tuples Comparison", ("sans-serif", 50).into_font())
        .margin(5)
        .x_label_area_size(30)
        .y_label_area_size(30)
        .build_cartesian_2d(
            RangedCoordf64::from(Range { start: x_scale.0, end: x_scale.1 }),
            RangedCoordf64::from(Range { start: y_scale.0, end: y_scale.1 }),
        )?;

    chart.configure_mesh().draw()?;

    let mut strategies = vec![];
    if options.show_micro_streaming {
        strategies.push("micro-streaming");
    }
    if options.show_micro_magic {
        strategies.push("micro-magic");
    }
    if options.show_micro_tabling {
        strategies.push("micro-tabling");
    }
    if options.show_crepe {
        strategies.push("crepe");
    }
    if options.show_ascent {
        strategies.push("ascent");
    }

    for (i, strategy) in strategies.iter().enumerate() {
        let strategy_results: Vec<_> = results
            .iter()
            .filter(|r| r.strategy == *strategy)
            .collect();

        if !strategy_results.is_empty() {
            let color = Palette99::pick(i);
            chart
                .draw_series(LineSeries::new(
                    strategy_results.iter().map(|r| {
                        (r.cumulative_edges as f64, r.inferred_tuples as f64)
                    }),
                    &color,
                ))?
                .label(*strategy)
                .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], &color));
        }
    }

    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .draw()?;

    Ok(())
}

pub fn visualize_results(
    results: &[BenchmarkResult],
    vis_dir: &Path,
    options: &VisualizationOptions,
) -> Result<(), Box<dyn Error>> {
    // Create visualization directory if it doesn't exist
    std::fs::create_dir_all(vis_dir)?;

    // Generate timestamp for the visualization files
    let timestamp = Local::now().format("%Y%m%d_%H%M%S").to_string();

    // Create performance plot
    create_performance_plot(results, vis_dir, options, &timestamp)?;

    // Create tuples plot
    //create_tuples_plot(results, vis_dir, options, &timestamp)?;

    Ok(())
} 