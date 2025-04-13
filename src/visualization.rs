use plotters::prelude::*;
use std::error::Error;
use std::path::Path;
use crate::benchmark::BenchmarkResult;

#[derive(Default)]
pub struct VisualizationOptions {
    pub show_micro_streaming: bool,
    pub show_micro_magic: bool,
    pub show_micro_tabling: bool,
    pub show_crepe: bool,
    pub show_ascent: bool,
    pub x_scale: Option<(f64, f64)>,  // (min, max) for x-axis
    pub y_scale_performance: Option<(f64, f64)>,  // (min, max) for y-axis in performance plot
    pub y_scale_tuples: Option<(f64, f64)>,  // (min, max) for y-axis in tuples plot
}

impl VisualizationOptions {
    pub fn all() -> Self {
        Self {
            show_micro_streaming: true,
            show_micro_magic: true,
            show_micro_tabling: true,
            show_crepe: true,
            show_ascent: true,
            x_scale: None,
            y_scale_performance: None,
            y_scale_tuples: None,
        }
    }
}

fn create_performance_plot(
    results: &[BenchmarkResult],
    options: &VisualizationOptions,
    path: &Path,
) -> Result<(), Box<dyn Error>> {
    let root = BitMapBackend::new(path, (1024, 768)).into_drawing_area();
    root.fill(&WHITE)?;

    // Find the maximum execution time and number of edges
    let max_time = results
        .iter()
        .filter(|r| match r.strategy.as_str() {
            "micro-streaming" => options.show_micro_streaming,
            "micro-magic" => options.show_micro_magic,
            "micro-tabling" => options.show_micro_tabling,
            "crepe" => options.show_crepe,
            "ascent" => options.show_ascent,
            _ => false,
        })
        .map(|r| r.execution_time_micros as f64 / 1000.0)
        .fold(0.0, f64::max);

    let max_edges = results
        .iter()
        .map(|r| r.cumulative_edges as f64)
        .fold(0.0, f64::max);

    // Use custom scales if provided, otherwise use computed values
    let x_range = options.x_scale.unwrap_or((0.0, max_edges));
    let y_range = options.y_scale_performance.unwrap_or((0.0, max_time));

    let mut chart = ChartBuilder::on(&root)
        .caption("Performance Comparison", ("sans-serif", 50).into_font())
        .margin(5)
        .x_label_area_size(30)
        .y_label_area_size(30)
        .build_cartesian_2d(x_range.0..x_range.1, y_range.0..y_range.1)?;

    let x_desc: String = String::from("Number of Edges");
    let y_desc: String = String::from("Execution Time (ms)");

    chart
        .configure_mesh()
        .x_desc(x_desc)
        .y_desc(y_desc)
        .draw()?;

    // Define colors for each strategy
    const COLORS: [RGBColor; 5] = [
        RGBColor(255, 0, 0),    // micro-streaming
        RGBColor(0, 255, 0),    // micro-magic
        RGBColor(0, 0, 255),    // micro-tabling
        RGBColor(255, 165, 0),  // crepe
        RGBColor(128, 0, 128),  // ascent
    ];

    let strategies = [
        ("micro-streaming", options.show_micro_streaming),
        ("micro-magic", options.show_micro_magic),
        ("micro-tabling", options.show_micro_tabling),
        ("crepe", options.show_crepe),
        ("ascent", options.show_ascent),
    ];

    for (i, (strategy, should_show)) in strategies.iter().enumerate() {
        if !should_show {
            continue;
        }

        let color = COLORS[i];
        let color_clone = color.clone();

        let strategy_results: Vec<_> = results
            .iter()
            .filter(|r| r.strategy == *strategy)
            .collect();

        if !strategy_results.is_empty() {
            chart
                .draw_series(LineSeries::new(
                    strategy_results.iter().map(|r| {
                        (r.cumulative_edges as f64, r.execution_time_micros as f64 / 1000.0)
                    }),
                    &color,
                ))?
                .label(*strategy)
                .legend(move |(x, y)| {
                    Rectangle::new([(x, y - 5), (x + 20, y + 5)], color_clone.filled())
                });
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
    options: &VisualizationOptions,
    path: &Path,
) -> Result<(), Box<dyn Error>> {
    let root = BitMapBackend::new(path, (1024, 768)).into_drawing_area();
    root.fill(&WHITE)?;

    // Find the maximum number of tuples and edges
    let max_tuples = results
        .iter()
        .filter(|r| match r.strategy.as_str() {
            "micro-streaming" => options.show_micro_streaming,
            "micro-magic" => options.show_micro_magic,
            "micro-tabling" => options.show_micro_tabling,
            "crepe" => options.show_crepe,
            "ascent" => options.show_ascent,
            _ => false,
        })
        .map(|r| r.inferred_tuples as f64)
        .fold(0.0, f64::max);

    let max_edges = results
        .iter()
        .map(|r| r.cumulative_edges as f64)
        .fold(0.0, f64::max);

    // Use custom scales if provided, otherwise use computed values
    let x_range = options.x_scale.unwrap_or((0.0, max_edges));
    let y_range = options.y_scale_tuples.unwrap_or((0.0, max_tuples));

    let mut chart = ChartBuilder::on(&root)
        .caption("Inferred Tuples Comparison", ("sans-serif", 50).into_font())
        .margin(5)
        .x_label_area_size(30)
        .y_label_area_size(30)
        .build_cartesian_2d(x_range.0..x_range.1, y_range.0..y_range.1)?;

    let x_desc: String = String::from("Number of Edges");
    let y_desc: String = String::from("Number of Inferred Tuples");

    chart
        .configure_mesh()
        .x_desc(x_desc)
        .y_desc(y_desc)
        .draw()?;

    // Define colors for each strategy
    const COLORS: [RGBColor; 5] = [
        RGBColor(255, 0, 0),    // micro-streaming
        RGBColor(0, 255, 0),    // micro-magic
        RGBColor(0, 0, 255),    // micro-tabling
        RGBColor(255, 165, 0),  // crepe
        RGBColor(128, 0, 128),  // ascent
    ];

    let strategies = [
        ("micro-streaming", options.show_micro_streaming),
        ("micro-magic", options.show_micro_magic),
        ("micro-tabling", options.show_micro_tabling),
        ("crepe", options.show_crepe),
        ("ascent", options.show_ascent),
    ];

    for (i, (strategy, should_show)) in strategies.iter().enumerate() {
        if !should_show {
            continue;
        }

        let color = COLORS[i];
        let color_clone = color.clone();

        let strategy_results: Vec<_> = results
            .iter()
            .filter(|r| r.strategy == *strategy)
            .collect();

        if !strategy_results.is_empty() {
            chart
                .draw_series(LineSeries::new(
                    strategy_results.iter().map(|r| {
                        (r.cumulative_edges as f64, r.inferred_tuples as f64)
                    }),
                    &color,
                ))?
                .label(*strategy)
                .legend(move |(x, y)| {
                    Rectangle::new([(x, y - 5), (x + 20, y + 5)], color_clone.filled())
                });
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
    std::fs::create_dir_all(vis_dir)?;

    let performance_path = vis_dir.join("performance.png");
    let tuples_path = vis_dir.join("tuples.png");

    create_performance_plot(results, options, &performance_path)?;
    //create_tuples_plot(results, options, &tuples_path)?;

    Ok(())
} 