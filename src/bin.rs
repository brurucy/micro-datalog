use ascent::ascent;
use crepe::crepe;
use datalog_rule_macro::program;
use datalog_syntax::*;
use itertools::*;
use micro_datalog::engine::datalog::MicroRuntime;
use std::time::Instant;

struct BenchmarkResult {
    strategy: String,
    batch_size: usize,
    cumulative_edges: usize,
    execution_time_micros: u128,
    inferred_tuples: usize,
}

//TC benchmark
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

fn main() {
    let program = program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
    };

    let mut streaming_micro = MicroRuntime::new(program.clone());
    let mut streaming_micro_magic = MicroRuntime::new(program.clone());
    let mut streaming_micro_tabling = MicroRuntime::new(program.clone());

    // Exponentially decreasing some value
    let batch_size = 10;
    let data = include_str!("../data/soc-Epinions1.txt");
    let mut integral = vec![];
    data.lines()
        .into_iter()
        .chunks(batch_size)
        .into_iter()
        .for_each(|line_batch| {
            for line in line_batch {
                let triple: Vec<_> = line.split("	").collect();
                let from: usize = triple[0].parse().unwrap();
                let to: usize = triple[1].parse().unwrap();

                streaming_micro.insert("e", (from, to));
                integral.push((from, to));
            }

            let now = Instant::now();
            streaming_micro.poll();
            println!("micro - streaming: {} milis", now.elapsed().as_micros());
            let q = build_query!(tc(_, _));
            let streaming_micro_runtime_answer: Vec<_> =
                streaming_micro.query(&q).into_iter().collect();
            println!("inferred tuples: {}", streaming_micro_runtime_answer.len());

            let program_tabling = program.clone();
            println!(
                "micro - streaming magic sets: {} milis",
                now.elapsed().as_micros()
            );
            let q = build_query!(tc(_, _));
            let streaming_micro_runtime_answer: Vec<_> = streaming_micro_magic
                .query_program(
                    &q,
                    program_tabling,
                    &micro_datalog::engine::datalog::Strategy::BottomUp,
                )
                .into_iter()
                .collect();
            println!("inferred tuples: {}", streaming_micro_runtime_answer.len());

            println!(
                "micro - streaming top down: {} milis",
                now.elapsed().as_micros()
            );
            let q = build_query!(tc(_, _));
            let program_magic = program.clone();
            let streaming_micro_runtime_answer: Vec<_> = streaming_micro_tabling
                .query_program(
                    &q,
                    program_magic,
                    &micro_datalog::engine::datalog::Strategy::TopDown,
                )
                .into_iter()
                .collect();
            println!("inferred tuples: {}", streaming_micro_runtime_answer.len());

            let mut micro_runtime = MicroRuntime::new(program.clone());
            for line in &integral {
                micro_runtime.insert("e", (line.0.clone(), line.1.clone()));
            }
            let now = Instant::now();
            micro_runtime.poll();
            println!("micro - stupid: {} milis", now.elapsed().as_micros());
            let q = build_query!(tc(_, _));
            let micro_runtime_answer: Vec<_> = micro_runtime.query(&q).into_iter().collect();
            println!("inferred tuples: {}", micro_runtime_answer.len());

            let mut crepe_runtime = Crepe::new();
            for line in &integral {
                crepe_runtime.e.push(E(line.0.clone(), line.1.clone()));
            }
            let now = Instant::now();
            let teecee = crepe_runtime.run();
            println!("crepe: {} milis", now.elapsed().as_micros());
            let crepe_answer: Vec<_> = teecee.0.iter().collect();
            println!("inferred tuples: {}", crepe_answer.len());

            let mut ascnt_runtime = AscentProgram::default();
            for line in &integral {
                ascnt_runtime.e.push((line.0.clone(), line.1.clone()))
            }
            let now = Instant::now();
            ascnt_runtime.run();
            println!("ascent: {} milis", now.elapsed().as_micros());
            let ascent_answer: Vec<_> = ascnt_runtime.tc.iter().collect();
            println!("inferred tuples: {}", ascent_answer.len());
        });
}

