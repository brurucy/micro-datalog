use ascent::ascent;
use crepe::crepe;
use datalog_rule_macro::program;
use datalog_syntax::*;
use micro_datalog::engine::datalog::MicroRuntime;
use std::time::Instant;

// TC benchmark
crepe! {
    @input
    struct e(usize, usize);

    @output
    struct tc(usize, usize);

    tc(x, y) <- e(x, y);
    tc(x, z) <- e(x, y), tc(y, z);
}

ascent! {
    relation e(usize, usize);
    relation tc(usize, usize);

    tc(x, y) <-- e(x, y);
    tc(x, z) <-- e(x, y), tc(y, z);
}

fn main() {
    let program =
        program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
    };

    let mut micro_runtime = MicroRuntime::new(program.clone());
    let mut ascnt_runtime = AscentProgram::default();
    let mut crepe_runtime = Crepe::new();

    let data = include_str!("../data/graph_dense.txt");
    for line in data.lines() {
        let triple: Vec<_> = line.split(" ").collect();
        let from: usize = triple[0].parse().unwrap();
        let to: usize = triple[1].parse().unwrap();

        micro_runtime.insert("e", vec![from.into(), to.into()]);
        crepe_runtime.e.push(e(from, to));
        ascnt_runtime.e.push((from, to));
    }
    let now = Instant::now();
    micro_runtime.poll();
    let q = build_query!(tc(_, _));
    let q_temp = build_query!(tc_ff(_, _));
    let result = micro_runtime.query_program(&q, &q, program, "Top-down");
    println!("micro: {} milis", now.elapsed().as_millis());
    let answer: Vec<_> = result.unwrap().into_iter().collect();
    println!("inferred tuples: {}", answer.len());

    let now = Instant::now();
    let teecee = crepe_runtime.run();
    println!("crepe: {} milis", now.elapsed().as_millis());
    println!("inferred tuples: {}", teecee.0.len());

    let now = Instant::now();
    ascnt_runtime.run();
    println!("ascent: {} milis", now.elapsed().as_millis());
    println!("inferred tuples: {}", ascnt_runtime.tc.len());
}
