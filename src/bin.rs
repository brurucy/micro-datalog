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
    let program = program! {
        ancestor(?x, ?y) <- [person(?x), parent(?x, ?y)],
        ancestor(?x, ?z) <- [person(?x), parent(?x, ?y), ancestor(?y, ?z)]
    };

    let mut micro_runtime = MicroRuntime::new(program);

    micro_runtime.insert("parent", vec!["john".into(), "bob".into()]);
    micro_runtime.insert("parent", vec!["bob".into(), "mary".into()]);
    micro_runtime.insert("person", vec!["john".into()]);
    micro_runtime.insert("person", vec!["bob".into()]);
    micro_runtime.insert("person", vec!["mary".into()]);

    micro_runtime.poll();
    let q = build_query!(ancestor(_, _));
    let answer: Vec<_> = micro_runtime.query(&q).unwrap().into_iter().collect();
    println!("{:?}", answer);
}
/*
crepe! {
    @input
    struct RDF(usize, usize, usize);

    @output
    struct T(usize, usize, usize);

    T(s, p, o) <- RDF(s, p, o);
    T(y, 0, x) <- T(a, 3, x), T(y, a, z);
    T(z, 0, x) <- T(a, 4, x), T(y, a, z);
    T(x, 2, z) <- T(x, 2, y), T(y, 2, z);
    T(x, 1, z) <- T(x, 1, y), T(y, 1, z);
    T(z, 0, y) <- T(x, 1, y), T(z, 0, x);
    T(x, b, y) <- T(a, 2, b), T(x, a, y);
}

ascent! {
    relation RDF(usize, usize, usize);
    relation T(usize, usize, usize);

    T(s, p, o) <-- RDF(s, p, o);
    T(y, 0, x) <-- T(a, 3, x), T(y, a, z);
    T(z, 0, x) <-- T(a, 4, x), T(y, a, z);
    T(x, 2, z) <-- T(x, 2, y), T(y, 2, z);
    T(x, 1, z) <-- T(x, 1, y), T(y, 1, z);
    T(z, 0, y) <-- T(x, 1, y), T(z, 0, x);
    T(x, b, y) <-- T(a, 2, b), T(x, a, y);
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

fn main() {
    let program = program! {
        T(?s, ?p, ?o) <- [RDF(?s, ?p, ?o)],
        T(?y, 0, ?x) <- [T(?a, 3, ?x), T(?y, ?a, ?z)],
        T(?z, 0, ?x) <- [T(?a, 4, ?x), T(?y, ?a, ?z)],
        T(?x, 2, ?z) <- [T(?x, 2, ?y), T(?y, 2, ?z)],
        T(?x, 1, ?z) <- [T(?x, 1, ?y), T(?y, 1, ?z)],
        T(?z, 0, ?y) <- [T(?x, 1, ?y), T(?z, 0, ?x)],
        T(?x, ?b, ?y) <- [T(?a, 2, ?b), T(?x, ?a, ?y)]
    };

    let mut rodeo = Rodeo::default();
    rodeo.get_or_intern(TYPE).into_usize();
    rodeo.get_or_intern(SUB_CLASS_OF);
    rodeo.get_or_intern(SUB_PROPERTY_OF);
    rodeo.get_or_intern(DOMAIN);
    rodeo.get_or_intern(RANGE);
    rodeo.get_or_intern(PROPERTY);

    let mut micro_runtime = MicroRuntime::new(program);
    let mut ascnt_runtime = AscentProgram::default();
    let mut crepe_runtime = Crepe::new();

    let data = include_str!("../data/lubm1.nt");
    data.lines().into_iter().for_each(|line| {
        if !line.contains("genid") {
            let triple: Vec<_> = line
                .split_whitespace()
                .map(|resource| resource.trim())
                .collect();
            let s = rodeo.get_or_intern_static(triple[0]).into_usize();
            let p = rodeo.get_or_intern_static(triple[1]).into_usize();
            let o = rodeo.get_or_intern_static(triple[2]).into_usize();

            micro_runtime.insert("RDF", vec![s.into(), p.into(), o.into()]);
            crepe_runtime.rdf.push(RDF(s, p, o));
            ascnt_runtime.RDF.push((s, p, o));
        }
    });

    let now = Instant::now();
    micro_runtime.poll();
    println!("micro: {} milis", now.elapsed().as_millis());
    let q = build_query!(T(_, _, _));
    let answer: Vec<_> = micro_runtime.query(&q).unwrap().into_iter().collect();
    println!("inferred tuples: {}", answer.len());

    let now = Instant::now();
    let crepe_out = crepe_runtime.run();
    println!("crepe: {} milis", now.elapsed().as_millis());
    println!("inferred tuples: {}", crepe_out.0.len());

    let now = Instant::now();
    ascnt_runtime.run();
    println!("ascent: {} milis", now.elapsed().as_millis());
    println!("inferred tuples: {}", ascnt_runtime.T.len());
}
*/
