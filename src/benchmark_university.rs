use crate::args::Args;
use crate::benchmark::BenchmarkResult;
use crate::engine::datalog::{MicroRuntime, Strategy};
use crate::helpers::parser::parse_data;
use ascent::ascent;
use datalog_rule_macro::program;
use datalog_syntax::*;
use itertools::*;
use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::time::{Duration, Instant};

ascent! {
    relation RDF(usize, usize, usize);
    relation T(usize, usize, usize);

    T(s, p, o) <-- RDF(s, p, o);
    T(y, 0usize, x) <-- T(a, 3usize, x), T(y, a, z);
    T(z, 0usize, x) <-- T(a, 4usize, x), T(y, a, z);
    T(x, 2usize, z) <-- T(x, 2usize, y), T(y, 2usize, z);
    T(x, 1usize, z) <-- T(x, 1usize, y), T(y, 1usize, z);
    T(z, 0usize, y) <-- T(x, 1usize, y), T(z, 0usize, x);
    T(x, b, y) <-- T(a, 2usize, b), T(x, a, y);

    T(x, 0usize, 119usize) <-- T(x, 0usize, 100usize), T(x, 213usize, y), T(y, 0usize, 129usize);

    T(x, 0usize, 110usize) <-- T(x, 0usize, 100usize), T(x, 207usize, y), T(y, 0usize, 124usize);

    T(x, 0usize, 112usize) <--
        T(x, 0usize, 100usize),
        T(x, 207usize, y),
        T(y, 0usize, 126usize)
    ;

    T(x, 0usize, 111usize) <--
        T(x, 207usize, y),
        T(y, 0usize, 123usize)
    ;

    T(x, 0usize, 101usize) <--
        T(x, 0usize, 100usize),
        T(x, 206usize, y),
        T(y, 0usize, 121usize)
    ;

    // T(x, 0usize, 116usize) <--
    //     T(x, 0usize,100usize),
    //     T(x, 215usize, y),
    //     T(y, 0usize, 129usize)
    // ;

    // T(x, 204usize, y) <-- T(y, 205usize, x);
    // T(x, 205usize, y) <-- T(y, 204usize, x);


    // T(x, 209usize, y) <-- T(y, 208usize, x);
    // T(y, 208usize, x) <-- T(x, 209usize, y);

    // T(x, 212usize, z) <-- T(x, 212usize, y), T(y, 212usize, z);
}

fn save_parsed_data_to_file(parsed_data: &[(String, String, String)], filename: &str) -> Result<(), Box<dyn Error>> {
    let mut file = File::create(filename)?;
    for (s, p, o) in parsed_data {
        writeln!(file, "{} {} {}", s, p, o)?;
    }
    println!("Parsed data saved to {}", filename);
    Ok(())
}
// fn run_ascent_benchmark(
//     runtime: &mut AscentProgram,
//     edges: &[(String, String, String)],
//     query: Query,
// ) -> (Duration, usize, Vec<(usize, usize, usize)>) {
//     for &(x, y, z) in edges {
//         runtime.RDF.push((x, y, z));
//     }

//     let start = Instant::now();
//     runtime.run();
//     let elapsed_time = start.elapsed();
//     // Query tuples based on source and target
//     let results: Vec<_> = runtime
//         .T
//         .iter()
//         .cloned()
//         .filter(
//             |&(x, y, z)| match (query_source, query_middle, query_target) {
//                 (Some(src), Some(middle), Some(tgt)) => x == src && z == tgt && y == middle,
//                 (Some(src), None, Some(tgt)) => x == src && z == tgt,
//                 (None, Some(middle), Some(tgt)) => y == middle && z == tgt,
//                 (Some(src), None, None) => x == src,
//                 (None, Some(middle), None) => y == middle,
//                 (None, None, Some(tgt)) => z == tgt,
//                 (Some(src), Some(middle), None) => x == src && y == middle,
//                 (None, None, None) => true,
//             },
//         )
//         .collect();
//     (elapsed_time, results.len(), results)
// }

fn run_micro_benchmark(
    runtime: &mut MicroRuntime,
    edges: &Vec<(String, String, String)>,
    strategy: Option<Strategy>,
    program: Program,
    query: Query,
) -> (Duration, usize, Vec<Vec<TypedValue>>) {

    for (first, second, third) in edges.clone() {
        if third.is_empty() {
            runtime.insert(&first, (second,));
        } else {
            runtime.insert(&first, (second, third));
        }
    }

    if let Some(s) = strategy {
        let (results, evaluation_time): (Vec<Vec<TypedValue>>, Duration) =
            runtime.query_program(&query, program, &s);
        (evaluation_time, results.len(), results)
    } else {
        let start = Instant::now();
        runtime.poll();
        let execution_time = start.elapsed();
        let results: Vec<Vec<TypedValue>> = runtime.query(&query).into_iter().flatten().collect();
        (execution_time, results.len(), results)
    }
}

pub fn run_benchmarks_university(
    args: &Args,
) -> Result<Vec<BenchmarkResult>, Box<dyn Error>> {

    // ==== Parse data ====
    let data = include_str!("../data/lubm1.nt");
    let mut parsed_data = Vec::new();
    
    data.lines().into_iter().for_each(|line| {
        if !line.contains("genid") {
            if let Some((s, p, o)) = parse_data(line) {
                parsed_data.push((s, p, o));
            }
        }
    });

    // ==== End parse data ====

    // ==== Program ====
    let program = program! {
        University(?y) <- [mastersDegreeFrom(?x,?y)],
        Person(?x) <- [title(?x,?y)],
        degreeFrom(?x,?y) <- [hasAlumnus(?y,?x)],
        hasAlumnus(?x,?y) <- [degreeFrom(?y,?x)],
        Employee(?x) <- [Faculty(?x)],
        Faculty(?x) <- [Professor(?x)],
        Course(?y) <- [listedCourse(?x,?y)],
        Professor(?x) <- [AssociateProfessor(?x)],
        Person(?y) <- [member(?x,?y)],
        Professor(?x) <- [AssistantProfessor(?x)],
        Organization(?x) <- [orgPublication(?x,?y)],
        Professor(?x) <- [Chair(?x)],
        Article(?x) <- [TechnicalReport(?x)],
        worksFor(?x,?y) <- [headOf(?x,?y)],
        Person(?x) <- [age(?x,?y)],
        Person(?x) <- [degreeFrom(?x,?y)],
        University(?y) <- [degreeFrom(?x,?y)],
        Publication(?x) <- [Specification(?x)],
        AdministrativeStaff(?x) <- [SystemsStaff(?x)],
        Person(?y) <- [hasAlumnus(?x,?y)],
        Publication(?y) <- [softwareDocumentation(?x,?y)],
        Faculty(?x) <- [PostDoc(?x)],
        Software(?x) <- [softwareVersion(?x,?y)],
        Article(?x) <- [ConferencePaper(?x)],
        TeachingAssistant(?x) <- [Person(?x), teachingAssistantOf(?x,?y), Course(?y)],
        Person(?y) <- [affiliateOf(?x,?y)],
        Chair(?x) <- [Person(?x), headOf(?x,?y), Department(?y)],
        Director(?x) <- [Person(?x), headOf(?x,?y), Program(?y)],
        memberOf(?x,?y) <- [member(?y,?x)],
        member(?x,?y) <- [memberOf(?y,?x)],
        Professor(?x) <- [tenured(?x,?y)],
        Course(?y) <- [teacherOf(?x,?y)],
        University(?x) <- [hasAlumnus(?x,?y)],
        Work(?x) <- [Research(?x)],
        Person(?x) <- [telephone(?x,?y)],
        Organization(?x) <- [Institute(?x)],
        Organization(?y) <- [subOrganizationOf(?x,?y)],
        memberOf(?x,?y) <- [worksFor(?x,?y)],
        Person(?x) <- [Employee(?x)],
        Software(?x) <- [softwareDocumentation(?x,?y)],
        Person(?x) <- [advisor(?x,?y)],
        Organization(?x) <- [member(?x,?y)],
        Organization(?x) <- [Department(?x)],
        Publication(?x) <- [Article(?x)],
        Faculty(?x) <- [Lecturer(?x)],
        Person(?y) <- [publicationAuthor(?x,?y)],
        Publication(?x) <- [Software(?x)],
        Research(?y) <- [researchProject(?x,?y)],
        Organization(?x) <- [Program(?x)],
        Employee(?x) <- [AdministrativeStaff(?x)],
        Professor(?y) <- [advisor(?x,?y)],
        Work(?x) <- [Course(?x)],
        Professor(?x) <- [FullProfessor(?x)],
        Publication(?x) <- [Book(?x)],
        Publication(?x) <- [publicationResearch(?x,?y)],
        AdministrativeStaff(?x) <- [ClericalStaff(?x)],
        degreeFrom(?x,?y) <- [doctoralDegreeFrom(?x,?y)],
        Organization(?x) <- [affiliatedOrganizationOf(?x,?y)],
        TeachingAssistant(?x) <- [teachingAssistantOf(?x,?y)],
        Professor(?x) <- [VisitingProfessor(?x)],
        Person(?x) <- [undergraduateDegreeFrom(?x,?y)],
        Organization(?x) <- [University(?x)],
        Article(?x) <- [JournalArticle(?x)],
        Research(?y) <- [publicationResearch(?x,?y)],
        Person(?x) <- [Director(?x)],
        Person(?x) <- [doctoralDegreeFrom(?x,?y)],
        Publication(?x) <- [publicationDate(?x,?y)],
        Organization(?y) <- [affiliatedOrganizationOf(?x,?y)],
        University(?y) <- [doctoralDegreeFrom(?x,?y)],
        Course(?y) <- [teachingAssistantOf(?x,?y)],
        University(?y) <- [undergraduateDegreeFrom(?x,?y)],
        degreeFrom(?x,?y) <- [mastersDegreeFrom(?x,?y)],
        Schedule(?x) <- [listedCourse(?x,?y)],
        Person(?x) <- [GraduateStudent(?x)],
        Person(?x) <- [ResearchAssistant(?x)],
        Student(?x) <- [UndergraduateStudent(?x)],
        degreeFrom(?x,?y) <- [undergraduateDegreeFrom(?x,?y)],
        Publication(?x) <- [publicationAuthor(?x,?y)],
        Person(?x) <- [mastersDegreeFrom(?x,?y)],
        Organization(?x) <- [College(?x)],
        Organization(?x) <- [ResearchGroup(?x)],
        Faculty(?x) <- [teacherOf(?x,?y)],
        Publication(?x) <- [UnofficialPublication(?x)],
        Person(?x) <- [Chair(?x)],
        Employee(?x) <- [Person(?x), worksFor(?x,?y), Organization(?y)],
        ResearchGroup(?x) <- [researchProject(?x,?y)],
        Organization(?x) <- [affiliateOf(?x,?y)],
        Course(?x) <- [GraduateCourse(?x)],
        Student(?x) <- [Person(?x), takesCourse(?x,?y), Course(?y)],
        Professor(?x) <- [Dean(?x)],
        Publication(?y) <- [orgPublication(?x,?y)],
        Publication(?x) <- [Manual(?x)],
        Dean(?x) <- [headOf(?x,?y), College(?y)],
        Person(?x) <- [TeachingAssistant(?x)],
        Organization(?x) <- [subOrganizationOf(?x,?y)],
        Person(?x) <- [Student(?x)],
        Person(?x) <- [emailAddress(?x,?y)],
        subOrganizationOf(?x,?z) <- [subOrganizationOf(?x,?y), subOrganizationOf(?y,?z)],
    };

    // ==== End program ====

    // ==== Query ====
    let matchers = match (args.query_source, args.query_target) {
        (Some(src), Some(tgt)) => vec![Matcher::Constant(TypedValue::from(src)), Matcher::Constant(TypedValue::from(tgt))],
        (Some(src), None) => vec![Matcher::Constant(TypedValue::from(src)), Matcher::Any],
        (None, Some(tgt)) => vec![Matcher::Any, Matcher::Constant(TypedValue::from(tgt))],
        (None, None) => {
            if args.arity == 1 {
                vec![Matcher::Any]
            } else {
                vec![Matcher::Any, Matcher::Any]
            }
        }
    };
    
    let query = Query {
        symbol: &args.query_predicate,
        matchers: matchers,
    };
    // ==== End query ====

    // ==== Start benchmarks ====
    let mut integral = Vec::new();
    let mut results = Vec::new();

    let mut streaming_micro = MicroRuntime::new(program.clone());
    let mut streaming_micro_magic = MicroRuntime::new(program.clone());
    let mut streaming_micro_tabling = MicroRuntime::new(program.clone());
    let mut ascent_runtime = AscentProgram::default();

    let chunk_size = if args.no_batching {
        parsed_data.len()
    } else {
        args.batch_size
    };

    for line_batch in &parsed_data.iter().chunks(chunk_size) {
        let batch: Vec<_> = line_batch.map(|(s, p, o)| (s.into(), p.into(), o.into())).collect::<Vec<_>>();
        integral.extend_from_slice(&batch);

        // Run selected benchmarks on just the new batch
        if args.micro_streaming {
            let (time, tuples, result_tuples) = run_micro_benchmark(
                &mut streaming_micro,
                &batch,
                None,
                program.clone(),
                query.clone(),
            );

            results.push(BenchmarkResult::new(
                "micro-streaming",
                batch.len(),
                integral.len(),
                time,
                tuples,
                result_tuples.clone(),
            ));
            println!(
                "Micro-streaming result tuples number: {:?}",
                result_tuples.len()
            );
        }

        if args.micro_magic {
            let (time, tuples, result_tuples) = run_micro_benchmark(
                &mut streaming_micro_magic,
                &batch,
                Some(Strategy::BottomUp),
                program.clone(),
                query.clone(),
            );
            results.push(BenchmarkResult::new(
                "micro-magic",
                batch.len(),
                integral.len(),
                time,
                tuples,
                result_tuples.clone(),
            ));
            println!(
                "Micro-magic result tuples number: {:?}",
                result_tuples.len()
            );
        }

        if args.micro_tabling {
            let (time, tuples, result_tuples) = run_micro_benchmark(
                &mut streaming_micro_tabling,
                &batch,
                Some(Strategy::TopDown),
                program.clone(),
                query.clone(),
            );
            results.push(BenchmarkResult::new(
                "micro-tabling",
                batch.len(),
                integral.len(),
                time,
                tuples,
                result_tuples.clone(),
            ));

            println!(
                "Micro-tabling result tuples number: {:?}",
                result_tuples.len()
            );
        }

        // if args.ascent {
        //     let (time, tuples, result_tuples) = run_ascent_benchmark(
        //         &mut ascent_runtime,
        //         &integral,
        //         args.query_source,
        //         args.query_target,
        //         args.query_middle,
        //     );
        //     let converted_result_tuples: Vec<Vec<TypedValue>> = result_tuples
        //         .into_iter()
        //         .map(|(a, b, c)| {
        //             vec![
        //                 TypedValue::from(a),
        //                 TypedValue::from(b),
        //                 TypedValue::from(c),
        //             ]
        //         })
        //         .collect();

        //     results.push(BenchmarkResult::new(
        //         "ascent",
        //         batch.len(),
        //         integral.len(),
        //         time,
        //         tuples,
        //         converted_result_tuples.clone(),
        //     ));
        //     println!(
        //         "Ascent result tuples number: {:?}",
        //         converted_result_tuples.len()
        //     );
        // }

        // Print progress
        println!("Processed {} edges", integral.len());
    }

    Ok(results)
  
}
