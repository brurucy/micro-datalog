use crate::args::Args;
use crate::benchmark::BenchmarkResult;
use crate::engine::datalog::{MicroRuntime, Strategy};
use crate::helpers::parser::parse_data;
use ascent::ascent;
use datalog_rule_macro::program;
use datalog_syntax::*;
use itertools::*;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::time::{Duration, Instant};

ascent! {
    relation AdministrativeStaff(String);
    relation Article(String);
    relation AssistantProfessor(String);
    relation AssociateProfessor(String);
    relation Book(String);
    relation Chair(String);
    relation ClericalStaff(String);
    relation College(String);
    relation ConferencePaper(String);
    relation Course(String);
    relation Dean(String);
    relation Department(String);
    relation Director(String);
    relation Employee(String);
    relation Faculty(String);
    relation FullProfessor(String);
    relation GraduateCourse(String);
    relation GraduateStudent(String);
    relation Institute(String);
    relation JournalArticle(String);
    relation Lecturer(String);
    relation Manual(String);
    relation Organization(String);
    relation Person(String);
    relation PostDoc(String);
    relation Professor(String);
    relation Program(String);
    relation Publication(String);
    relation Research(String);
    relation ResearchAssistant(String);
    relation ResearchGroup(String);
    relation Schedule(String);
    relation Software(String);
    relation Specification(String);
    relation Student(String);
    relation SystemsStaff(String);
    relation TeachingAssistant(String);
    relation TechnicalReport(String);
    relation UndergraduateStudent(String);
    relation UnofficialPublication(String);
    relation University(String);
    relation VisitingProfessor(String);
    relation Work(String);
    relation advisor(String, String);
    relation affiliatedOrganizationOf(String, String);
    relation affiliateOf(String, String);
    relation age(String, String);
    relation degreeFrom(String, String);
    relation doctoralDegreeFrom(String, String);
    relation emailAddress(String, String);
    relation hasAlumnus(String, String);
    relation headOf(String, String);
    relation listedCourse(String, String);
    relation mastersDegreeFrom(String, String);
    relation member(String, String);
    relation memberOf(String, String);
    relation orgPublication(String, String);
    relation publicationAuthor(String, String);
    relation publicationDate(String, String);
    relation publicationResearch(String, String);
    relation researchProject(String, String);
    relation softwareDocumentation(String, String);
    relation softwareVersion(String, String);
    relation subOrganizationOf(String, String);
    relation takesCourse(String, String);
    relation teacherOf(String, String);
    relation teachingAssistantOf(String, String);
    relation telephone(String, String);
    relation tenured(String, String);
    relation title(String, String);
    relation undergraduateDegreeFrom(String, String);
    relation worksFor(String, String);
    relation researchAssistant(String, String);
    relation undergraduateStudent(String, String);


    University(y) <-- mastersDegreeFrom(x,y);
    Person(x) <-- title(x,y);
    degreeFrom(x,y) <-- hasAlumnus(y,x);
    hasAlumnus(x,y) <-- degreeFrom(y,x);
    Employee(x) <-- Faculty(x);
    Faculty(x) <-- Professor(x);
    Course(y) <-- listedCourse(x,y);
    Professor(x) <-- AssociateProfessor(x);
    Person(y) <-- member(x,y);
    Professor(x) <-- AssistantProfessor(x);
    Organization(x) <-- orgPublication(x,y);
    Professor(x) <-- Chair(x);
    Article(x) <-- TechnicalReport(x);
    worksFor(x,y) <-- headOf(x,y);
    Person(x) <-- age(x,y);
    Person(x) <-- degreeFrom(x,y);
    University(y) <-- degreeFrom(x,y);
    Publication(x) <-- Specification(x);
    AdministrativeStaff(x) <-- SystemsStaff(x);
    Person(y) <-- hasAlumnus(x,y);
    Publication(y) <-- softwareDocumentation(x,y);
    Faculty(x) <-- PostDoc(x);
    Software(x) <-- softwareVersion(x,y);
    Article(x) <-- ConferencePaper(x);
    TeachingAssistant(x) <-- Person(x), teachingAssistantOf(x,y), Course(y);
    Person(y) <-- affiliateOf(x,y);
    Chair(x) <-- Person(x), headOf(x,y), Department(y);
    Director(x) <-- Person(x), headOf(x,y), Program(y);
    memberOf(x,y) <-- member(y,x);
    member(x,y) <-- memberOf(y,x);
    Professor(x) <-- tenured(x,y);
    Course(y) <-- teacherOf(x,y);
    University(x) <-- hasAlumnus(x,y);
    Work(x) <-- Research(x);
    Person(x) <-- telephone(x,y);
    Organization(x) <-- Institute(x);
    Organization(y) <-- subOrganizationOf(x,y);
    memberOf(x,y) <-- worksFor(x,y);
    Person(x) <-- Employee(x);
    Software(x) <-- softwareDocumentation(x,y);
    Person(x) <-- advisor(x,y);
    Organization(x) <-- member(x,y);
    Organization(x) <-- Department(x);
    Publication(x) <-- Article(x);
    Faculty(x) <-- Lecturer(x);
    Person(y) <-- publicationAuthor(x,y);
    Publication(x) <-- Software(x);
    Research(y) <-- researchProject(x,y);
    Organization(x) <-- Program(x);
    Employee(x) <-- AdministrativeStaff(x);
    Professor(y) <-- advisor(x,y);
    Work(x) <-- Course(x);
    Professor(x) <-- FullProfessor(x);
    Publication(x) <-- Book(x);
    Publication(x) <-- publicationResearch(x,y);
    AdministrativeStaff(x) <-- ClericalStaff(x);
    degreeFrom(x,y) <-- doctoralDegreeFrom(x,y);
    Organization(x) <-- affiliatedOrganizationOf(x,y);
    TeachingAssistant(x) <-- teachingAssistantOf(x,y);
    Professor(x) <-- VisitingProfessor(x);
    Person(x) <-- undergraduateDegreeFrom(x,y);
    Organization(x) <-- University(x);
    Article(x) <-- JournalArticle(x);
    Research(y) <-- publicationResearch(x,y);
    Person(x) <-- Director(x);
    Person(x) <-- doctoralDegreeFrom(x,y);
    Publication(x) <-- publicationDate(x,y);
    Organization(y) <-- affiliatedOrganizationOf(x,y);
    University(y) <-- doctoralDegreeFrom(x,y);
    Course(y) <-- teachingAssistantOf(x,y);
    University(y) <-- undergraduateDegreeFrom(x,y);
    degreeFrom(x,y) <-- mastersDegreeFrom(x,y);
    Schedule(x) <-- listedCourse(x,y);
    Person(x) <-- GraduateStudent(x);
    Person(x) <-- ResearchAssistant(x);
    Student(x) <-- UndergraduateStudent(x);
    degreeFrom(x,y) <-- undergraduateDegreeFrom(x,y);
    Publication(x) <-- publicationAuthor(x,y);
    Person(x) <-- mastersDegreeFrom(x,y);
    Organization(x) <-- College(x);
    Organization(x) <-- ResearchGroup(x);
    Faculty(x) <-- teacherOf(x,y);
    Publication(x) <-- UnofficialPublication(x);
    Person(x) <-- Chair(x);
    Employee(x) <-- Person(x), worksFor(x,y), Organization(y);
    ResearchGroup(x) <-- researchProject(x,y);
    Organization(x) <-- affiliateOf(x,y);
    Course(x) <-- GraduateCourse(x);
    Student(x) <-- Person(x), takesCourse(x,y), Course(y);
    Professor(x) <-- Dean(x);
    Publication(y) <-- orgPublication(x,y);
    Publication(x) <-- Manual(x);
    Dean(x) <-- headOf(x,y), College(y);
    Person(x) <-- TeachingAssistant(x);
    Person(x) <-- Student(x);
    Person(x) <-- emailAddress(x,y);
    subOrganizationOf(x,z) <-- subOrganizationOf(x,y), subOrganizationOf(y,z);
}

fn save_parsed_data_to_file(
    parsed_data: &[(String, String, String)],
    filename: &str,
) -> Result<(), Box<dyn Error>> {
    let mut file = File::create(filename)?;
    for (s, p, o) in parsed_data {
        writeln!(file, "{} {} {}", s, p, o)?;
    }
    println!("Parsed data saved to {}", filename);
    Ok(())
}

fn run_ascent_benchmark(
    runtime: &mut AscentProgram,
    edges: &[(String, String, String)],
    query_source_str: Option<String>,
) -> (Duration, usize, Vec<(String,)>) {
    for (pred, x, y) in edges {
        match pred.as_str() {
            "affiliateOf" => {
                runtime.affiliateOf.push((x.into(), y.into()));
            }
            "AssistantProfessor" => {
                runtime.AssistantProfessor.push((x.into(),));
            }
            "AssociateProfessor" => {
                runtime.AssociateProfessor.push((x.into(),));
            }
            "Book" => {
                runtime.Book.push((x.into(),));
            }
            "ClericalStaff" => {
                runtime.ClericalStaff.push((x.into(),));
            }
            "College" => {
                runtime.College.push((x.into(),));
            }
            "ConferencePaper" => {
                runtime.ConferencePaper.push((x.into(),));
            }
            "Department" => {
                runtime.Department.push((x.into(),));
            }
            "FullProfessor" => {
                runtime.FullProfessor.push((x.into(),));
            }
            "GraduateCourse" => {
                runtime.GraduateCourse.push((x.into(),));
            }
            "GraduateStudent" => {
                runtime.GraduateStudent.push((x.into(),));
            }
            "Institute" => {
                runtime.Institute.push((x.into(),));
            }
            "UndergraduateStudent" => {
                runtime.UndergraduateStudent.push((x.into(),));
            }
            "UnofficialPublication" => {
                runtime.UnofficialPublication.push((x.into(),));
            }
            "VisitingProfessor" => {
                runtime.VisitingProfessor.push((x.into(),));
            }
            "advisor" => {
                runtime.advisor.push((x.into(), y.into()));
            }
            "affiliatedOrganizationOf" => {
                runtime.affiliatedOrganizationOf.push((x.into(), y.into()));
            }
            "age" => {
                runtime.age.push((x.into(), y.into()));
            }
            "doctoralDegreeFrom" => {
                runtime.doctoralDegreeFrom.push((x.into(), y.into()));
            }
            "emailAddress" => {
                runtime.emailAddress.push((x.into(), y.into()));
            }
            "headOf" => {
                runtime.headOf.push((x.into(), y.into()));
            }
            "listedCourse" => {
                runtime.mastersDegreeFrom.push((x.into(), y.into()));
            }
            "member" => {
                runtime.member.push((x.into(), y.into()));
            }
            "orgPublication" => {
                runtime.orgPublication.push((x.into(), y.into()));
            }
            "publicationAuthor" => {
                runtime.publicationAuthor.push((x.into(), y.into()));
            }
            "publicationDate" => {
                runtime.publicationDate.push((x.into(), y.into()));
            }
            "publicationResearch" => {
                runtime.publicationResearch.push((x.into(), y.into()));
            }
            "researchProject" => {
                runtime.researchProject.push((x.into(), y.into()));
            }
            "softwareDocumentation" => {
                runtime.softwareDocumentation.push((x.into(), y.into()));
            }
            "softwareVersion" => {
                runtime.softwareVersion.push((x.into(), y.into()));
            }
            "takesCourse" => {
                runtime.takesCourse.push((x.into(), y.into()));
            }
            "ResearchAssistant" => {
                runtime.ResearchAssistant.push((x.into(),));
            }
            "teachingAssistantOf" => {
                runtime.teachingAssistantOf.push((x.into(), y.into()));
            }
            "subOrganizationOf" => {
                runtime.subOrganizationOf.push((x.into(), y.into()));
            }
            "undergraduateDegreeFrom" => {
                runtime.undergraduateDegreeFrom.push((x.into(), y.into()));
            }
            "worksFor" => {
                runtime.worksFor.push((x.into(), y.into()));
            }
            "mastersDegreeFrom" => {
                runtime.mastersDegreeFrom.push((x.into(), y.into()));
            }
            "teacherOf" => {
                runtime.teacherOf.push((x.into(), y.into()));
            }
            "Lecturer" => {
                runtime.Lecturer.push((x.into(),));
            }
            "University" => {
                runtime.University.push((x.into(),));
            }
            "TeachingAssistant" => {
                runtime.TeachingAssistant.push((x.into(),));
            }
            "Course" => {
                runtime.Course.push((x.into(),));
            }
            "Publication" => {
                runtime.Publication.push((x.into(),));
            }
            "memberOf" => {
                runtime.memberOf.push((x.into(), y.into()));
            }
            "ResearchGroup" => {
                runtime.ResearchGroup.push((x.into(),));
            }

            _ => {
                //println!("Invalid predicate: {}", pred);
                continue;
            }
        }
    }

    let start = Instant::now();
    runtime.run();
    let elapsed_time = start.elapsed();
    // Query tuples based on source and target
    let results: Vec<_> = runtime
        .University
        .iter()
        .cloned()
        // .filter(
        //     |&(x)| match (query_source, query_middle, query_target) {
        //         (Some(src), Some(middle), Some(tgt)) => x == src && z == tgt && y == middle,
        //         (Some(src), None, Some(tgt)) => x == src && z == tgt,
        //         (None, Some(middle), Some(tgt)) => y == middle && z == tgt,
        //         (Some(src), None, None) => x == src,
        //         (None, Some(middle), None) => y == middle,
        //         (None, None, Some(tgt)) => z == tgt,
        //         (Some(src), Some(middle), None) => x == src && y == middle,
        //         (None, None, None) => true,
        //     },
        // )
        //.filter(|(x, )| x.as_str() == query_source_str.as_ref().unwrap())
        .collect();
    (elapsed_time, results.len(), results)
}

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
        //println!("runtime: {:?}", runtime.unprocessed_insertions.get_all_relations());
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

pub fn run_benchmarks_university(args: &Args) -> Result<Vec<BenchmarkResult>, Box<dyn Error>> {
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
        Person(?x) <- [Student(?x)],
        Person(?x) <- [emailAddress(?x,?y)],
        subOrganizationOf(?x,?z) <- [subOrganizationOf(?x,?y), subOrganizationOf(?y,?z)],
    };

    // ==== End program ====

    // ==== Query ====
    let matchers = match (args.query_source_str.clone(), args.query_target_str.clone()) {
        (Some(src), Some(tgt)) => vec![
            Matcher::Constant(TypedValue::from(src)),
            Matcher::Constant(TypedValue::from(tgt)),
        ],
        (Some(src), None) => {
            if args.arity == 1 {
                vec![Matcher::Constant(TypedValue::from(src))]
            } else {
                vec![Matcher::Constant(TypedValue::from(src)), Matcher::Any]
            }
        }
        (None, Some(tgt)) => {
            if args.arity == 1 {
                vec![Matcher::Constant(TypedValue::from(tgt))]
            } else {
                vec![Matcher::Any, Matcher::Constant(TypedValue::from(tgt))]
            }
        }
        (None, None) => {
            if args.arity == 1 {
                vec![Matcher::Any]
            } else {
                vec![Matcher::Any, Matcher::Any]
            }
        }
    };

    let query_predicate = if args.query_predicate.is_empty() {
        "title"
    } else {
        args.query_predicate.as_str()
    };
    let query = Query {
        symbol: query_predicate,
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
        let batch: Vec<_> = line_batch
            .map(|(s, p, o)| (s.into(), p.into(), o.into()))
            .collect::<Vec<_>>();
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

        if args.ascent {
            let (time, tuples, result_tuples) = run_ascent_benchmark(
                &mut ascent_runtime,
                &integral,
                args.query_source_str.clone(),
            );
            let mut seen = HashSet::new();
            let converted_result_tuples: Vec<Vec<TypedValue>> = result_tuples
                .into_iter()
                .map(|(a,)| vec![TypedValue::from(a)])
                .filter(|tuple| seen.insert(tuple.clone()))
                .collect();

            results.push(BenchmarkResult::new(
                "ascent",
                batch.len(),
                integral.len(),
                time,
                tuples,
                converted_result_tuples.clone(),
            ));
            println!(
                "Ascent result tuples number: {:?}",
                converted_result_tuples.len()
            );
        }

        // Print progress
        println!("Processed {} edges", integral.len());
    }

    Ok(results)
}
