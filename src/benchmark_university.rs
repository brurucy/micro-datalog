use crate::args::Args;
use crate::benchmark::BenchmarkResult;
use crate::engine::datalog::{MicroRuntime, Strategy};
use crate::helpers::parser::parse_data;
use ascent::ascent;
use datalog_rule_macro::program;
use datalog_syntax::*;
use itertools::*;
use std::collections::HashSet;
use std::error::Error;
use std::time::{Duration, Instant};

ascent! {
    relation AdministrativeStaff(String);
    relation AdministrativeStaff_ground(String);
    relation Article(String);
    relation Article_ground(String);
    relation AssistantProfessor(String);
    relation AssistantProfessor_ground(String);
    relation AssociateProfessor(String);
    relation AssociateProfessor_ground(String);
    relation Book(String);
    relation Book_ground(String);
    relation Chair(String);
    relation Chair_ground(String);
    relation ClericalStaff(String);
    relation ClericalStaff_ground(String);
    relation College(String);
    relation College_ground(String);
    relation ConferencePaper(String);
    relation ConferencePaper_ground(String);
    relation Course(String);
    relation Course_ground(String);
    relation Dean(String);
    relation Dean_ground(String);
    relation Department(String);
    relation Department_ground(String);
    relation Director(String);
    relation Director_ground(String);
    relation Employee(String);
    relation Employee_ground(String);
    relation Faculty(String);
    relation Faculty_ground(String);
    relation FullProfessor(String);
    relation FullProfessor_ground(String);
    relation GraduateCourse(String);
    relation GraduateCourse_ground(String);
    relation GraduateStudent(String);
    relation GraduateStudent_ground(String);
    relation Institute(String);
    relation Institute_ground(String);
    relation JournalArticle(String);
    relation JournalArticle_ground(String);
    relation Lecturer(String);
    relation Lecturer_ground(String);
    relation Manual(String);
    relation Manual_ground(String);
    relation Organization(String);
    relation Organization_ground(String);
    relation Person(String);
    relation Person_ground(String);
    relation PostDoc(String);
    relation PostDoc_ground(String);
    relation Professor(String);
    relation Professor_ground(String);
    relation Program(String);
    relation Publication(String);
    relation Publication_ground(String);
    relation Research(String);
    relation Research_ground(String);
    relation ResearchAssistant(String);
    relation ResearchAssistant_ground(String);
    relation ResearchGroup(String);
    relation ResearchGroup_ground(String);
    relation Schedule(String);
    relation Schedule_ground(String);
    relation Software(String);
    relation Software_ground(String);
    relation Specification(String);
    relation Specification_ground(String);
    relation Student(String);
    relation Student_ground(String);
    relation SystemsStaff(String);
    relation SystemsStaff_ground(String);
    relation TeachingAssistant(String);
    relation TeachingAssistant_ground(String);
    relation TechnicalReport(String);
    relation TechnicalReport_ground(String);
    relation UndergraduateStudent(String);
    relation UndergraduateStudent_ground(String);
    relation UnofficialPublication(String);
    relation UnofficialPublication_ground(String);
    relation University(String);
    relation University_ground(String);
    relation VisitingProfessor(String);
    relation VisitingProfessor_ground(String);
    relation Work(String);
    relation Work_ground(String);
    relation advisor(String, String);
    relation advisor_ground(String, String);
    relation affiliatedOrganizationOf(String, String);
    relation affiliatedOrganizationOf_ground(String, String);
    relation affiliateOf(String, String);
    relation affiliateOf_ground(String, String);
    relation age(String, String);
    relation age_ground(String, String);
    relation degreeFrom(String, String);
    relation degreeFrom_ground(String, String);
    relation doctoralDegreeFrom(String, String);
    relation doctoralDegreeFrom_ground(String, String);
    relation emailAddress(String, String);
    relation emailAddress_ground(String, String);
    relation hasAlumnus(String, String);
    relation hasAlumnus_ground(String, String);
    relation headOf(String, String);
    relation headOf_ground(String, String);
    relation listedCourse(String, String);
    relation listedCourse_ground(String, String);
    relation mastersDegreeFrom(String, String);
    relation mastersDegreeFrom_ground(String, String);
    relation member(String, String);
    relation member_ground(String, String);
    relation memberOf(String, String);
    relation memberOf_ground(String, String);
    relation orgPublication(String, String);
    relation orgPublication_ground(String, String);
    relation publicationAuthor(String, String);
    relation publicationAuthor_ground(String, String);
    relation publicationDate(String, String);
    relation publicationDate_ground(String, String);
    relation publicationResearch(String, String);
    relation publicationResearch_ground(String, String);
    relation researchProject(String, String);
    relation researchProject_ground(String, String);
    relation softwareDocumentation(String, String);
    relation softwareDocumentation_ground(String, String);
    relation softwareVersion(String, String);
    relation softwareVersion_ground(String, String);
    relation subOrganizationOf(String, String);
    relation subOrganizationOf_ground(String, String);
    relation takesCourse(String, String);
    relation takesCourse_ground(String, String);
    relation teacherOf(String, String);
    relation teacherOf_ground(String, String);
    relation teachingAssistantOf(String, String);
    relation teachingAssistantOf_ground(String, String);
    relation telephone(String, String);
    relation telephone_ground(String, String);
    relation tenured(String, String);
    relation tenured_ground(String, String);
    relation title(String, String);
    relation title_ground(String, String);
    relation undergraduateDegreeFrom(String, String);
    relation undergraduateDegreeFrom_ground(String, String);
    relation worksFor(String, String);
    relation worksFor_ground(String, String);
    relation researchAssistant(String, String);
    relation researchAssistant_ground(String, String);
    relation undergraduateStudent(String, String);
    relation undergraduateStudent_ground(String, String);

    AdministrativeStaff(x) <-- AdministrativeStaff_ground(x);
    Article(x) <-- Article_ground(x);
    AssistantProfessor(x) <-- AssistantProfessor_ground(x);
    AssociateProfessor(x) <-- AssociateProfessor_ground(x);
    Book(x) <-- Book_ground(x);
    Chair(x) <-- Chair_ground(x);
    ClericalStaff(x) <-- ClericalStaff_ground(x);
    College(x) <-- College_ground(x);
    ConferencePaper(x) <-- ConferencePaper_ground(x);
    Course(x) <-- Course_ground(x);
    Dean(x) <-- Dean_ground(x);
    Department(x) <-- Department_ground(x);
    Director(x) <-- Director_ground(x);
    Employee(x) <-- Employee_ground(x);
    Faculty(x) <-- Faculty_ground(x);
    FullProfessor(x) <-- FullProfessor_ground(x);
    GraduateCourse(x) <-- GraduateCourse_ground(x);
    GraduateStudent(x) <-- GraduateStudent_ground(x);
    Institute(x) <-- Institute_ground(x);
    JournalArticle(x) <-- JournalArticle_ground(x);
    Lecturer(x) <-- Lecturer_ground(x);
    Manual(x) <-- Manual_ground(x);
    Organization(x) <-- Organization_ground(x);
    Person(x) <-- Person_ground(x);
    PostDoc(x) <-- PostDoc_ground(x);
    Professor(x) <-- Professor_ground(x);
    Publication(x) <-- Publication_ground(x);
    Research(x) <-- Research_ground(x);
    ResearchAssistant(x) <-- ResearchAssistant_ground(x);
    ResearchGroup(x) <-- ResearchGroup_ground(x);
    Schedule(x) <-- Schedule_ground(x);
    Software(x) <-- Software_ground(x);
    Specification(x) <-- Specification_ground(x);
    Student(x) <-- Student_ground(x);
    SystemsStaff(x) <-- SystemsStaff_ground(x);
    TechnicalReport(x) <-- TechnicalReport_ground(x);
    UndergraduateStudent(x) <-- UndergraduateStudent_ground(x);
    UnofficialPublication(x) <-- UnofficialPublication_ground(x);
    University(x) <-- University_ground(x);
    VisitingProfessor(x) <-- VisitingProfessor_ground(x);
    Work(x) <-- Work_ground(x);
    advisor(x,y) <-- advisor_ground(x,y);
    affiliatedOrganizationOf(x,y) <-- affiliatedOrganizationOf_ground(x,y);
    affiliateOf(x,y) <-- affiliateOf_ground(x,y);
    age(x,y) <-- age_ground(x,y);
    degreeFrom(x,y) <-- degreeFrom_ground(x,y);
    doctoralDegreeFrom(x,y) <-- doctoralDegreeFrom_ground(x,y);
    emailAddress(x,y) <-- emailAddress_ground(x,y);
    hasAlumnus(x,y) <-- hasAlumnus_ground(x,y);
    headOf(x,y) <-- headOf_ground(x,y);
    listedCourse(x,y) <-- listedCourse_ground(x,y);
    mastersDegreeFrom(x,y) <-- mastersDegreeFrom_ground(x,y);
    member(x,y) <-- member_ground(x,y);
    memberOf(x,y) <-- memberOf_ground(x,y);
    orgPublication(x,y) <-- orgPublication_ground(x,y);
    publicationAuthor(x,y) <-- publicationAuthor_ground(x,y);
    publicationDate(x,y) <-- publicationDate_ground(x,y);
    publicationResearch(x,y) <-- publicationResearch_ground(x,y);
    researchProject(x,y) <-- researchProject_ground(x,y);
    softwareDocumentation(x,y) <-- softwareDocumentation_ground(x,y);
    softwareVersion(x,y) <-- softwareVersion_ground(x,y);
    subOrganizationOf(x,y) <-- subOrganizationOf_ground(x,y);
    takesCourse(x,y) <-- takesCourse_ground(x,y);
    teacherOf(x,y) <-- teacherOf_ground(x,y);
    teachingAssistantOf(x,y) <-- teachingAssistantOf_ground(x,y);
    telephone(x,y) <-- telephone_ground(x,y);
    tenured(x,y) <-- tenured_ground(x,y);
    title(x,y) <-- title_ground(x,y);
    undergraduateDegreeFrom(x,y) <-- undergraduateDegreeFrom_ground(x,y);
    worksFor(x,y) <-- worksFor_ground(x,y);
    researchAssistant(x,y) <-- researchAssistant_ground(x,y);
    undergraduateStudent(x,y) <-- undergraduateStudent_ground(x,y);

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

// fn save_parsed_data_to_file(
//     parsed_data: &Vec<(String, String)>,
//     filename: &str,
// ) -> Result<(), Box<dyn Error>> {
//     let mut file = File::create(filename)?;
//     for (s, p) in parsed_data {
//         writeln!(file, "{} {}", s, p)?;
//     }
//     println!("Parsed data saved to {}", filename);
//     Ok(())
// }

fn run_ascent_benchmark(
    runtime: &mut AscentProgram,
    edges: &[(String, String, String)],
    query_source_str: Option<String>,
    query_target_str: Option<String>,
) -> (Duration, usize, Vec<(String, String)>) {
    for (pred, x, y) in edges {
        match pred.as_str() {
            "affiliateOf" => {
                runtime.affiliateOf_ground.push((x.into(), y.into()));
            }
            "AssistantProfessor" => {
                runtime.AssistantProfessor_ground.push((x.into(),));
            }
            "AssociateProfessor" => {
                runtime.AssociateProfessor_ground.push((x.into(),));
            }
            "Book" => {
                runtime.Book_ground.push((x.into(),));
            }
            "ClericalStaff" => {
                runtime.ClericalStaff_ground.push((x.into(),));
            }
            "College" => {
                runtime.College_ground.push((x.into(),));
            }
            "ConferencePaper" => {
                runtime.ConferencePaper_ground.push((x.into(),));
            }
            "Department" => {
                runtime.Department_ground.push((x.into(),));
            }
            "FullProfessor" => {
                runtime.FullProfessor_ground.push((x.into(),));
            }
            "GraduateCourse" => {
                runtime.GraduateCourse_ground.push((x.into(),));
            }
            "GraduateStudent" => {
                runtime.GraduateStudent_ground.push((x.into(),));
            }
            "Institute" => {
                runtime.Institute_ground.push((x.into(),));
            }
            "UndergraduateStudent" => {
                runtime.UndergraduateStudent_ground.push((x.into(),));
            }
            "UnofficialPublication" => {
                runtime.UnofficialPublication_ground.push((x.into(),));
            }
            "VisitingProfessor" => {
                runtime.VisitingProfessor_ground.push((x.into(),));
            }
            "advisor" => {
                runtime.advisor_ground.push((x.into(), y.into()));
            }
            "affiliatedOrganizationOf" => {
                runtime.affiliatedOrganizationOf_ground.push((x.into(), y.into()));
            }
            "age" => {
                runtime.age_ground.push((x.into(), y.into()));
            }
            "doctoralDegreeFrom" => {
                runtime.doctoralDegreeFrom_ground.push((x.into(), y.into()));
            }
            "emailAddress" => {
                runtime.emailAddress_ground.push((x.into(), y.into()));
            }
            "headOf" => {
                runtime.headOf_ground.push((x.into(), y.into()));
            }
            "listedCourse" => {
                runtime.mastersDegreeFrom_ground.push((x.into(), y.into()));
            }
            "member" => {
                runtime.member_ground.push((x.into(), y.into()));
            }
            "orgPublication" => {
                runtime.orgPublication_ground.push((x.into(), y.into()));
            }
            "publicationAuthor" => {
                runtime.publicationAuthor_ground.push((x.into(), y.into()));
            }
            "publicationDate" => {
                runtime.publicationDate_ground.push((x.into(), y.into()));
            }
            "publicationResearch" => {
                runtime.publicationResearch_ground.push((x.into(), y.into()));
            }
            "researchProject" => {
                runtime.researchProject_ground.push((x.into(), y.into()));
            }
            "softwareDocumentation" => {
                runtime.softwareDocumentation_ground.push((x.into(), y.into()));
            }
            "softwareVersion" => {
                runtime.softwareVersion_ground.push((x.into(), y.into()));
            }
            "takesCourse" => {
                runtime.takesCourse_ground.push((x.into(), y.into()));
            }
            "ResearchAssistant" => {
                runtime.ResearchAssistant_ground.push((x.into(),));
            }
            "teachingAssistantOf" => {
                runtime.teachingAssistantOf_ground.push((x.into(), y.into()));
            }
            "subOrganizationOf" => {
                runtime.subOrganizationOf_ground.push((x.into(), y.into()));
            }
            "undergraduateDegreeFrom" => {
                runtime.undergraduateDegreeFrom_ground.push((x.into(), y.into()));
            }
            "worksFor" => {
                runtime.worksFor_ground.push((x.into(), y.into()));
            }
            "mastersDegreeFrom" => {
                runtime.mastersDegreeFrom_ground.push((x.into(), y.into()));
            }
            "teacherOf" => {
                runtime.teacherOf_ground.push((x.into(), y.into()));
            }
            "Lecturer" => {
                runtime.Lecturer_ground.push((x.into(),));
            }
            "University" => {
                runtime.University_ground.push((x.into(),));
            }
            "TeachingAssistant" => {
                runtime.TeachingAssistant_ground.push((x.into(),));
            }
            "Course" => {
                runtime.Course_ground.push((x.into(),));
            }
            "Publication" => {
                runtime.Publication_ground.push((x.into(),));
            }
            "memberOf" => {
                runtime.memberOf_ground.push((x.into(), y.into()));
            }
            "ResearchGroup" => {
                runtime.ResearchGroup_ground.push((x.into(),));
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
        .subOrganizationOf 
        .iter()
        .cloned()
        .filter(|(x, y)| x.as_str() == query_source_str.as_ref().unwrap())
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
            runtime.insert(&format!("{}_ground", first), (second,));
        } else {
            runtime.insert(&format!("{}_ground", first), (second, third));
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
        AdministrativeStaff(?x) <- [AdministrativeStaff_ground(?x)],
        Article(?x) <- [Article_ground(?x)],
        AssistantProfessor(?x) <- [AssistantProfessor_ground(?x)],
        AssociateProfessor(?x) <- [AssociateProfessor_ground(?x)],
        Book(?x) <- [Book_ground(?x)],
        Chair(?x) <- [Chair_ground(?x)],
        ClericalStaff(?x) <- [ClericalStaff_ground(?x)],
        College(?x) <- [College_ground(?x)],
        ConferencePaper(?x) <- [ConferencePaper_ground(?x)],
        Course(?x) <- [Course_ground(?x)],
        Dean(?x) <- [Dean_ground(?x)],
        Department(?x) <- [Department_ground(?x)],
        Director(?x) <- [Director_ground(?x)],
        Employee(?x) <- [Employee_ground(?x)],
        Faculty(?x) <- [Faculty_ground(?x)],
        FullProfessor(?x) <- [FullProfessor_ground(?x)],
        GraduateCourse(?x) <- [GraduateCourse_ground(?x)],
        GraduateStudent(?x) <- [GraduateStudent_ground(?x)],
        Institute(?x) <- [Institute_ground(?x)],
        JournalArticle(?x) <- [JournalArticle_ground(?x)],
        Lecturer(?x) <- [Lecturer_ground(?x)],
        Manual(?x) <- [Manual_ground(?x)],
        Organization(?x) <- [Organization_ground(?x)],
        Person(?x) <- [Person_ground(?x)],
        PostDoc(?x) <- [PostDoc_ground(?x)],
        Professor(?x) <- [Professor_ground(?x)],
        Publication(?x) <- [Publication_ground(?x)],
        Research(?x) <- [Research_ground(?x)],
        ResearchAssistant(?x) <- [ResearchAssistant_ground(?x)],
        ResearchGroup(?x) <- [ResearchGroup_ground(?x)],
        Schedule(?x) <- [Schedule_ground(?x)],
        Software(?x) <- [Software_ground(?x)],
        Specification(?x) <- [Specification_ground(?x)],
        Student(?x) <- [Student_ground(?x)],
        SystemsStaff(?x) <- [SystemsStaff_ground(?x)],
        TechnicalReport(?x) <- [TechnicalReport_ground(?x)],
        UndergraduateStudent(?x) <- [UndergraduateStudent_ground(?x)],
        UnofficialPublication(?x) <- [UnofficialPublication_ground(?x)],
        University(?x) <- [University_ground(?x)],
        VisitingProfessor(?x) <- [VisitingProfessor_ground(?x)],
        Work(?x) <- [Work_ground(?x)],
        advisor(?x,?y) <- [advisor_ground(?x,?y)],
        affiliatedOrganizationOf(?x,?y) <- [affiliatedOrganizationOf_ground(?x,?y)],
        affiliateOf(?x,?y) <- [affiliateOf_ground(?x,?y)],
        age(?x,?y) <- [age_ground(?x,?y)],
        degreeFrom(?x,?y) <- [degreeFrom_ground(?x,?y)],
        doctoralDegreeFrom(?x,?y) <- [doctoralDegreeFrom_ground(?x,?y)],
        emailAddress(?x,?y) <- [emailAddress_ground(?x,?y)],
        hasAlumnus(?x,?y) <- [hasAlumnus_ground(?x,?y)],
        headOf(?x,?y) <- [headOf_ground(?x,?y)],
        listedCourse(?x,?y) <- [listedCourse_ground(?x,?y)],
        mastersDegreeFrom(?x,?y) <- [mastersDegreeFrom_ground(?x,?y)],
        member(?x,?y) <- [member_ground(?x,?y)],
        memberOf(?x,?y) <- [memberOf_ground(?x,?y)],
        orgPublication(?x,?y) <- [orgPublication_ground(?x,?y)],
        publicationAuthor(?x,?y) <- [publicationAuthor_ground(?x,?y)],
        publicationDate(?x,?y) <- [publicationDate_ground(?x,?y)],
        publicationResearch(?x,?y) <- [publicationResearch_ground(?x,?y)],
        researchProject(?x,?y) <- [researchProject_ground(?x,?y)],
        softwareDocumentation(?x,?y) <- [softwareDocumentation_ground(?x,?y)],
        softwareVersion(?x,?y) <- [softwareVersion_ground(?x,?y)],
        subOrganizationOf(?x,?y) <- [subOrganizationOf_ground(?x,?y)],
        takesCourse(?x,?y) <- [takesCourse_ground(?x,?y)],
        teacherOf(?x,?y) <- [teacherOf_ground(?x,?y)],
        teachingAssistantOf(?x,?y) <- [teachingAssistantOf_ground(?x,?y)],
        telephone(?x,?y) <- [telephone_ground(?x,?y)],
        tenured(?x,?y) <- [tenured_ground(?x,?y)],
        title(?x,?y) <- [title_ground(?x,?y)],
        undergraduateDegreeFrom(?x,?y) <- [undergraduateDegreeFrom_ground(?x,?y)],
        worksFor(?x,?y) <- [worksFor_ground(?x,?y)],
        researchAssistant(?x,?y) <- [researchAssistant_ground(?x,?y)],
        undergraduateStudent(?x,?y) <- [undergraduateStudent_ground(?x,?y)],

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


    let predicate = args.query_predicate.as_ref().unwrap();
    let query = Query {
        symbol: predicate,
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
                vec![],
            ));
            // println!(
            //     "Micro-streaming result tuples number: {:?}",
            //     result_tuples.len()
            // );
        }

        if args.micro_magic {
            let (time, tuples, _result_tuples) = run_micro_benchmark(
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
                vec![],
            ));
            // println!(
            //     "Micro-magic result tuples number: {:?}",
            //     result_tuples.len()
            // );
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
                result_tuples,
            ));

            // println!(
            //     "Micro-tabling result tuples number: {:?}",
            //     result_tuples.len()
            // );
        }

        if args.ascent {
            let (time, tuples, result_tuples) = run_ascent_benchmark(
                &mut ascent_runtime,
                &integral,
                args.query_source_str.clone(),
                args.query_target_str.clone()
            );
            let mut seen = HashSet::new();
            let converted_result_tuples: Vec<Vec<TypedValue>> = result_tuples
                .into_iter()
                .map(|(a, b)| {
                    vec![
                        TypedValue::from(a),
                        TypedValue::from(b),
                    ]
                })
                .filter(|tuple| seen.insert(tuple.clone()))
                .collect();

            results.push(BenchmarkResult::new(
                "ascent",
                batch.len(),
                integral.len(),
                time,
                tuples,
                converted_result_tuples,
            ));
            // println!(
            //     "Ascent result tuples number: {:?}",
            //     converted_result_tuples.len()
            // );
        }

        // Print progress
        println!("Processed {} edges", integral.len());
    }

    Ok(results)
}
