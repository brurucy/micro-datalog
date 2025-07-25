use std::collections::HashSet;

pub struct SimpleDatalogParser {
    ontology_classes: HashSet<String>,
    output_facts: Vec<String>,
}

impl SimpleDatalogParser {
    pub fn new() -> Self {
        let mut parser = SimpleDatalogParser {
            ontology_classes: HashSet::new(),
            output_facts: Vec::new(),
        };
        
        // Pre-populate known LUBM ontology classes
        parser.populate_ontology_classes();
        parser
    }
    
    fn populate_ontology_classes(&mut self) {
        let classes = vec![
            "Person", "Professor", "FullProfessor", "AssociateProfessor", "AssistantProfessor",
            "University", "Course", "GraduateCourse", "Department", "Employee", "Faculty",
            "Student", "GraduateStudent", "TeachingAssistant", "Chair", "Dean", "Director",
            "Organization", "College", "Institute", "Program", "ResearchGroup",
            "Publication", "Article", "Book", "ConferencePaper", "JournalArticle", 
            "TechnicalReport", "Manual", "Software", "Specification",
            "AdministrativeStaff", "ClericalStaff", "SystemsStaff", "PostDoc", "Lecturer",
            "VisitingProfessor", "UndergraduateStudent", "ResearchAssistant",
            "Work", "Research", "Schedule", "UnofficialPublication"
        ];
        
        for class in classes {
            self.ontology_classes.insert(class.to_string());
        }
    }
    
    pub fn parse_to_datalog_format(&mut self, rdf_data: &str) -> Vec<String> {
        for line in rdf_data.lines() {
            if line.trim().is_empty() || line.contains("genid") {
                continue;
            }
            
            if let Some(triple) = self.parse_triple(line) {
                self.process_triple(&triple);
            }
        }
        
        self.output_facts.clone()
    }
    
    fn parse_triple(&self, line: &str) -> Option<(String, String, String)> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() >= 3 {
            let subject = parts[0].trim_matches('<').trim_matches('>').to_string();
            let predicate = parts[1].trim_matches('<').trim_matches('>').to_string();
            let object = parts[2].trim_matches('<').trim_matches('>').trim_matches('"').to_string();
            Some((subject, predicate, object))
        } else {
            None
        }
    }
    
    fn process_triple(&mut self, triple: &(String, String, String)) {
        let (subject, predicate, object) = triple;
        
        // Skip schema/ontology triples
        if self.is_schema_triple(subject, predicate, object) {
            return;
        }
        
        match predicate.as_str() {
            "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" => {
                self.handle_type_assertion(subject, object);
            },
            _ => {
                self.handle_property_relationship(subject, predicate, object);
            }
        }
    }
    
    fn is_schema_triple(&self, subject: &str, predicate: &str, object: &str) -> bool {
        // Skip if object is a meta-class (indicates schema)
        if object == "http://www.w3.org/2002/07/owl#Class" ||
           object == "http://www.w3.org/2002/07/owl#ObjectProperty" ||
           object == "http://www.w3.org/2002/07/owl#DatatypeProperty" {
            return true;
        }
        
        // Skip rdfs/owl schema predicates
        if predicate.contains("rdfs:") || predicate.contains("owl:") ||
           predicate.contains("subClassOf") || predicate.contains("subPropertyOf") ||
           predicate.contains("domain") || predicate.contains("range") {
            return true;
        }
        
        // Skip label properties  
        if predicate.contains("label") {
            return true;
        }
        
        false
    }
    
    fn handle_type_assertion(&mut self, individual_uri: &str, class_uri: &str) {
        let individual_name = self.extract_name(individual_uri);
        let class_name = self.extract_name(class_uri);
        
        // Only process if it's a known ontology class (not meta-classes)
        if self.ontology_classes.contains(&class_name) {
            let fact = format!("{} {} .", class_name, individual_name);
            self.output_facts.push(fact);
        }
    }
    
    fn handle_property_relationship(&mut self, subject_uri: &str, predicate_uri: &str, object_uri: &str) {
        // Skip data properties (strings) and schema properties
        if object_uri.starts_with('"') || 
           predicate_uri.contains("rdfs:") || 
           predicate_uri.contains("owl:") ||
           predicate_uri.contains("emailAddress") ||
           predicate_uri.contains("telephone") ||
           predicate_uri.contains("name") ||
           predicate_uri.contains("researchInterest") {
            return;
        }
        
        let subject_name = self.extract_name(subject_uri);
        let predicate_name = self.extract_name(predicate_uri);
        let object_name = self.extract_name(object_uri);
        
        let fact = format!("{} {} {}", predicate_name, subject_name, object_name);
        self.output_facts.push(fact);
    }
    
    fn extract_name(&self, uri: &str) -> String {
        // Extract name from URI: remove everything before # or last /
        if let Some(hash_pos) = uri.rfind('#') {
            uri[hash_pos + 1..].to_string()
        } else if let Some(slash_pos) = uri.rfind('/') {
            uri[slash_pos + 1..].to_string()
        } else {
            uri.to_string()
        }
    }
    
    pub fn get_facts(&self) -> &Vec<String> {
        &self.output_facts
    }
}

// Usage function
fn main() {
    let rdf_data = r#"
<http://www.Department0.University0.edu/FullProfessor3> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#worksFor> <http://www.Department0.University0.edu> .
<http://www.Department0.University0.edu/FullProfessor3> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#emailAddress> "FullProfessor3@Department0.University0.edu" .
<http://www.Department0.University0.edu/FullProfessor3> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#telephone> "xxx-xxx-xxxx" .
<http://www.Department0.University0.edu/FullProfessor3> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#researchInterest> "Research12" .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#FullProfessor> .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#name> "FullProfessor4" .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#teacherOf> <http://www.Department0.University0.edu/Course6> .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#teacherOf> <http://www.Department0.University0.edu/GraduateCourse6> .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#teacherOf> <http://www.Department0.University0.edu/GraduateCourse7> .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#undergraduateDegreeFrom> <http://www.University608.edu> .
<http://www.University608.edu> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#University> .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#mastersDegreeFrom> <http://www.University737.edu> .
<http://www.University737.edu> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#University> .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#doctoralDegreeFrom> <http://www.University143.edu> .
<http://www.University143.edu> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#University> .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#worksFor> <http://www.Department0.University0.edu> .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#emailAddress> "FullProfessor4@Department0.University0.edu" .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#telephone> "xxx-xxx-xxxx" .
<http://www.Department0.University0.edu/FullProfessor4> <http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#researchInterest> "Research7" .
"#;

    let mut parser = SimpleDatalogParser::new();
    let facts = parser.parse_to_datalog_format(rdf_data);
    
    // println!("Generated Datalog facts:");
    // for fact in facts {
    //     println!("{}", fact);
    // }
}

// Simple function to parse RDF line into Datalog format
pub fn parse_data(line: &str) -> Option<(String, String, String)> {
    // Parse the RDF triple
    let parts: Vec<&str> = line.split_whitespace().collect();
    if parts.len() < 3 {
        return None;
    }
    
    let subject = parts[0].trim_matches('<').trim_matches('>');
    let predicate = parts[1].trim_matches('<').trim_matches('>');
    let object = parts[2].trim_matches('<').trim_matches('>').trim_matches('"');
    
    // Skip schema/ontology data
    if is_schema_triple(subject, predicate, object) {
        return None;
    }
    
    // Handle type assertions (X rdf:type Class)
    if predicate == "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" {
        let individual_name = extract_name(subject);
        let class_name = extract_name(object);
        
        // Only process known ontology classes
        if is_known_class(&class_name) {
            return Some((class_name, individual_name, String::new())); // Empty string for unary predicates
        }
    }
    // Handle property relationships (X property Y)
    else {
        // Skip data properties (strings) and schema properties
        if object.starts_with('"') || 
           predicate.contains("rdfs:") || 
           predicate.contains("owl:") ||
           predicate.contains("emailAddress") ||
           predicate.contains("telephone") ||
           predicate.contains("name") ||
           predicate.contains("researchInterest") {
            return None;
        }
        
        let subject_name = extract_name(subject);
        let predicate_name = extract_name(predicate);
        let object_name = extract_name(object);
        
        return Some((predicate_name, subject_name, object_name));
    }
    
    None
}

fn is_schema_triple(subject: &str, predicate: &str, object: &str) -> bool {
    // Skip if object is a meta-class (indicates schema)
    if object == "http://www.w3.org/2002/07/owl#Class" ||
       object == "http://www.w3.org/2002/07/owl#ObjectProperty" ||
       object == "http://www.w3.org/2002/07/owl#DatatypeProperty" {
        return true;
    }
    
    // Skip rdfs/owl schema predicates
    if predicate.contains("rdfs:") || predicate.contains("owl:") ||
       predicate.contains("subClassOf") || predicate.contains("subPropertyOf") ||
       predicate.contains("domain") || predicate.contains("range") ||
       predicate.contains("label") {
        return true;
    }
    
    false
}

fn is_known_class(class_name: &str) -> bool {
    let known_classes = [
        "Person", "Professor", "FullProfessor", "AssociateProfessor", "AssistantProfessor",
        "University", "Course", "GraduateCourse", "Department", "Employee", "Faculty",
        "Student", "GraduateStudent", "TeachingAssistant", "Chair", "Dean", "Director",
        "Organization", "College", "Institute", "Program", "ResearchGroup",
        "Publication", "Article", "Book", "ConferencePaper", "JournalArticle",
        "TechnicalReport", "Manual", "Software", "Specification",
        "AdministrativeStaff", "ClericalStaff", "SystemsStaff", "PostDoc", "Lecturer",
        "VisitingProfessor", "UndergraduateStudent", "ResearchAssistant",
        "Work", "Research", "Schedule", "UnofficialPublication"
    ];
    
    known_classes.contains(&class_name)
}

fn extract_name(uri: &str) -> String {
    if let Some(hash_pos) = uri.rfind('#') {
        uri[hash_pos + 1..].to_string()
    } else if let Some(slash_pos) = uri.rfind('/') {
        uri[slash_pos + 1..].to_string()
    } else {
        uri.to_string()
    }
}

// Alternative version if you want to separate type assertions from properties
pub fn parse_data_separated(line: &str) -> Option<DatalogTriple> {
    let parts: Vec<&str> = line.split_whitespace().collect();
    if parts.len() < 3 {
        return None;
    }
    
    let subject = parts[0].trim_matches('<').trim_matches('>');
    let predicate = parts[1].trim_matches('<').trim_matches('>');
    let object = parts[2].trim_matches('<').trim_matches('>').trim_matches('"');
    
    if is_schema_triple(subject, predicate, object) {
        return None;
    }
    
    if predicate == "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" {
        let individual_name = extract_name(subject);
        let class_name = extract_name(object);
        
        if is_known_class(&class_name) {
            return Some(DatalogTriple::TypeAssertion {
                class: class_name,
                individual: individual_name,
            });
        }
    } else {
        if object.starts_with('"') || 
           predicate.contains("rdfs:") || 
           predicate.contains("owl:") ||
           predicate.contains("emailAddress") ||
           predicate.contains("telephone") ||
           predicate.contains("name") ||
           predicate.contains("researchInterest") {
            return None;
        }
        
        let subject_name = extract_name(subject);
        let predicate_name = extract_name(predicate);
        let object_name = extract_name(object);
        
        return Some(DatalogTriple::Property {
            predicate: predicate_name,
            subject: subject_name,
            object: object_name,
        });
    }
    
    None
}

#[derive(Debug)]
pub enum DatalogTriple {
    TypeAssertion {
        class: String,
        individual: String,
    },
    Property {
        predicate: String,
        subject: String,
        object: String,
    },
}

impl DatalogTriple {
    pub fn to_datalog_string(&self) -> String {
        match self {
            DatalogTriple::TypeAssertion { class, individual } => {
                format!("{} {} .", class, individual)
            },
            DatalogTriple::Property { predicate, subject, object } => {
                format!("{} {} {}", predicate, subject, object)
            },
        }
    }
}
