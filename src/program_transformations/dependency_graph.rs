use std::collections::HashMap;
use datalog_syntax::{Program, Rule};
use petgraph::{algo, Directed};
use petgraph::graphmap::{DiGraphMap, GraphMap};

type RuleGraph<'a> = GraphMap<&'a Rule, bool, Directed>;

pub fn generate_rule_dependency_graph<'a>(program: &Vec<Rule>) -> RuleGraph {
    let mut output = DiGraphMap::new();
    let mut idb_relations = HashMap::new();
    for rule in program {
        idb_relations.insert(rule.clone().head.symbol, rule);
        output.add_node(rule);
    }
    for rule in program {
        for body_atom in &rule.body {
            if let Some(body_atom_rule) = idb_relations.get(&body_atom.symbol) {
                output.add_edge(body_atom_rule, rule, true);
            }
        }
    }
    return output;
}

pub fn stratify<'a>(rule_graph: &'a RuleGraph) -> Vec<Vec<&'a Rule>> {
    let sccs = algo::kosaraju_scc(&rule_graph);

    return sccs;
}

pub fn sort_program(program: &Program) -> Program {
    let rule_graph = generate_rule_dependency_graph(&program.inner);
    let stratification = stratify(&rule_graph)
        .into_iter()
        .rev()
        .flat_map( | program| {
            program
        })
        .cloned()
        .collect();

    return Program {
        inner: stratification
    }
}
