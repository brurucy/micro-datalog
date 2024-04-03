use ahash::HashSet;
use datalog_syntax::{Program, Rule};
use petgraph::graphmap::{DiGraphMap, GraphMap};
use petgraph::visit::{EdgeIndexable, IntoNodeReferences};
use petgraph::{algo, Directed};
use std::collections::HashMap;

type RuleGraph<'a> = GraphMap<usize, bool, Directed>;

pub fn generate_rule_dependency_graph<'a>(program: &Vec<Rule>) -> RuleGraph {
    let mut output = DiGraphMap::new();
    let mut idb_relations: HashMap<String, HashSet<usize>> = Default::default();
    let mut rule_to_node_index: HashMap<usize, usize> = Default::default();
    for rule in program {
        let current_rule_index = output.add_node(rule.id);
        rule_to_node_index
            .entry(rule.id)
            .or_insert(current_rule_index);
        idb_relations
            .entry(rule.clone().head.symbol)
            .or_default()
            .insert(current_rule_index);
    }
    for rule in program {
        let current_rule_node_index = rule_to_node_index.get(&rule.id).unwrap();

        for body_atom in &rule.body {
            if let Some(dependents) = idb_relations.get(&body_atom.symbol) {
                for dependent in dependents {
                    output.add_edge(*dependent, *current_rule_node_index, true);
                }
            }
        }
    }

    return output;
}

pub fn stratify<'a>(rule_graph: &'a RuleGraph) -> Vec<Vec<usize>> {
    let sccs = algo::kosaraju_scc(&rule_graph);

    return sccs;
} // make a test

pub fn sort_program(program: &Program) -> Program {
    let rule_graph = generate_rule_dependency_graph(&program.inner);
    let stratification = stratify(&rule_graph)
        .into_iter()
        .rev()
        .flat_map(|ids| ids)
        .map(|id| program.inner.get(id).unwrap())
        .cloned()
        .collect();

    return Program {
        inner: stratification,
    };
}

#[cfg(test)]
mod test {
    use datalog_rule_macro::program;
    use datalog_syntax::*;
    use pretty_assertions::assert_eq;

    use crate::program_transformations::dependency_graph::sort_program;

    #[test]
    fn test_sort_program() {
        let program = program! {
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
            tc(?x, ?y) <- [e(?x, ?y)],
        };

        let expected_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };

        let actual_program = sort_program(&program);

        assert_eq!(expected_program, actual_program)
    }
}
