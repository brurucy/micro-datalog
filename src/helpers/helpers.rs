use crate::engine::datalog::{MicroRuntime, Strategy};
use crate::{engine::storage::RelationStorage, program_transformations::adorned_atom::*};
use datalog_rule_macro::program;
use datalog_syntax::*;
use indexmap::IndexSet;
use rand::prelude::*;
use rand::seq::SliceRandom;
use std::collections::{HashMap, HashSet};

pub fn get_rules_for_predicate<'a>(program: &'a Program, pred_symbol: &str) -> Vec<&'a Rule> {
    program
        .inner
        .iter()
        .filter(|rule| rule.head.symbol == pred_symbol)
        .collect()
}

pub fn is_derived_predicate(program: &Program, pred_symbol: &str) -> bool {
    program
        .inner
        .iter()
        .any(|rule| rule.head.symbol == pred_symbol)
}

pub fn split_program(program: Program) -> (Program, Program) {
    let mut nonrecursive = vec![];
    let mut recursive = vec![];

    let idb_relations = program
        .inner
        .iter()
        .map(|r| r.head.symbol.as_str())
        .collect::<IndexSet<_>>();

    program.inner.iter().for_each(|rule| {
        if rule
            .body
            .iter()
            .map(|body_atom| &body_atom.symbol)
            .any(|body_atom_symbol| idb_relations.contains(body_atom_symbol.as_str()))
        {
            recursive.push(rule.clone());
        } else {
            nonrecursive.push(rule.clone());
        }
    });

    (Program::from(nonrecursive), Program::from(recursive))
}

pub fn compute_bound_vars_at_position(
    rule: &Rule,
    initial_bound_vars: &HashSet<String>,
    current_pos: usize,
    last_derived_pos: usize,
    program: &Program,
) -> HashSet<String> {
    let mut bound_vars = initial_bound_vars.clone();

    // Process predicates sequentially
    for i in last_derived_pos..current_pos {
        let body_atom = &rule.body[i];

        if is_derived_predicate(program, &body_atom.symbol) {
            // Create an adorned atom for this position
            let adorned_body_atom = AdornedAtom::from_atom_and_bound_vars(body_atom, &bound_vars);

            if adorned_body_atom
                .adornment
                .iter()
                .any(|a| matches!(a, Adornment::Bound))
            {
                for term in &body_atom.terms {
                    if let Term::Variable(var) = term {
                        bound_vars.insert(var.clone());
                    }
                }
            }
        } else {
            // If it's a base predicate and at least one term is bound, add all terms to bound vars
            let has_bound_terms = body_atom.terms.iter().any(|term| {
                match term {
                    Term::Variable(var) => bound_vars.contains(var),
                    Term::Constant(_) => true, // Constants are always considered bound
                }
            });

            if has_bound_terms {
                // Add all variables from this base predicate to bound vars
                for term in &body_atom.terms {
                    if let Term::Variable(var) = term {
                        bound_vars.insert(var.clone());
                    }
                }
            }
        }

    }

    bound_vars
}

/// Creates an adorned version of the head predicate
pub fn create_adorned_head_predicate(adorned_head: AdornedAtom) -> Atom {
    Atom {
        symbol: format!(
            "{}_{}",
            //original_head.symbol,
            adorned_head.atom.symbol,
            adorned_head.get_pattern_string()
        ),
        terms: adorned_head.atom.terms.clone(),
        sign: true,
    }
}

pub fn make_magic_predicate_name(adorned_atom: &AdornedAtom) -> String {
    format!(
        "magic_{}_{}",
        adorned_atom.atom.symbol,
        adorned_atom.get_pattern_string()
    )
}

/// Modifies a body predicate with its adornment
pub fn adorn_body_predicate(original_body: &Atom, adorned_body_atom: &AdornedAtom) -> Atom {
    Atom {
        symbol: format!(
            "{}_{}",
            adorned_body_atom.atom.symbol,
            adorned_body_atom.get_pattern_string()
        ),
        terms: adorned_body_atom.atom.terms.clone(),
        sign: original_body.sign,
    }
}

pub fn get_bound_terms_from_adorned(adorned: &AdornedAtom) -> Vec<Term> {
    adorned
        .atom
        .terms
        .iter()
        .zip(adorned.adornment.iter())
        .filter_map(|(term, adornment)| match adornment {
            Adornment::Bound => Some(term.clone()),
            Adornment::Free => None,
        })
        .collect()
}

// Use when we need variable names as strings
pub fn get_bound_vars_from_adorned_atom(adorned: &AdornedAtom) -> HashSet<String> {
    get_bound_terms_from_adorned(adorned)
        .into_iter()
        .filter_map(|term| match term {
            Term::Variable(var) => Some(var),
            _ => None,
        })
        .collect()
}

pub fn load_initial_edges(graph: &RelationStorage, ratio: f64) -> Vec<(String, String)> {
    let all_edges = graph.get_all_edges("e".to_string());
    let initial_count = (all_edges.len() as f64 * ratio) as usize;

    let mut rng = rand::thread_rng();
    let mut edges = all_edges.clone();
    edges.shuffle(&mut rng);

    edges.drain(0..initial_count).collect()
}

pub fn load_remaining_edges(graph: &RelationStorage) -> Vec<(String, String)> {
    let all_edges = graph.get_all_edges("e".to_string());
    let initial_count = (all_edges.len() as f64 * 0.2) as usize; // 20% initial

    let mut rng = rand::thread_rng();
    let mut edges = all_edges.clone();
    edges.shuffle(&mut rng);

    edges.drain(initial_count..).collect()
}

/// Calculate out-degree for each node in the graph
pub fn calculate_out_degrees(storage: &RelationStorage, node: String) -> HashMap<String, usize> {
    let mut degrees = HashMap::new();

    for edge in storage.get_all_edges(node) {
        let (src, _) = edge;
        *degrees.entry(src).or_insert(0) += 1;
    }

    degrees
}

/// Calculate in-degree for each node in the graph
pub fn calculate_in_degrees(storage: &RelationStorage, node: String) -> HashMap<String, usize> {
    let mut degrees = HashMap::new();

    for edge in storage.get_all_edges(node) {
        let (_, dst) = edge;
        *degrees.entry(dst).or_insert(0) += 1;
    }

    degrees
}

/// Get all unique nodes in the graph
pub fn get_all_nodes(storage: &RelationStorage, node: String) -> HashSet<String> {
    let mut nodes = HashSet::new();

    for (src, dst) in storage.get_all_edges(node) {
        nodes.insert(src);
        nodes.insert(dst);
    }

    nodes
}

/// Randomly sample n items from a vector, or return all if fewer than n
pub fn sample<T: Clone>(items: Vec<T>, n: usize) -> Vec<T> {
    if items.len() <= n {
        return items;
    }

    let mut rng = rand::rng();
    let mut indices: Vec<usize> = (0..items.len()).collect();
    indices.shuffle(&mut rng);

    indices.iter().take(n).map(|&i| items[i].clone()).collect()
}

/// Split edges into initial and remaining sets for streaming tests
pub fn split_edges_for_streaming(
    storage: &RelationStorage,
    node: String,
    initial_ratio: f64,
) -> (Vec<(String, String)>, Vec<(String, String)>) {
    let all_edges = storage.get_all_edges(node);
    let initial_count = (all_edges.len() as f64 * initial_ratio) as usize;

    let mut rng = rand::rng();
    let mut edges = all_edges.clone();
    edges.shuffle(&mut rng);

    let initial = edges.drain(0..initial_count).collect();
    let remaining = edges;

    (initial, remaining)
}

pub fn get_pred_name_and_binding_pattern(pred_symbol: &str) -> (String, Vec<String>) {
    // Split the symbol by "_" to separate the predicate name from the binding pattern
    let parts: Vec<&str> = pred_symbol.split('_').collect();

    if parts.len() >= 2 {
        // Get the predicate name (everything except the last part)
        let predicate_name = parts[..parts.len() - 1].join("_");
        let binding_pattern_str = parts[parts.len() - 1];

        // Check that the binding pattern only contains 'b' and 'f' characters
        if binding_pattern_str.chars().all(|c| c == 'b' || c == 'f') {
            let binding_pattern = binding_pattern_str.chars().map(|c| c.to_string()).collect();
            (predicate_name, binding_pattern)
        } else {
            // If the binding pattern contains invalid characters, treat as non-adorned
            (pred_symbol.to_string(), vec![])
        }
    } else {
        (pred_symbol.to_string(), vec![])
    }
}

fn get_query_preds_with_all_binding_patterns(
    query_original: &Query,
    magic_program: &Program,
) -> Vec<String> {
    let mut query_preds = Vec::new();

    // Collect all predicates from rule heads that match the query pattern
    for rule in &magic_program.inner {
        let head_symbol = &rule.head.symbol;

        // Split the symbol by "_" to separate the predicate name from the binding pattern
        let parts: Vec<&str> = head_symbol.split('_').collect();

        if parts.len() >= 2 {
            // Get the predicate name (everything except the last part)
            let predicate_name = parts[..parts.len() - 1].join("_");
            let binding_pattern = parts[parts.len() - 1];

            // Check if this predicate matches the original query predicate
            if predicate_name == query_original.symbol
                && binding_pattern.len() == query_original.matchers.len()
            {
                query_preds.push(head_symbol.to_string());
            }
        }
    }
    query_preds
}

pub fn get_queries_with_all_binding_patterns<'a>(
    query_original: &'a Query<'a>,
    magic_program: &'a Program,
) -> Vec<Query<'static>> {
    let mut queries = Vec::new();

    for pred_adorned in get_query_preds_with_all_binding_patterns(query_original, magic_program) {
        //println!("pred==={:?}", pred_adorned);
        let (_pred_name, binding_pattern) = get_pred_name_and_binding_pattern(&pred_adorned);
        if binding_pattern.len() == 0 {
            continue;
        }
        let new_query = Query {
            matchers: query_original.matchers.clone(),
            symbol: pred_adorned.leak(),
        };

        queries.push(new_query);
    }
    queries
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::helpers::helpers::split_program;
    use datalog_rule_macro::{program, rule};

    // Helper function to create a set of strings
    fn str_set(strs: &[&str]) -> HashSet<String> {
        strs.iter().map(|s| s.to_string()).collect()
    }
    /*
    #[test]
    fn test_derived_predicate_fb_pattern() {
        // Rule: path(X, Y) :- node(X), path(Z, X), edge(Z, Y)
        let rule = rule! { path(?x, ?y) <- [node(?x), path(?z, ?x), edge(?z, ?y)] };
        let program = program! {
            path(?x, ?y) <- [edge(?x, ?y)],
            path(?x, ?y) <- [node(?x), path(?z, ?x), edge(?z, ?y)]
        };

        // Y is initially bound (fb pattern)
        let initial_bound_vars = str_set(&["y"]);

        // Position 1: node(X) processed, but no connection to bound vars yet
        let bound_vars = compute_bound_vars_at_position(&program, &rule, 1, &initial_bound_vars);
        assert_eq!(bound_vars, str_set(&["y"]));

        // Position 2: path(Z, X) processed, X connects to Y? No direct connection
        let bound_vars = compute_bound_vars_at_position(&program, &rule, 2, &initial_bound_vars);
        assert_eq!(bound_vars, str_set(&["y"]));

        // Position 3: edge(Z, Y) processed, Y was bound, so Z becomes bound
        let bound_vars = compute_bound_vars_at_position(&program, &rule, 3, &initial_bound_vars);
        assert_eq!(bound_vars, str_set(&["y", "z"]));
    }*/

    #[test]
    fn test_split_program_complex() {
        let stratified_program = program! {
            // Stratum 1: Base rule
            base(?x, ?y) <- [edge(?x, ?y)],

            // Stratum 2: Derived rule depends on Stratum 1
            derived(?x, ?y) <- [base(?x, ?y)],
            derived(?x, ?z) <- [base(?x, ?y), derived(?y, ?z)],

            // Stratum 3: Another level of derivation
            top(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)],
        };

        let expected_nonrecursive_program = program! {
            base(?x, ?y) <- [edge(?x, ?y)],
        };

        let expected_recursive_program = program! {
            derived(?x, ?y) <- [base(?x, ?y)],
            derived(?x, ?z) <- [base(?x, ?y), derived(?y, ?z)],
            top(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)],
        };

        let (nonrecursive_program, recursive_program) = split_program(stratified_program);

        assert_eq!(expected_nonrecursive_program, nonrecursive_program);
        assert_eq!(expected_recursive_program, recursive_program);
    }

    // #[test]
    // fn test_create_adorned_head_predicate() {
    //     let original = Atom {
    //         symbol: "p".to_string(),
    //         terms: vec![
    //             Term::Variable("x".to_string()),
    //             Term::Variable("y".to_string()),
    //         ],
    //         sign: true,
    //     };

    //     let adorned = AdornedAtom {
    //         atom: original.clone(),
    //         adornment: vec![Adornment::Bound, Adornment::Free],
    //     };

    //     let result = create_adorned_head_predicate(&original, &adorned.adornment);
    //     assert_eq!(result.symbol, "p_bf");
    // }

    #[test]
    fn test_get_bound_vars_from_adorned() {
        let atom = Atom {
            symbol: "p".to_string(),
            terms: vec![
                Term::Variable("x".to_string()),
                Term::Variable("y".to_string()),
            ],
            sign: true,
        };

        let adorned = AdornedAtom {
            atom: atom,
            adornment: vec![Adornment::Bound, Adornment::Free],
        };

        let bound_vars = get_bound_vars_from_adorned_atom(&adorned);
        assert!(bound_vars.contains("x"));
        assert!(!bound_vars.contains("y"));
    }

    #[test]
    fn test_split_program() {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(? x, ?z) <- [e(? x, ?y), tc(? y, ?z)]
        };

        let expected_nonrecursive_program = program! { tc(?x, ?y) <- [e(?x, ?y)] };
        let expected_recursive_program = program! { tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)] };

        let (actual_nonrecursive_program, actual_recursive_program) = split_program(program);

        assert_eq!(expected_nonrecursive_program, actual_nonrecursive_program);
        assert_eq!(expected_recursive_program, actual_recursive_program);
    }
}
