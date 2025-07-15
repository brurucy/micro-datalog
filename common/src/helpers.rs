use std::collections::{HashMap, HashSet};
use itertools::Itertools;

use datalog_syntax::{Atom, Rule, Term};

pub fn clean_rule(rule: &Rule) -> Rule {
    let mut clean_rule = rule.clone();
    let head_atom_terms: HashSet<_> = rule.head.terms.clone().into_iter().collect();
    let body_atoms: Vec<_> = rule.body.iter().enumerate().collect();
    let body_atom_terms: HashMap<_, _> = rule
        .body
        .iter()
        .map(|atom| (atom, atom.terms.clone().into_iter().collect::<HashSet<_>>()))
        .collect();

    body_atoms.iter().for_each(|(position, atom)| {
        let terms = body_atom_terms.get(atom).unwrap();
        if terms.intersection(&head_atom_terms).collect_vec().len() == 0 {
            clean_rule.body.remove(*position);
        }
    });

    clean_rule
}

pub fn canonicalize_rule(rule: &Rule) -> Rule {
    if rule.body.is_empty() {
        return rule.clone();
    }

    let mut ordered_atoms = Vec::new();
    let mut remaining_atoms = rule.body.clone();
    let mut available_variables = HashSet::new();

    fn get_variables(atom: &Atom) -> HashSet<String> {
        atom.terms
            .iter()
            .filter_map(|term| match term {
                Term::Variable(var) => Some(var.clone()),
                Term::Constant(_) => None,
            })
            .collect()
    }

    if let Some(first_atom) = remaining_atoms.first() {
        let first_vars = get_variables(first_atom);
        available_variables.extend(first_vars);
        ordered_atoms.push(first_atom.clone());
        remaining_atoms.remove(0);
    }

    while !remaining_atoms.is_empty() {
        let mut best_atom_idx = None;
        let mut best_score = 0;

        for (idx, atom) in remaining_atoms.iter().enumerate() {
            let atom_vars = get_variables(atom);
            let shared_vars = atom_vars.intersection(&available_variables).count();

            if shared_vars > best_score {
                best_score = shared_vars;
                best_atom_idx = Some(idx);
            }
        }

        if let Some(idx) = best_atom_idx {
            let atom = remaining_atoms.remove(idx);
            let atom_vars = get_variables(&atom);
            available_variables.extend(atom_vars);
            ordered_atoms.push(atom);
        } else {
            let atom = remaining_atoms.remove(0);
            let atom_vars = get_variables(&atom);
            available_variables.extend(atom_vars);
            ordered_atoms.push(atom);
        }
    }

    Rule {
        head: rule.head.clone(),
        body: ordered_atoms,
        id: rule.id,
    }
}