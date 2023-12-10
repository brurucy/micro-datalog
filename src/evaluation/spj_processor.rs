use std::time::Instant;
use crate::engine::ephemeral_storage::{EphemeralStorage, EphemeralValue};
use crate::engine::storage::RelationStorage;
use ahash::{HashMap, HashSet};
use datalog_syntax::{AnonymousGroundAtom, Rule, Term, TypedValue, Variable};
use crate::evaluation::spj_processor::Instruction::{Join, Project};
use rayon::prelude::*;

// This implements a minimal SPJ (Select, Project, Join) processor

pub type Column = usize;
pub type Value = TypedValue;
pub type Symbol = String;

#[derive(PartialEq, Debug, Clone)]
enum ProjectionInput {
    Column(Column),
    Value(Value),
}

#[derive(PartialEq, Debug, Clone)]
enum Instruction {
    Move(Symbol),
    Select(Symbol, Column, Value),
    Project(Symbol, Vec<ProjectionInput>),
    Join(Symbol, Symbol, Vec<(usize, usize)>),
}

#[derive(PartialEq, Debug, Clone)]
struct Stack {
    inner: Vec<Instruction>,
}

fn stringify_selection(selection: &Instruction) -> String {
    return match selection {
        Instruction::Select(symbol, column, value) => format!("{}_{}={:?}", symbol, column, value),
        _ => unreachable!(),
    };
}

fn stringify_join(join: &Instruction) -> String {
    return match join {
        Instruction::Join(left_symbol, right_symbol, join_keys) => {
            let join_keys_format = join_keys
                .iter()
                .map(|(left_column, right_column)| format!("{}={}", left_column, right_column))
                .collect::<Vec<_>>()
                .join("_");

            format!("{}_{}_{}", left_symbol, right_symbol, join_keys_format)
        },
        _ => unreachable!(),
    };
}

fn get_selection(symbol: &str, terms: &Vec<Term>) -> Option<Instruction> {
    let selection: Vec<Instruction> = terms
        .iter()
        .enumerate()
        .filter(|(_, term)| match term {
            Term::Variable(_) => false,
            Term::Constant(_) => true,
        })
        .map(|(idx, constant)| {
            let constant_value = match constant {
                Term::Constant(inner) => inner,
                _ => unreachable!(),
            };

            return Instruction::Select(symbol.to_string(), idx, constant_value.clone());
        })
        .collect();

    return selection.get(0).cloned();
}

fn get_variables(terms: &Vec<Term>) -> HashMap<Variable, usize> {
    terms
        .clone()
        .into_iter()
        .enumerate()
        .filter(|(_, term)| match term {
            Term::Variable(_) => true,
            Term::Constant(_) => false,
        })
        .map(|(idx, term)| match term {
            Term::Variable(name) => (name, idx),
            Term::Constant(_) => unreachable!(),
        })
        .collect()
}

fn get_join(
    left_terms: &Vec<Term>,
    right_terms: &Vec<Term>,
    left_symbol: &str,
    right_symbol: &str,
) -> Option<Instruction> {
    let left_variable_map = get_variables(left_terms);
    let right_variable_map = get_variables(right_terms);

    let mut join_keys = vec![];

    for (variable_name, left_position) in left_variable_map {
        if let Some(right_position) = right_variable_map.get(&variable_name) {
            join_keys.push((left_position, *right_position));
        }
    }

    if !join_keys.is_empty() {
        return Some(Join(
            left_symbol.to_string(),
            right_symbol.to_string(),
            join_keys
        ))
    }

    return None;
}

fn get_projection(rule: &Rule) -> Instruction {
    let projection_variable_targets: HashSet<String> = rule
        .head
        .terms
        .iter()
        .filter(|term| match term {
            Term::Variable(_) => true,
            Term::Constant(_) => false,
        })
        .map(|term| match term {
            Term::Variable(name) => name.clone(),
            Term::Constant(_) => unreachable!(),
        })
        .collect();

    let mut seen: HashSet<_> = Default::default();
    let mut variable_location_assuming_joins_are_natural: HashMap<Variable, usize> =
        Default::default();

    let mut position_assuming_joins_are_natural = 0;

    rule.body.iter().for_each(|body_atom| {
        body_atom.terms.iter().for_each(|term| {
            match term {
                Term::Variable(name) => {
                    if !seen.contains(name) {
                        seen.insert(name.clone());

                        if projection_variable_targets.contains(name) {
                            variable_location_assuming_joins_are_natural
                                .insert(name.clone(), position_assuming_joins_are_natural);
                        }
                    }
                }
                Term::Constant(_) => {}
            }

            position_assuming_joins_are_natural += 1;
        });
    });

    let projection = rule
        .head
        .terms
        .iter()
        .map(|term| match term {
            Term::Variable(name) => ProjectionInput::Column(
                *variable_location_assuming_joins_are_natural
                    .get(name)
                    .unwrap(),
            ),
            Term::Constant(value) => ProjectionInput::Value(value.clone()),
        })
        .collect();

    Project(rule.head.symbol.clone(), projection)
}

impl From<Rule> for Stack {
    fn from(rule: Rule) -> Self {
        let mut operations = vec![];

        let mut body_iter = rule.body.iter().peekable();
        let mut last_join_result_name = None;
        let mut last_join_terms = vec![];
        while let Some(current_atom) = body_iter.next() {
            if let Some(next_atom) = body_iter.peek() {
                let mut left_symbol = current_atom.symbol.clone();
                let mut left_terms = &current_atom.terms;
                let mut right_symbol = next_atom.symbol.clone();
                let right_terms = &next_atom.terms;

                if last_join_result_name.is_none() {
                    if let Some(selection) = get_selection(&left_symbol, &current_atom.terms) {
                        left_symbol = stringify_selection(&selection);

                        operations.push(selection);
                    } else {
                        operations.push(Instruction::Move(left_symbol.clone()));
                    }
                } else {
                    left_symbol = last_join_result_name.clone().unwrap();
                    left_terms = &last_join_terms;
                }

                if let Some(selection) = get_selection(&right_symbol, right_terms) {
                    right_symbol = stringify_selection(&selection);

                    operations.push(selection);
                } else {
                    operations.push(Instruction::Move(right_symbol.clone()));
                }

                if let Some(binary_join) =
                    get_join(&left_terms, right_terms, &left_symbol, &right_symbol)
                {
                    last_join_result_name = Some(stringify_join(&binary_join));
                    last_join_terms = left_terms.clone();
                    last_join_terms.extend(right_terms.clone());

                    operations.push(binary_join);
                }
            } else {
                if operations.is_empty() {
                    operations.push(Instruction::Move(current_atom.symbol.clone()));
                }

                let projection = get_projection(&rule);

                operations.push(projection)
            }
        }

        /*println!("Rule: {:?}", &rule);
        println!("CallStack:");
        for operation in &operations {
            println!("\t{:?}", operation);
        }*/

        Stack { inner: operations }
    }
}

pub struct RuleEvaluator<'a> {
    rule: &'a Rule,
    facts_storage: &'a RelationStorage,
}

impl<'a> RuleEvaluator<'a> {
    pub(crate) fn new(facts_storage: &'a RelationStorage, rule: &'a Rule) -> Self {
        Self {
            rule,
            facts_storage,
        }
    }
}

impl<'a> RuleEvaluator<'a> {
    pub fn step(&self) -> impl Iterator<Item = AnonymousGroundAtom> + 'a {
        let stack = Stack::from(self.rule.clone());

        let mut out = EphemeralStorage::default();

        // There will always be at least two elements in the stack. Move or Select and then Projection.
        let penultimate_operation = stack.inner.len() - 2;
        let mut relation_symbol_to_be_projected = self.rule.head.symbol.clone();
        let mut grounded_facts: Vec<AnonymousGroundAtom> = vec![];

        for (idx, operation) in stack.inner.iter().enumerate() {
            match operation {
                Instruction::Move(symbol) => {
                    if idx == penultimate_operation {
                        relation_symbol_to_be_projected = symbol.clone();
                    }
                    let moved = out.inner.get(symbol).is_some();
                    // If it has already been moved, then this is a NOOP
                    if !moved {
                        let fact_refs = self.facts_storage.get_relation(symbol);

                        out.borrow_all(
                            symbol,
                            fact_refs
                                .into_iter()
                                .map(|fact| EphemeralValue::FactRef(fact)),
                        )
                    }
                }
                Instruction::Select(symbol, column, value) => {
                    let index_name = stringify_selection(&operation);
                    if idx == penultimate_operation {
                        relation_symbol_to_be_projected = index_name.clone();
                    }
                    // If the index already exists, then this is a NOOP.
                    if out.inner.get(&index_name).is_none() {
                        let target_relation = self.facts_storage.get_relation(symbol);

                        let selection = target_relation
                            .iter()
                            .filter(|fact| fact[*column] == *value)
                            .map(|fact| EphemeralValue::FactRef(fact));

                        out.borrow_all(&index_name, selection)
                    }
                }
                Instruction::Join(left_symbol, right_symbol, join_keys) => {
                    let now = Instant::now();
                    let left_relation = out.get_relation(&left_symbol);
                    let right_relation = out.get_relation(&right_symbol);
                    let join_result_name = stringify_join(operation);
                    if idx == penultimate_operation {
                        relation_symbol_to_be_projected = join_result_name.clone();
                    }

                    let mut join_result = boxcar::vec![];

                    left_relation.into_par_iter().for_each(|left_allocation| {
                        let is_left_product = match left_allocation {
                            EphemeralValue::FactRef(_) => false,
                            EphemeralValue::JoinResult(_) => true
                        };
                        let mut join_key_positions = None;
                        if is_left_product {
                            join_key_positions = Some(join_keys
                                .iter()
                                .map(|(left_column, right_column)| {
                                    let mut cumsum = 0;

                                    let arities = {
                                        match left_allocation {
                                            EphemeralValue::JoinResult(product) => product,
                                            _ => unreachable!()
                                        }
                                    }
                                        .iter()
                                        .map(|fact| fact.len());

                                    let mut left_idx = 0;

                                    for (idx, arity) in arities.enumerate() {
                                        cumsum += arity;

                                        if *left_column < cumsum {
                                            left_idx = idx;
                                            break;
                                        }
                                    }

                                    ((left_idx, cumsum - left_column), right_column)
                                })
                            );
                        }

                        right_relation.into_iter().for_each(|right_allocation| {
                            let right_fact = match right_allocation {
                                EphemeralValue::FactRef(fact) => fact,
                                EphemeralValue::JoinResult(_) => unreachable!(),
                            };

                            match left_allocation {
                                EphemeralValue::FactRef(left_fact) => {
                                    if join_keys
                                        .iter()
                                        .all(|(left_column, right_column)| {
                                            left_fact[*left_column] == right_fact[*right_column]
                                        }) {
                                        {
                                            join_result.push(EphemeralValue::JoinResult(vec![
                                                left_fact,
                                                right_fact,
                                            ]));
                                        }
                                    }
                                }
                                EphemeralValue::JoinResult(product) => {
                                    if join_key_positions.clone().unwrap().into_iter().all(|((left_fact_idx, left_column), right_column)| {
                                        product[left_fact_idx][left_column] == right_fact[*right_column]
                                    }) {
                                        let mut new_product = product.clone();
                                        new_product.push(right_fact);

                                        join_result.push(EphemeralValue::JoinResult(new_product));
                                    };
                                }
                            }
                        })
                    });

                    out.borrow_all(&join_result_name, join_result.into_iter());
                }
                Instruction::Project(_symbol, projection_inputs) => {
                    let ephemeral_relation_to_be_projected = out
                        .inner
                        .remove(relation_symbol_to_be_projected.as_str())
                        .unwrap();
                    ephemeral_relation_to_be_projected
                        .into_iter()
                        .for_each(|allocation| {
                            let fact = match allocation {
                                EphemeralValue::FactRef(fact) => fact.clone(),
                                EphemeralValue::JoinResult(facts) => {
                                    facts.into_iter().flat_map(|fact| fact).cloned().collect()
                                }
                            };
                            let mut projection = vec![];

                            projection_inputs.iter().for_each(|projection_input| {
                                match projection_input {
                                    ProjectionInput::Column(column) => {
                                        projection.push(fact[*column].clone())
                                    }
                                    ProjectionInput::Value(value) => {
                                        projection.push(value.clone())
                                    }
                                }
                            });

                            grounded_facts.push(projection)
                        });
                }
            }
        }

        grounded_facts.into_iter()
    }
}

#[cfg(test)]
mod test {
    use datalog_rule_macro::rule;
    use datalog_syntax::*;
    use crate::evaluation::spj_processor::{Instruction, ProjectionInput, Stack};

    #[test]
    fn from_unary_rule_into_stack() {
        let rule = rule! { Y(?x, ?y) <- [T(?x, ?y)] };

        let expected_stack = Stack {
            inner: vec![
                Instruction::Move("T".to_string()),
                Instruction::Project(
                    "Y".to_string(),
                    vec![ProjectionInput::Column(0), ProjectionInput::Column(1)],
                ),
            ],
        };

        assert_eq!(expected_stack, Stack::from(rule))
    }

    #[test]
    fn from_binary_rule_into_stack() {
        let rule = rule! { T(?y, 0, ?x) <- [T(?x, 2, ?y), T(?y, 2, ?z)] };

        let expected_stack = Stack {
            inner: vec![
                Instruction::Select("T".to_string(), 1, TypedValue::Int(2)),
                Instruction::Select("T".to_string(), 1, TypedValue::Int(2)),
                Instruction::Join("T_1=2".to_string(), "T_1=2".to_string(), vec![(2, 0)]),
                Instruction::Project(
                    "T".to_string(),
                    vec![
                        ProjectionInput::Column(2),
                        ProjectionInput::Value(TypedValue::Int(0)),
                        ProjectionInput::Column(0),
                    ],
                ),
            ],
        };

        assert_eq!(expected_stack, Stack::from(rule))
    }

    #[test]
    fn from_simple_binary_rule_into_stack() {
        let rule = rule! { T(?x, ?z) <- [T(?x, ?y), T(?y, ?z)] };

        let expected_stack = Stack {
            inner: vec![
                Instruction::Move("T".to_string()),
                Instruction::Move("T".to_string()),
                Instruction::Join("T".to_string(), "T".to_string(), vec![(1, 0)]),
                Instruction::Project(
                    "T".to_string(),
                    vec![ProjectionInput::Column(0), ProjectionInput::Column(3)],
                ),
            ],
        };

        assert_eq!(expected_stack, Stack::from(rule))
    }

    #[test]
    fn from_ternary_rule_into_operations() {
        let rule = rule! { T(?y, 0, ?w) <- [T(?x, 2, ?y), T(?y, 2, ?z), T(3, ?z, ?w)] };

        let expected_stack = Stack {
            inner: vec![
                Instruction::Select("T".to_string(), 1, TypedValue::Int(2)),
                Instruction::Select("T".to_string(), 1, TypedValue::Int(2)),
                Instruction::Join("T_1=2".to_string(), "T_1=2".to_string(), vec![(2, 0)]),
                Instruction::Select("T".to_string(), 0, TypedValue::Int(3)),
                Instruction::Join("T_1=2_T_1=2_2=0".to_string(), "T_0=3".to_string(), vec![(5, 1)]),
                Instruction::Project(
                    "T".to_string(),
                    vec![
                        ProjectionInput::Column(2),
                        ProjectionInput::Value(TypedValue::Int(0)),
                        ProjectionInput::Column(8),
                    ],
                ),
            ],
        };

        assert_eq!(expected_stack, Stack::from(rule))
    }
}
