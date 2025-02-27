use std::collections::HashMap;
use std::sync::Arc;

use crate::engine::index_storage::{EphemeralValue, IndexStorage};
use crate::engine::storage::RelationStorage;
use crate::evaluation::spj_processor::Instruction::{Antijoin, Join, Project};
use boxcar;
use datalog_syntax::{AnonymousGroundAtom, Rule, Term, TypedValue, Variable};
use indexmap::{IndexMap, IndexSet};

// This implements a minimal SPJ (Select, Project, Join) processor

pub type Column = usize;
pub type Value = TypedValue;
pub type Symbol = String;
pub type Sign = bool;

#[derive(PartialEq, Debug, Clone)]
pub enum ProjectionInput {
    Column(Column),
    Value(Value),
}

#[derive(PartialEq, Debug, Clone)]
pub enum Instruction {
    Move(Symbol),
    Select(Symbol, Sign, Column, Value),
    Project(Symbol, Vec<ProjectionInput>),
    Join(Symbol, Symbol, Vec<(usize, usize)>),
    Antijoin(Symbol, Symbol, Vec<(usize, usize)>),
}

#[derive(PartialEq, Debug, Clone)]
pub struct Stack {
    pub(crate) inner: Vec<Instruction>,
}

fn stringify_selection(selection: &Instruction) -> String {
    match selection {
        Instruction::Select(symbol, sign, column, value) => {
            if *sign {
                format!("{}_{}={:?}", symbol, column, value)
            } else {
                format!("!{}_{}={:?}", symbol, column, value)
            }
        }
        _ => unreachable!(),
    }
}

fn stringify_join(join: &Instruction) -> String {
    let equality = match join {
        Instruction::Join(_, _, _) => "=",
        Instruction::Antijoin(_, _, _) => "!=",
        _ => unreachable!(),
    };

    return match join {
        Instruction::Join(left_symbol, right_symbol, join_keys)
        | Instruction::Antijoin(left_symbol, right_symbol, join_keys) => {
            let join_keys_format = join_keys
                .iter()
                .map(|(left_column, right_column)| {
                    format!("{}{}{}", left_column, equality, right_column)
                })
                .collect::<Vec<_>>()
                .join("_");

            format!("{}_{}_{}", left_symbol, right_symbol, join_keys_format)
        }
        _ => unreachable!(),
    };
}

fn get_selection(symbol: &str, sign: &bool, terms: &Vec<Term>) -> Option<Instruction> {
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

            return Instruction::Select(
                symbol.to_string(),
                sign.clone(),
                idx,
                constant_value.clone(),
            );
        })
        .collect();

    return selection.get(0).cloned();
}

fn get_variables(terms: &Vec<Term>) -> IndexMap<Variable, usize> {
    terms
        .into_iter()
        .cloned()
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
    anti: bool,
) -> Option<Instruction> {
    let left_variable_map = get_variables(left_terms);
    let right_variable_map = get_variables(right_terms);

    let mut join_keys = vec![];

    // Find matching variables between left and right terms
    for (variable_name, left_position) in left_variable_map {
        if let Some(right_position) = right_variable_map.get(&variable_name) {
            join_keys.push((left_position, *right_position));
        }
    }

    if !join_keys.is_empty() {
        return if anti {
            Some(Antijoin(
                left_symbol.to_string(),
                right_symbol.to_string(),
                join_keys,
            ))
        } else {
            Some(Join(
                left_symbol.to_string(),
                right_symbol.to_string(),
                join_keys,
            ))
        };
    }

    return None;
}

fn get_projection(rule: &Rule) -> Instruction {
    let projection_variable_targets: IndexSet<String> = rule
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

    let mut seen: IndexSet<_> = Default::default();
    let mut variable_location_assuming_joins_are_natural: IndexMap<Variable, usize> =
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

impl Stack {
    pub fn get_all_join_keys(&self) -> Vec<(String, Vec<(usize, usize)>)> {
        self.inner
            .iter()
            .filter_map(|instruction| match instruction {
                Instruction::Join(left_symbol, right_symbol, join_keys)
                | Instruction::Antijoin(left_symbol, right_symbol, join_keys) => Some(vec![
                    (left_symbol.clone(), join_keys.clone()),
                    (
                        right_symbol.clone(),
                        join_keys.iter().map(|(l, r)| (*r, *l)).collect(),
                    ),
                ]),
                _ => None,
            })
            .flatten() // Flatten the vec of pairs into a single iterator
            .collect()
    }

    pub fn get_all_moves(&self) -> IndexSet<String> {
        self.inner
            .iter()
            .filter(|m| match m {
                Instruction::Move(_) => true,
                _ => false,
            })
            .map(|m| match m {
                Instruction::Move(symbol) => symbol.clone(),
                _ => unreachable!(),
            })
            .collect::<IndexSet<_>>()
    }
}

impl From<Rule> for Stack {
    // convert a logical Rule into a sequence of operations represented by an Instruction enum
    fn from(rule: Rule) -> Self {
        let mut operations = vec![];

        let mut body_iter = rule.body.iter().peekable();
        let mut last_join_result_name = None;
        let mut last_join_terms: Vec<Term> = vec![];
        while let Some(current_atom) = body_iter.next() {
            if let Some(next_atom) = body_iter.peek() {
                let mut left_symbol = current_atom.symbol.clone();
                let mut left_terms = current_atom.terms.clone();
                let left_sign = current_atom.sign.clone();
                let mut right_symbol = next_atom.symbol.clone();
                let right_sign = next_atom.sign.clone();
                let right_terms = &next_atom.terms;

                if last_join_result_name.is_none() {
                    if let Some(selection) =
                        get_selection(&left_symbol, &left_sign, &current_atom.terms)
                    {
                        left_symbol = stringify_selection(&selection);
                        operations.push(selection);
                    } else {
                        operations.push(Instruction::Move(left_symbol.clone()));
                    }
                } else if let Some(_) = last_join_result_name {
                    left_symbol = last_join_result_name.clone().unwrap();
                    left_terms = last_join_terms.clone();
                }

                if let Some(selection) = get_selection(&right_symbol, &right_sign, right_terms) {
                    right_symbol = stringify_selection(&selection);
                    operations.push(selection);
                } else {
                    operations.push(Instruction::Move(right_symbol.clone()));
                }

                let is_anti_join = !left_sign || !right_sign;
                if let Some(binary_join) = get_join(
                    &left_terms,
                    right_terms,
                    &left_symbol,
                    &right_symbol,
                    is_anti_join,
                ) {
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

                operations.push(projection);
            }
        }

        Stack { inner: operations }
    }
}

pub struct RuleEvaluator<'a> {
    pub rule: &'a Rule,
    pub facts_storage: &'a RelationStorage,
}

impl<'a> RuleEvaluator<'a> {
    pub(crate) fn new(facts_storage: &'a RelationStorage, rule: &'a Rule) -> Self {
        Self {
            rule,
            facts_storage,
        }
    }
}

fn do_join(
    join_keys: &Vec<(usize, usize)>,
    left_relation: Option<&Vec<EphemeralValue>>,
    right_relation: &Vec<EphemeralValue>,
    join_key_positions: Option<&Vec<((usize, usize), usize)>>,
    index_storage: &IndexStorage,
    left_symbol: &str,
    right_symbol: Option<&str>,
) -> boxcar::Vec<EphemeralValue> {
    let join_result = boxcar::vec![];

    match (left_relation, right_symbol) {
        // If we don't have left relation, and no right_symbol, we probe the hash table of the left relation with the given right_relation.
        (None, None) => {
            if let Some(hash_table) = index_storage
                .hash_indices
                .get(&left_symbol.to_string())
                .and_then(|hash_table| hash_table.get(join_keys))
            {
                right_relation.into_iter().for_each(|right_allocation| {
                    let probe_key: Vec<TypedValue> = match right_allocation {
                        EphemeralValue::FactRef(right_fact) => {
                            let key = join_keys
                                .iter()
                                .map(|(_, right_col)| right_fact[*right_col].clone())
                                .collect();
                            key
                        }
                        EphemeralValue::JoinResult(_) => unreachable!(),
                    };

                    if let Some(matches) = hash_table.get(&probe_key) {
                        for left_allocation in matches {
                            match (left_allocation, right_allocation) {
                                (
                                    EphemeralValue::FactRef(left_fact),
                                    EphemeralValue::FactRef(right_fact),
                                ) => {
                                    join_result.push(EphemeralValue::JoinResult(vec![
                                        left_fact.clone(),
                                        right_fact.clone(),
                                    ]));
                                }
                                (
                                    EphemeralValue::JoinResult(left_product),
                                    EphemeralValue::FactRef(right_fact),
                                ) => {
                                    let mut new_product = left_product.clone();
                                    new_product.push(right_fact.clone());
                                    join_result.push(EphemeralValue::JoinResult(new_product));
                                }
                                _ => unreachable!(),
                            }
                        }
                    }
                });
            } else {
                unreachable!()
            }
        }
        // Else if there is a left_relation, and a right_symbol, we probe the hash table of the right relation with the given left_relation.
        (Some(left_relation), Some(right_symbol)) => {
            let reversed_join_keys: Vec<(usize, usize)> = join_keys
                .iter()
                .map(|(left, right)| (*right, *left))
                .collect();

            if let Some(hash_table) = index_storage
                .hash_indices
                .get(&right_symbol.to_string())
                .and_then(|hash_table| hash_table.get(&reversed_join_keys))
            {
                left_relation.into_iter().for_each(|left_allocation| {
                    let probe_key: Vec<TypedValue> = match left_allocation {
                        EphemeralValue::FactRef(left_fact) => {
                            let key = reversed_join_keys
                                .iter()
                                .map(|(_, left_col)| left_fact[*left_col].clone())
                                .collect();
                            key
                        }
                        EphemeralValue::JoinResult(left_product) => {
                            let key = join_key_positions
                                .unwrap()
                                .iter()
                                .map(|((left_fact_idx, left_column), _)| {
                                    left_product[*left_fact_idx][*left_column].clone()
                                })
                                .collect();

                            key
                        }
                    };

                    if let Some(matches) = hash_table.get(&probe_key) {
                        for right_allocation in matches {
                            match (left_allocation, right_allocation) {
                                (
                                    EphemeralValue::FactRef(left_fact),
                                    EphemeralValue::FactRef(right_fact),
                                ) => {
                                    join_result.push(EphemeralValue::JoinResult(vec![
                                        left_fact.clone(),
                                        right_fact.clone(),
                                    ]));
                                }
                                (
                                    EphemeralValue::JoinResult(left_product),
                                    EphemeralValue::FactRef(right_fact),
                                ) => {
                                    let mut new_product = left_product.clone();
                                    new_product.push(right_fact.clone());
                                    join_result.push(EphemeralValue::JoinResult(new_product));
                                }
                                _ => unreachable!(),
                            }
                        }
                    };
                });
            } else {
                unreachable!()
            }
        }
        (Some(left_relation), None) => {
            left_relation.iter().for_each(|left_allocation| {
                right_relation.iter().for_each(|right_allocation| {
                    match (left_allocation, right_allocation) {
                        (
                            EphemeralValue::FactRef(left_fact),
                            EphemeralValue::FactRef(right_fact),
                        ) => {
                            let matches = join_keys.iter().all(|(left_col, right_col)| {
                                left_fact[*left_col] == right_fact[*right_col]
                            });

                            if matches {
                                join_result.push(EphemeralValue::JoinResult(vec![
                                    left_fact.clone(),
                                    right_fact.clone(),
                                ]));
                            };
                        }
                        (
                            EphemeralValue::JoinResult(product),
                            EphemeralValue::FactRef(right_fact),
                        ) => {
                            if let Some(join_key_positions) = join_key_positions.as_ref() {
                                let matches =
                                    join_key_positions.iter().enumerate().all(|(i, _)| {
                                        let ((left_fact_idx, left_column), right_column) =
                                            join_key_positions[i];
                                        product[left_fact_idx][left_column]
                                            == right_fact[right_column]
                                    });

                                if matches {
                                    let mut new_product = product.clone();
                                    new_product.push(right_fact.clone());
                                    join_result.push(EphemeralValue::JoinResult(new_product));
                                };
                            }
                        }
                        _ => unreachable!(),
                    };
                });
            });
        }
        _ => unreachable!(),
    }

    join_result
}

impl<'a> RuleEvaluator<'a> {
    pub fn step(
        &self,
        index_storage: &mut IndexStorage,
    ) -> impl Iterator<Item = AnonymousGroundAtom> + 'a {
        let stack = Stack::from(self.rule.clone());

        // There will always be at least two elements on the stack. Move or Select, and then Projection.
        let penultimate_operation = stack.inner.len() - 2;
        let mut relation_symbol_to_be_projected = self.rule.head.symbol.clone();
        let mut grounded_facts = vec![];

        for (idx, operation) in stack.inner.iter().enumerate() {
            match operation {
                Instruction::Move(symbol) => {
                    if idx == penultimate_operation {
                        relation_symbol_to_be_projected = symbol.clone();
                    }
                }
                Instruction::Select(symbol, sign, column, value) => {
                    let index_name = stringify_selection(&operation);
                    if idx == penultimate_operation {
                        relation_symbol_to_be_projected = index_name.clone();
                    }
                    if index_storage.diff.get(&index_name).is_none() {
                        let target_relation = self.facts_storage.get_relation(symbol);

                        let selection = target_relation
                            .iter()
                            .filter(|fact| {
                                if *sign {
                                    fact[*column] == *value
                                } else {
                                    fact[*column] != *value
                                }
                            })
                            .map(|fact| EphemeralValue::FactRef(fact.clone()));

                        index_storage.borrow_all(&index_name, selection);
                    }
                }

                Instruction::Join(left_symbol, right_symbol, join_keys)
                | Instruction::Antijoin(left_symbol, right_symbol, join_keys) => {
                    let left = index_storage.inner.get(left_symbol);
                    let right = index_storage.inner.get(right_symbol);
                    let left_delta = index_storage.diff.get(left_symbol);
                    let right_delta = index_storage.diff.get(right_symbol);

                    let join_result_name = stringify_join(operation);
                    let mut join_key_positions = None;
                    if let Some(left_relation) = left {
                        if let Some(left_allocation) = left_relation
                            .get(0)
                            .or_else(|| left_delta.and_then(|ld| ld.get(0)))
                        {
                            match left_allocation {
                                EphemeralValue::JoinResult(product) => {
                                    join_key_positions = Some(
                                        join_keys
                                            .iter()
                                            .map(|(left_column, right_column)| {
                                                let mut cumsum = 0;

                                                let arities = product.iter().map(|fact| fact.len());

                                                let mut left_idx = 0;

                                                for (idx, arity) in arities.enumerate() {
                                                    cumsum += arity;

                                                    if *left_column < cumsum {
                                                        left_idx = idx;
                                                        break;
                                                    }
                                                }

                                                ((left_idx, cumsum - left_column), *right_column)
                                            })
                                            .collect::<Vec<_>>(),
                                    );
                                }
                                EphemeralValue::FactRef(_) => {}
                            }
                        };
                    }

                    let (left_right_delta, (right_left_delta, left_delta_right_delta)) =
                        rayon::join(
                            || {
                                if left.is_some() && right_delta.is_some() {
                                    Some(do_join(
                                        join_keys,
                                        None,
                                        right_delta.as_ref().unwrap(),
                                        join_key_positions.as_ref(),
                                        &*index_storage,
                                        left_symbol,
                                        None,
                                    ))
                                } else {
                                    None
                                }
                            },
                            || {
                                (
                                    if left_delta.is_some() && right.is_some() {
                                        Some(do_join(
                                            join_keys,
                                            Some(left_delta.as_ref().unwrap()),
                                            right.as_ref().unwrap(),
                                            join_key_positions.as_ref(),
                                            &*index_storage,
                                            left_symbol,
                                            Some(right_symbol.as_ref()),
                                        ))
                                    } else {
                                        None
                                    },
                                    if left_delta.is_some() && right_delta.is_some() {
                                        Some(do_join(
                                            join_keys,
                                            Some(left_delta.as_ref().unwrap()),
                                            right_delta.as_ref().unwrap(),
                                            join_key_positions.as_ref(),
                                            &*index_storage,
                                            left_symbol,
                                            None,
                                        ))
                                    } else {
                                        None
                                    },
                                )
                            },
                        );

                    if idx == penultimate_operation {
                        relation_symbol_to_be_projected = join_result_name.clone();
                    }

                    if let Some(left_right_delta) = left_right_delta {
                        index_storage.borrow_all(&join_result_name, left_right_delta.into_iter());
                    }
                    if let Some(right_left_delta) = right_left_delta {
                        index_storage.borrow_all(&join_result_name, right_left_delta.into_iter());
                    }
                    if let Some(left_delta_right_delta) = left_delta_right_delta {
                        index_storage
                            .borrow_all(&join_result_name, left_delta_right_delta.into_iter());
                    }
                }

                Instruction::Project(_symbol, projection_inputs) => {
                    if let Some(ephemeral_relation_to_be_projected) = index_storage
                        .diff
                        .get(relation_symbol_to_be_projected.as_str())
                    {
                        ephemeral_relation_to_be_projected
                            .into_iter()
                            .for_each(|allocation| {
                                let fact = match allocation {
                                    EphemeralValue::FactRef(fact) => fact.clone(),
                                    EphemeralValue::JoinResult(facts) => Arc::new(
                                        facts
                                            .into_iter()
                                            .flat_map(|fact| {
                                                fact.iter().cloned().collect::<Vec<_>>()
                                            })
                                            .collect(),
                                    ),
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

                                grounded_facts.push(projection);
                            });
                    }
                }
            }
        }

        grounded_facts.into_iter()
    }
}

#[cfg(test)]
mod test {
    use crate::evaluation::spj_processor::{Instruction, ProjectionInput, Stack};
    use datalog_rule_macro::rule;

    use datalog_syntax::*;

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
    fn from_unary_rule_with_negation_into_stack() {
        let rule = rule! { Y(?x, ?y) <- [T(?x, ?y), !E(?x, ?y)] };

        let expected_stack = Stack {
            inner: vec![
                Instruction::Move("T".to_string()),
                Instruction::Move("E".to_string()),
                Instruction::Antijoin("T".to_string(), "E".to_string(), vec![(0, 0), (1, 1)]),
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
                Instruction::Select("T".to_string(), true, 1, TypedValue::Int(2)),
                Instruction::Select("T".to_string(), true, 1, TypedValue::Int(2)),
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
                Instruction::Select("T".to_string(), true, 1, TypedValue::Int(2)),
                Instruction::Select("T".to_string(), true, 1, TypedValue::Int(2)),
                Instruction::Join("T_1=2".to_string(), "T_1=2".to_string(), vec![(2, 0)]),
                Instruction::Select("T".to_string(), true, 0, TypedValue::Int(3)),
                Instruction::Join(
                    "T_1=2_T_1=2_2=0".to_string(),
                    "T_0=3".to_string(),
                    vec![(5, 1)],
                ),
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
