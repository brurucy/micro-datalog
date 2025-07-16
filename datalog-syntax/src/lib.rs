use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::{collections::{HashMap, HashSet}, fmt::{Debug, Formatter}};

pub fn clean_rule(rule: &Rule) -> Rule {
    let mut clean_rule = rule.clone();
    let head_atom_terms: HashSet<_> = rule.head.terms.clone().into_iter().collect();
    let body_atoms: Vec<_> = rule.body.iter().enumerate().collect();
    let body_atom_terms: HashMap<_, _> = rule
        .body
        .iter()
        .map(|atom| (atom, atom.terms.clone().into_iter().collect::<HashSet<_>>()))
        .collect();

    let confirmed_non_useless_atoms = body_atoms.iter().filter(|(position, atom)| {
        let terms = body_atom_terms.get(atom).unwrap();
        if terms.intersection(&head_atom_terms).collect_vec().len() != 0 {
            true
        } else {
            false
        }
    }).collect_vec();

    body_atoms.iter().for_each(|(position, atom)| {
        let terms = body_atom_terms.get(atom).unwrap();
        if !confirmed_non_useless_atoms.contains(&&(*position, atom)) {
            let mut any_intersection = false;

            for non_useless_atom in confirmed_non_useless_atoms.iter() {
                let non_useless_atom_terms = body_atom_terms.get(non_useless_atom.1).unwrap();
                if non_useless_atom_terms.intersection(&terms).collect_vec().len() != 0 {
                    any_intersection = true;
                    break;
                }
            }

            if !any_intersection {  
                clean_rule.body.remove(*position);
            }
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

#[derive(Eq, Ord, PartialEq, PartialOrd, Clone, Hash, Serialize, Deserialize)]
pub enum TypedValue {
    Str(String),
    Int(usize),
    Bool(bool),
}

impl Debug for TypedValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypedValue::Str(x) => x.fmt(f),
            TypedValue::Int(x) => x.fmt(f),
            TypedValue::Bool(x) => x.fmt(f),
        }
    }
}

impl From<String> for TypedValue {
    fn from(value: String) -> Self {
        TypedValue::Str(value)
    }
}

impl From<&str> for TypedValue {
    fn from(value: &str) -> Self {
        TypedValue::Str(value.to_string())
    }
}

impl From<usize> for TypedValue {
    fn from(value: usize) -> Self {
        TypedValue::Int(value)
    }
}

impl From<bool> for TypedValue {
    fn from(value: bool) -> Self {
        TypedValue::Bool(value)
    }
}

impl Into<usize> for TypedValue {
    fn into(self) -> usize {
        match self {
            TypedValue::Int(x) => x,
            _ => unreachable!(),
        }
    }
}

impl Into<bool> for TypedValue {
    fn into(self) -> bool {
        match self {
            TypedValue::Bool(x) => x,
            _ => unreachable!(),
        }
    }
}

impl Into<String> for TypedValue {
    fn into(self) -> String {
        match self {
            TypedValue::Str(x) => x,
            _ => unreachable!(),
        }
    }
}

pub type Variable = String;

#[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Hash)]
pub enum Term {
    Variable(String),
    Constant(TypedValue),
}

impl Debug for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Variable(x) => x.fmt(f),
            Term::Constant(x) => x.fmt(f),
        }
    }
}

pub type AnonymousGroundAtom = Vec<TypedValue>;

pub struct Fact(pub AnonymousGroundAtom);

impl<T> From<(T,)> for Fact
where
    T: Into<TypedValue>,
{
    fn from(value: (T,)) -> Self {
        Fact(vec![value.0.into()])
    }
}

impl<T, R> From<(T, R)> for Fact
where
    T: Into<TypedValue>,
    R: Into<TypedValue>,
{
    fn from(value: (T, R)) -> Self {
        Fact(vec![value.0.into(), value.1.into()])
    }
}

impl<T, R, S> From<(T, R, S)> for Fact
where
    T: Into<TypedValue>,
    R: Into<TypedValue>,
    S: Into<TypedValue>,
{
    fn from(value: (T, R, S)) -> Self {
        Fact(vec![value.0.into(), value.1.into(), value.2.into()])
    }
}

impl<T, R, S, U> From<(T, R, S, U)> for Fact
where
    T: Into<TypedValue>,
    R: Into<TypedValue>,
    S: Into<TypedValue>,
    U: Into<TypedValue>,
{
    fn from(value: (T, R, S, U)) -> Self {
        Fact(vec![
            value.0.into(),
            value.1.into(),
            value.2.into(),
            value.3.into(),
        ])
    }
}

impl<T, R, S, U, V> From<(T, R, S, U, V)> for Fact
where
    T: Into<TypedValue>,
    R: Into<TypedValue>,
    S: Into<TypedValue>,
    U: Into<TypedValue>,
    V: Into<TypedValue>,
{
    fn from(value: (T, R, S, U, V)) -> Self {
        Fact(vec![
            value.0.into(),
            value.1.into(),
            value.2.into(),
            value.3.into(),
            value.4.into(),
        ])
    }
}

impl<T, R, S, U, V, W> From<(T, R, S, U, V, W)> for Fact
where
    T: Into<TypedValue>,
    R: Into<TypedValue>,
    S: Into<TypedValue>,
    U: Into<TypedValue>,
    V: Into<TypedValue>,
    W: Into<TypedValue>,
{
    fn from(value: (T, R, S, U, V, W)) -> Self {
        Fact(vec![
            value.0.into(),
            value.1.into(),
            value.2.into(),
            value.3.into(),
            value.4.into(),
            value.5.into(),
        ])
    }
}

impl<T, R, S, U, V, W, X> From<(T, R, S, U, V, W, X)> for Fact
where
    T: Into<TypedValue>,
    R: Into<TypedValue>,
    S: Into<TypedValue>,
    U: Into<TypedValue>,
    V: Into<TypedValue>,
    W: Into<TypedValue>,
    X: Into<TypedValue>,
{
    fn from(value: (T, R, S, U, V, W, X)) -> Self {
        Fact(vec![
            value.0.into(),
            value.1.into(),
            value.2.into(),
            value.3.into(),
            value.4.into(),
            value.5.into(),
            value.6.into(),
        ])
    }
}

impl<T, R, S, U, V, W, X, Y> From<(T, R, S, U, V, W, X, Y)> for Fact
where
    T: Into<TypedValue>,
    R: Into<TypedValue>,
    S: Into<TypedValue>,
    U: Into<TypedValue>,
    V: Into<TypedValue>,
    W: Into<TypedValue>,
    X: Into<TypedValue>,
    Y: Into<TypedValue>,
{
    fn from(value: (T, R, S, U, V, W, X, Y)) -> Self {
        Fact(vec![
            value.0.into(),
            value.1.into(),
            value.2.into(),
            value.3.into(),
            value.4.into(),
            value.5.into(),
            value.6.into(),
            value.7.into(),
        ])
    }
}

impl<T> From<Vec<T>> for Fact
where
    T: Into<TypedValue>,
{
    fn from(value: Vec<T>) -> Self {
        Fact(value.into_iter().map(|x| x.into()).collect())
    }
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Hash)]
pub struct Atom {
    pub terms: Vec<Term>,
    pub symbol: String,
    pub sign: bool, // true for positive, false for negative
}

impl Debug for Atom {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}(", &self.symbol)?;

        for (index, term) in self.terms.iter().enumerate() {
            write!(f, "{:?}", term)?;
            // Add comma between terms, but not after the last term
            if index < self.terms.len() - 1 {
                write!(f, ", ")?;
            }
        }

        write!(f, ")")
    }
}

#[derive(Clone, Debug)]
pub enum Matcher {
    Any,
    Constant(TypedValue),
}

#[derive(Clone)]
pub struct Query<'a> {
    pub matchers: Vec<Matcher>,
    pub symbol: &'a str,
}

pub struct QueryBuilder<'a> {
    pub query: Query<'a>,
}

impl<'a> QueryBuilder<'a> {
    pub fn new(relation: &'a str) -> Self {
        QueryBuilder {
            query: Query {
                matchers: vec![],
                symbol: relation,
            },
        }
    }
    pub fn with_any(&mut self) {
        self.query.matchers.push(Matcher::Any);
    }
    pub fn with_constant(&mut self, value: TypedValue) {
        self.query.matchers.push(Matcher::Constant(value))
    }
}

impl<'a> From<QueryBuilder<'a>> for Query<'a> {
    fn from(value: QueryBuilder<'a>) -> Self {
        value.query
    }
}

#[macro_export]
macro_rules! build_query {
    ($relation:ident ( $( $matcher:tt ),* $(,)? )) => {{
        let mut builder = QueryBuilder::new(stringify!($relation));
        $(
            build_query!(@matcher builder, $matcher);
        )*
        builder.query
    }};
    (@matcher $builder:expr, _) => {{
        $builder.with_any();
    }};
    (@matcher $builder:expr, $value:expr) => {{
        $builder.with_constant($value.into());
    }};
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Hash)]
pub struct Rule {
    pub head: Atom,
    pub body: Vec<Atom>,
    pub id: usize,
}

impl Debug for Rule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", &self.head)?;
        write!(f, " <- [")?;
        for (index, atom) in self.body.iter().enumerate() {
            write!(f, "{:?}", atom)?;
            if index < self.body.len() - 1 {
                write!(f, ", ")?;
            }
        }

        write!(f, "]")
    }
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone, Hash, Default)]
pub struct Program {
    pub inner: Vec<Rule>,
}

impl From<Vec<Rule>> for Program {
    fn from(value: Vec<Rule>) -> Self {
        let mut val: Vec<Rule> = value
            .into_iter()
            .map(|rule| clean_rule(&rule))
            .map(|rule| canonicalize_rule(&rule))
            .collect();
        val.sort();
        // Questionable, I know :)
        for (id, rule) in val.iter_mut().enumerate() {
            (*rule).id = id;
        }

        Self { inner: val }
    }
}

macro_rules! impl_fact_tuple {
    (2) => {
        impl<'a> TryInto<(&'a str, &'a str)> for &'a Fact {
            type Error = String;
            fn try_into(self) -> Result<(&'a str, &'a str), Self::Error> {
                if self.0.len() != 2 {
                    return Err("Fact must contain exactly 2 values".to_string());
                }
                Ok((
                    match &self.0[0] {
                        TypedValue::Str(s) => s.as_str(),
                        _ => return Err("Value at position 0 must be a string".to_string()),
                    },
                    match &self.0[1] {
                        TypedValue::Str(s) => s.as_str(),
                        _ => return Err("Value at position 1 must be a string".to_string()),
                    },
                ))
            }
        }
    };
    (3) => {
        impl<'a> TryInto<(&'a str, &'a str, &'a str)> for &'a Fact {
            type Error = String;
            fn try_into(self) -> Result<(&'a str, &'a str, &'a str), Self::Error> {
                if self.0.len() != 3 {
                    return Err("Fact must contain exactly 3 values".to_string());
                }
                Ok((
                    match &self.0[0] {
                        TypedValue::Str(s) => s.as_str(),
                        _ => return Err("Value at position 0 must be a string".to_string()),
                    },
                    match &self.0[1] {
                        TypedValue::Str(s) => s.as_str(),
                        _ => return Err("Value at position 1 must be a string".to_string()),
                    },
                    match &self.0[2] {
                        TypedValue::Str(s) => s.as_str(),
                        _ => return Err("Value at position 2 must be a string".to_string()),
                    },
                ))
            }
        }
    };
}

// Implement for tuple sizes 2 and 3
impl_fact_tuple!(2);
impl_fact_tuple!(3);
