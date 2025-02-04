use std::fmt::{Debug, Formatter};

#[derive(Eq, Ord, PartialEq, PartialOrd, Clone, Hash)]
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
            _ => unreachable!()
        }
    }
}

impl Into<bool> for TypedValue {
    fn into(self) -> bool {
        match self {
            TypedValue::Bool(x) => x,
            _ => unreachable!()
        }
    }
}

impl Into<String> for TypedValue {
    fn into(self) -> String {
        match self {
            TypedValue::Str(x) => x,
            _ => unreachable!()
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
        Fact(vec![value.0.into(), value.1.into(), value.2.into(), value.3.into()])
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
        Fact(vec![value.0.into(), value.1.into(), value.2.into(), value.3.into(), value.4.into()])
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
        Fact(vec![value.0.into(), value.1.into(), value.2.into(), value.3.into(), value.4.into(), value.5.into()])
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
        Fact(vec![value.0.into(), value.1.into(), value.2.into(), value.3.into(), value.4.into(), value.5.into(), value.6.into()])
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
        Fact(vec![value.0.into(), value.1.into(), value.2.into(), value.3.into(), value.4.into(), value.5.into(), value.6.into(), value.7.into()])
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

pub enum Matcher {
    Any,
    Constant(TypedValue),
}

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
        let mut val = value;
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
                        _ => return Err("Value at position 0 must be a string".to_string())
                    },
                    match &self.0[1] {
                        TypedValue::Str(s) => s.as_str(),
                        _ => return Err("Value at position 1 must be a string".to_string())
                    }
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
                        _ => return Err("Value at position 0 must be a string".to_string())
                    },
                    match &self.0[1] {
                        TypedValue::Str(s) => s.as_str(),
                        _ => return Err("Value at position 1 must be a string".to_string())
                    },
                    match &self.0[2] {
                        TypedValue::Str(s) => s.as_str(),
                        _ => return Err("Value at position 2 must be a string".to_string())
                    }
                ))
            }
        }
    };
}

// Implement for tuple sizes 2 and 3
impl_fact_tuple!(2);
impl_fact_tuple!(3);
