use std::cell::UnsafeCell;
use std::fs::File;
use std::io::{BufRead, BufReader};

use pyo3::prelude::*;
use pyo3::types::{PyBool, PyInt, PyString, PyTuple};

use datalog_syntax::{
    AnonymousGroundAtom, Atom, Matcher, Program, Query, Rule, Term, TypedValue,
};
use micro_datalog::engine::datalog::MicroRuntime as RustRuntime;

// RustRuntime contains Box<dyn EvaluationEngine> which is !Send.
// Python's GIL ensures single-threaded access, so this is safe.
struct SendWrapper(UnsafeCell<RustRuntime>);
unsafe impl Send for SendWrapper {}
unsafe impl Sync for SendWrapper {}

impl SendWrapper {
    fn get(&self) -> &RustRuntime {
        unsafe { &*self.0.get() }
    }
    fn get_mut(&self) -> &mut RustRuntime {
        unsafe { &mut *self.0.get() }
    }
}

// ============================================================================
// Variable class
// ============================================================================

#[pyclass]
#[derive(Clone)]
struct Variable {
    #[pyo3(get)]
    name: String,
}

#[pymethods]
impl Variable {
    #[new]
    fn new(name: String) -> Self {
        Variable { name }
    }

    fn __repr__(&self) -> String {
        format!("Variable(\"{}\")", self.name)
    }
}

// ============================================================================
// Python → Rust conversions
// ============================================================================

fn py_to_typed_value(obj: &Bound<PyAny>) -> PyResult<TypedValue> {
    // Check bool before int (bool is subclass of int in Python)
    if let Ok(b) = obj.downcast::<PyBool>() {
        Ok(TypedValue::Bool(b.is_true()))
    } else if let Ok(i) = obj.downcast::<PyInt>() {
        let val: usize = i.extract()?;
        Ok(TypedValue::Int(val))
    } else if let Ok(s) = obj.downcast::<PyString>() {
        Ok(TypedValue::Str(s.to_str()?.to_string()))
    } else {
        Err(PyErr::new::<pyo3::exceptions::PyTypeError, _>(format!(
            "Expected str, int, or bool, got {}",
            obj.get_type().name()?
        )))
    }
}

fn py_to_term(obj: &Bound<PyAny>) -> PyResult<Term> {
    if let Ok(var) = obj.extract::<Variable>() {
        return Ok(Term::Variable(var.name));
    }
    let val = py_to_typed_value(obj)?;
    Ok(Term::Constant(val))
}

fn py_to_atom(obj: &Bound<PyAny>) -> PyResult<Atom> {
    let tuple: &Bound<PyTuple> = obj.downcast()?;
    if tuple.len() != 2 {
        return Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(
            "Atom must be a 2-tuple: (\"predicate\", (term1, term2, ...))",
        ));
    }

    let pred_str: String = tuple.get_item(0)?.extract()?;
    let (symbol, sign) = if let Some(stripped) = pred_str.strip_prefix('!') {
        (stripped.to_string(), false)
    } else {
        (pred_str, true)
    };

    let terms_obj = tuple.get_item(1)?;
    let terms_tuple: &Bound<PyTuple> = terms_obj.downcast()?;
    let mut terms = Vec::new();
    for i in 0..terms_tuple.len() {
        terms.push(py_to_term(&terms_tuple.get_item(i)?)?);
    }

    Ok(Atom { symbol, terms, sign })
}

fn py_to_rule(obj: &Bound<PyAny>) -> PyResult<Rule> {
    let tuple: &Bound<PyTuple> = obj.downcast()?;
    if tuple.len() < 2 {
        return Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(
            "Rule must have at least 2 atoms: (head, body1, ...)",
        ));
    }

    let head = py_to_atom(&tuple.get_item(0)?)?;
    let mut body = Vec::new();
    for i in 1..tuple.len() {
        body.push(py_to_atom(&tuple.get_item(i)?)?);
    }

    Ok(Rule { head, body, id: 0 })
}

fn py_to_program(rules: &Bound<PyAny>) -> PyResult<Program> {
    let list: Vec<Bound<PyAny>> = rules.extract()?;
    let mut rust_rules = Vec::new();
    for item in &list {
        rust_rules.push(py_to_rule(item)?);
    }
    Ok(Program::from(rust_rules))
}

fn py_to_fact(obj: &Bound<PyAny>) -> PyResult<(String, AnonymousGroundAtom)> {
    let tuple: &Bound<PyTuple> = obj.downcast()?;
    if tuple.len() != 2 {
        return Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(
            "Fact must be a 2-tuple: (\"predicate\", (val1, val2, ...))",
        ));
    }

    let pred: String = tuple.get_item(0)?.extract()?;
    let vals_obj = tuple.get_item(1)?;
    let vals_tuple: &Bound<PyTuple> = vals_obj.downcast()?;
    let mut vals = Vec::new();
    for i in 0..vals_tuple.len() {
        vals.push(py_to_typed_value(&vals_tuple.get_item(i)?)?);
    }

    Ok((pred, vals))
}

fn py_to_matchers(pattern: &Bound<PyTuple>) -> PyResult<Vec<Matcher>> {
    let mut matchers = Vec::new();
    for i in 0..pattern.len() {
        let item = pattern.get_item(i)?;
        if item.is_none() {
            matchers.push(Matcher::Any);
        } else {
            matchers.push(Matcher::Constant(py_to_typed_value(&item)?));
        }
    }
    Ok(matchers)
}

// ============================================================================
// Rust → Python conversions
// ============================================================================

fn typed_value_to_py(py: Python, val: &TypedValue) -> Py<PyAny> {
    match val {
        TypedValue::Str(s) => {
            let ps = PyString::new(py, s);
            ps.into_any().unbind()
        }
        TypedValue::Int(i) => {
            let pi = (*i as i64).into_pyobject(py).unwrap();
            pi.into_any().unbind()
        }
        TypedValue::Bool(b) => {
            let pb = PyBool::new(py, *b);
            pb.to_owned().into_any().unbind()
        }
    }
}

fn fact_to_py(py: Python, fact: &AnonymousGroundAtom) -> Py<PyAny> {
    let items: Vec<Py<PyAny>> = fact.iter().map(|v| typed_value_to_py(py, v)).collect();
    let refs: Vec<&Bound<PyAny>> = items.iter().map(|i| i.bind(py)).collect();
    PyTuple::new(py, &refs).unwrap().into_any().unbind()
}

// ============================================================================
// MicroRuntime wrapper
// ============================================================================

#[pyclass]
struct MicroRuntime {
    inner: SendWrapper,
    program: Program,
}

#[pymethods]
impl MicroRuntime {
    #[new]
    fn new(rules: &Bound<PyAny>) -> PyResult<Self> {
        let program = py_to_program(rules)?;
        let inner = RustRuntime::new(program.clone());

        Ok(MicroRuntime {
            inner: SendWrapper(UnsafeCell::new(inner)),
            program,
        })
    }

    fn insert(&self, fact: &Bound<PyAny>) -> PyResult<bool> {
        let (pred, vals) = py_to_fact(fact)?;
        Ok(self.inner.get_mut().insert(&pred, vals))
    }

    fn poll(&self) {
        self.inner.get_mut().poll();
    }

    fn query(&self, py: Python, predicate: &str, pattern: &Bound<PyTuple>) -> PyResult<Vec<Py<PyAny>>> {
        let matchers = py_to_matchers(pattern)?;
        let query = Query {
            symbol: predicate,
            matchers,
        };

        // Collect results before query is dropped (lifetime issue)
        let results: Result<Vec<AnonymousGroundAtom>, String> = self
            .inner
            .get()
            .query(&query)
            .map(|iter| iter.collect());

        match results {
            Ok(facts) => Ok(facts.iter().map(|f| fact_to_py(py, f)).collect()),
            Err(e) => Err(PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e)),
        }
    }

    fn contains(&self, fact: &Bound<PyAny>) -> PyResult<bool> {
        let (pred, vals) = py_to_fact(fact)?;
        match self.inner.get().contains(&pred, vals) {
            Ok(b) => Ok(b),
            Err(e) => Err(PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e)),
        }
    }

    fn safe(&self) -> bool {
        self.inner.get().safe()
    }

    fn query_program(
        &self,
        py: Python,
        predicate: &str,
        pattern: &Bound<PyTuple>,
        rules: &Bound<PyAny>,
        strategy: &str,
    ) -> PyResult<Vec<Py<PyAny>>> {
        let program = py_to_program(rules)?;
        let matchers = py_to_matchers(pattern)?;
        let query = Query {
            symbol: predicate,
            matchers,
        };

        let results: Result<Vec<AnonymousGroundAtom>, String> = self
            .inner
            .get_mut()
            .query_program(&query, program, strategy)
            .map(|iter| iter.collect());

        match results {
            Ok(facts) => Ok(facts.iter().map(|f| fact_to_py(py, f)).collect()),
            Err(e) => Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(e)),
        }
    }

    /// Return the MST-transformed program as a list of rule strings.
    fn get_mst_transformed(&self, predicate: &str, pattern: &Bound<PyTuple>, rules: &Bound<PyAny>) -> PyResult<Vec<String>> {
        let program = py_to_program(rules)?;
        let matchers = py_to_matchers(pattern)?;
        let query = Query { symbol: predicate, matchers };
        let transformed = micro_datalog::program_transformations::magic_sets::apply_magic_transformation(&program, &query);
        Ok(transformed.inner.iter().map(|r| format!("{:?}", r)).collect())
    }

    fn __len__(&self) -> usize {
        self.inner.get().fact_count()
    }
}

// ============================================================================
// IncrementalQueryView — persistent transformed runtime for incremental eval
// ============================================================================

/// A query-directed view that supports incremental base fact updates.
///
/// Transforms the program once (MST or SDT), creates a persistent runtime,
/// and handles incremental base fact insertion through poll(). Much faster
/// than calling query_program() repeatedly, which creates a fresh runtime
/// each time.
#[pyclass]
struct IncrementalQueryView {
    inner: SendWrapper,
    /// The adorned predicate name to query results from (e.g., "tc_bf")
    result_predicate: String,
    /// The original query matchers (for filtering results)
    query_matchers: Vec<Matcher>,
    /// IDB predicate names from the original program (to identify base predicates)
    idb_predicates: std::collections::HashSet<String>,
}

#[pymethods]
impl IncrementalQueryView {
    /// Create a new incremental query view.
    ///
    /// Args:
    ///     rules: list of rule tuples (the original program)
    ///     predicate: the predicate to query (e.g., "tc")
    ///     pattern: query pattern tuple (None for wildcard, value for bound)
    ///     strategy: "MST" or "SDT"
    #[new]
    #[pyo3(signature = (rules, predicate, pattern, strategy="MST"))]
    fn new(
        rules: &Bound<PyAny>,
        predicate: &str,
        pattern: &Bound<PyTuple>,
        strategy: Option<&str>,
    ) -> PyResult<Self> {
        let program = py_to_program(rules)?;
        let matchers = py_to_matchers(pattern)?;

        let query = Query {
            symbol: predicate,
            matchers: matchers.clone(),
        };

        // Build the adorned result predicate name
        let pattern_string: String = matchers
            .iter()
            .map(|m| match m {
                Matcher::Constant(_) => 'b',
                Matcher::Any => 'f',
            })
            .collect();
        let result_predicate = format!("{}_{}", predicate, pattern_string);

        // Apply the transformation
        let strategy = strategy.unwrap_or("MST");
        let (transformed_program, demand_preds) = match strategy {
            "MST" | "Bottom-up" => {
                let tp = micro_datalog::program_transformations::magic_sets::apply_magic_transformation(&program, &query);
                (tp, std::collections::HashSet::new())
            }
            "SDT" => {
                let result = micro_datalog::program_transformations::sdt::apply_sdt_transformation(&program, &query);
                (result.program, result.demand_predicates)
            }
            other => {
                return Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!(
                    "Unknown strategy '{}'. Use 'MST' or 'SDT'.",
                    other
                )));
            }
        };

        let mut runtime = RustRuntime::new(transformed_program.clone());

        // Register all relations from the transformed program
        for rule in &transformed_program.inner {
            runtime.unprocessed_insertions.inner.entry(rule.head.symbol.clone()).or_default();
            for body_atom in &rule.body {
                runtime.unprocessed_insertions.inner.entry(body_atom.symbol.clone()).or_default();
            }
        }

        // Insert the magic seed fact
        let (magic_pred, seed_fact) = micro_datalog::program_transformations::magic_sets::create_magic_seed_fact(&query);
        runtime.unprocessed_insertions.inner.entry(magic_pred.clone()).or_default();
        if !seed_fact.is_empty() {
            runtime.insert(&magic_pred, seed_fact);
        }

        // Collect IDB predicate names
        let idb_predicates: std::collections::HashSet<String> = program
            .inner
            .iter()
            .map(|r| r.head.symbol.clone())
            .collect();

        Ok(IncrementalQueryView {
            inner: SendWrapper(UnsafeCell::new(runtime)),
            result_predicate,
            query_matchers: matchers,
            idb_predicates,
        })
    }

    /// Insert a base fact. Only EDB (base) facts should be inserted.
    fn insert(&self, fact: &Bound<PyAny>) -> PyResult<bool> {
        let (pred, vals) = py_to_fact(fact)?;
        Ok(self.inner.get_mut().insert(&pred, vals))
    }

    /// Run incremental evaluation (processes only new delta facts).
    fn poll(&self) {
        self.inner.get_mut().poll();
    }

    /// Query the current results (after poll).
    fn query(&self, py: Python) -> PyResult<Vec<Py<PyAny>>> {
        let query = Query {
            symbol: &self.result_predicate,
            matchers: self.query_matchers.clone(),
        };

        let results: Result<Vec<AnonymousGroundAtom>, String> = self
            .inner
            .get()
            .query(&query)
            .map(|iter| iter.collect());

        match results {
            Ok(facts) => Ok(facts.iter().map(|f| fact_to_py(py, f)).collect()),
            Err(e) => Err(PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(e)),
        }
    }

    fn safe(&self) -> bool {
        self.inner.get().safe()
    }

    fn __len__(&self) -> usize {
        self.inner.get().fact_count()
    }
}

// ============================================================================
// LUBM .nt file loader (Rust-speed parsing)
// ============================================================================

const RDF_TYPE: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
const LUBM_NS: &str = "http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#";

fn load_lubm_nt_into(rt: &mut RustRuntime, path: &str) -> PyResult<usize> {
    let file = File::open(path)
        .map_err(|e| PyErr::new::<pyo3::exceptions::PyIOError, _>(format!("{}", e)))?;
    let reader = BufReader::with_capacity(1 << 20, file);

    let mut count = 0usize;
    let mut seen: std::collections::HashSet<(String, String, String)> = std::collections::HashSet::new();

    for line in reader.lines() {
        let Ok(line) = line else { continue };
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let line = line.trim_end_matches(" .").trim_end_matches('.');
        let mut parts = line.splitn(3, ' ');
        let s = match parts.next() {
            Some(s) => s.trim_matches(|c| c == '<' || c == '>'),
            None => continue,
        };
        let p = match parts.next() {
            Some(p) => p.trim_matches(|c| c == '<' || c == '>'),
            None => continue,
        };
        let o_raw = match parts.next() {
            Some(o) => o.trim(),
            None => continue,
        };
        let o = if o_raw.starts_with('<') {
            o_raw.trim_matches(|c| c == '<' || c == '>')
        } else {
            o_raw
        };

        if p == RDF_TYPE {
            if let Some(class_name) = o.strip_prefix(LUBM_NS) {
                let pred = format!("src_{}", class_name.to_lowercase());
                let key = (pred.clone(), s.to_string(), s.to_string());
                if seen.insert(key) {
                    let vals: AnonymousGroundAtom = vec![
                        TypedValue::Str(s.to_string()),
                        TypedValue::Str(s.to_string()),
                    ].into();
                    rt.insert(&pred, vals);
                    count += 1;
                }
            }
        } else if let Some(prop_name) = p.strip_prefix(LUBM_NS) {
            let pred = format!("src_{}", prop_name.to_lowercase());
            let key = (pred.clone(), s.to_string(), o.to_string());
            if seen.insert(key) {
                let vals: AnonymousGroundAtom = vec![
                    TypedValue::Str(s.to_string()),
                    TypedValue::Str(o.to_string()),
                ].into();
                rt.insert(&pred, vals);
                count += 1;
            }
        }
    }

    Ok(count)
}

/// Parse an N-Triples .nt file and insert all LUBM binary facts directly
/// into a MicroRuntime or IncrementalQueryView. Parsing in Rust — no Python loop.
/// Returns the number of facts inserted.
#[pyfunction]
fn load_lubm_nt(target: &Bound<PyAny>, path: &str) -> PyResult<usize> {
    if let Ok(rt) = target.downcast::<MicroRuntime>() {
        let rt_ref = rt.borrow();
        load_lubm_nt_into(rt_ref.inner.get_mut(), path)
    } else if let Ok(view) = target.downcast::<IncrementalQueryView>() {
        let view_ref = view.borrow();
        load_lubm_nt_into(view_ref.inner.get_mut(), path)
    } else {
        Err(PyErr::new::<pyo3::exceptions::PyTypeError, _>(
            "Expected MicroRuntime or IncrementalQueryView",
        ))
    }
}

// ============================================================================
// Module
// ============================================================================

mod ascent_programs;

#[pymodule]
fn pymycrodatalog(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<Variable>()?;
    m.add_class::<MicroRuntime>()?;
    m.add_class::<IncrementalQueryView>()?;
    m.add_function(wrap_pyfunction!(load_lubm_nt, m)?)?;
    ascent_programs::register(m)?;
    Ok(())
}
