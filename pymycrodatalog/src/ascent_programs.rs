use ascent::ascent;
use pyo3::prelude::*;
use pyo3::types::PyTuple;
use std::cell::UnsafeCell;
use std::time::Instant;

// ============================================================================
// Ascent program definitions (compile-time macro expansion)
// ============================================================================

ascent! {
    struct AscentLinearTC;
    relation e(usize, usize);
    relation tc(usize, usize);
    tc(x, y) <-- e(x, y);
    tc(x, z) <-- e(x, y), tc(y, z);
}

ascent! {
    struct AscentNonlinearTC;
    relation e(usize, usize);
    relation tc(usize, usize);
    tc(x, y) <-- e(x, y);
    tc(x, z) <-- tc(x, y), tc(y, z);
}

// MST-transformed TC for BF query: demand-driven + compile-time specialization
ascent! {
    struct AscentMstTcBf;
    relation e(usize, usize);
    relation magic_tc_bf(usize);
    relation tc_bf(usize, usize);

    // seed is inserted externally: magic_tc_bf(query_node)
    // demand rule: propagate demand along edges
    magic_tc_bf(y) <-- magic_tc_bf(x), e(x, y);
    // modified rules: only derive tc where demand exists
    tc_bf(x, y) <-- magic_tc_bf(x), e(x, y);
    tc_bf(x, z) <-- magic_tc_bf(x), e(x, y), tc_bf(y, z);
}

// MST-transformed TC for BB query: demand-driven point query
ascent! {
    struct AscentMstTcBb;
    relation e(usize, usize);
    relation magic_tc_bb(usize);
    relation tc_bb(usize, usize);

    // For BB, magic predicate carries first bound arg (source)
    // seed: magic_tc_bb(source) inserted externally
    magic_tc_bb(y) <-- magic_tc_bb(x), e(x, y);
    tc_bb(x, y) <-- magic_tc_bb(x), e(x, y);
    tc_bb(x, z) <-- magic_tc_bb(x), e(x, y), tc_bb(y, z);
}

ascent! {
    struct AscentRDFS;
    relation triple(usize, usize, usize);
    relation t(usize, usize, usize);

    // Copy
    t(s, p, o) <-- triple(s, p, o);
}

// For RDFS we need a custom struct with constant IDs
// Use a wrapper that sets up the program with the right constants

// ============================================================================
// SendWrapper for Ascent programs (not Send due to internal types)
// ============================================================================

struct SendWrap<T>(UnsafeCell<T>);
unsafe impl<T> Send for SendWrap<T> {}
unsafe impl<T> Sync for SendWrap<T> {}
impl<T> SendWrap<T> {
    fn get_mut(&self) -> &mut T { unsafe { &mut *self.0.get() } }
    fn get(&self) -> &T { unsafe { &*self.0.get() } }
}

// ============================================================================
// Python wrappers
// ============================================================================

/// Ascent Linear TC: tc(x,y) <- e(x,y). tc(x,z) <- e(x,y), tc(y,z).
/// NOT incremental — each run() recomputes from scratch.
#[pyclass]
struct AscentTC {
    inner: SendWrap<AscentLinearTC>,
}

#[pymethods]
impl AscentTC {
    #[new]
    fn new() -> Self {
        Self { inner: SendWrap(UnsafeCell::new(AscentLinearTC::default())) }
    }

    fn insert(&self, from: usize, to: usize) {
        self.inner.get_mut().e.push((from, to));
    }

    fn insert_many(&self, edges: Vec<(usize, usize)>) {
        self.inner.get_mut().e.extend(edges);
    }

    /// Run to fixpoint. Returns elapsed time in microseconds.
    fn run(&self) -> f64 {
        let start = Instant::now();
        self.inner.get_mut().run();
        start.elapsed().as_micros() as f64
    }

    fn tc_len(&self) -> usize {
        self.inner.get().tc.len()
    }

    fn tc_query(&self, py: Python, from_val: usize) -> Vec<Py<PyAny>> {
        self.inner.get().tc.iter()
            .filter(|(f, _)| *f == from_val)
            .map(|(f, t)| {
                PyTuple::new(py, &[f.into_pyobject(py).unwrap().into_any().unbind(),
                                   t.into_pyobject(py).unwrap().into_any().unbind()])
                    .unwrap().into_any().unbind()
            })
            .collect()
    }

    fn tc_all(&self, py: Python) -> Vec<Py<PyAny>> {
        self.inner.get().tc.iter()
            .map(|(f, t)| {
                PyTuple::new(py, &[f.into_pyobject(py).unwrap().into_any().unbind(),
                                   t.into_pyobject(py).unwrap().into_any().unbind()])
                    .unwrap().into_any().unbind()
            })
            .collect()
    }

    /// Reset the program (clear all facts).
    fn clear(&self) {
        let p = self.inner.get_mut();
        p.e.clear();
        p.tc.clear();
    }
}

/// Ascent Nonlinear TC: tc(x,z) <- tc(x,y), tc(y,z).
#[pyclass]
struct AscentNonlinTC {
    inner: SendWrap<AscentNonlinearTC>,
}

#[pymethods]
impl AscentNonlinTC {
    #[new]
    fn new() -> Self {
        Self { inner: SendWrap(UnsafeCell::new(AscentNonlinearTC::default())) }
    }

    fn insert(&self, from: usize, to: usize) {
        self.inner.get_mut().e.push((from, to));
    }

    fn insert_many(&self, edges: Vec<(usize, usize)>) {
        self.inner.get_mut().e.extend(edges);
    }

    fn run(&self) -> f64 {
        let start = Instant::now();
        self.inner.get_mut().run();
        start.elapsed().as_micros() as f64
    }

    fn tc_len(&self) -> usize {
        self.inner.get().tc.len()
    }

    fn tc_query(&self, py: Python, from_val: usize) -> Vec<Py<PyAny>> {
        self.inner.get().tc.iter()
            .filter(|(f, _)| *f == from_val)
            .map(|(f, t)| {
                PyTuple::new(py, &[f.into_pyobject(py).unwrap().into_any().unbind(),
                                   t.into_pyobject(py).unwrap().into_any().unbind()])
                    .unwrap().into_any().unbind()
            })
            .collect()
    }

    fn tc_all(&self, py: Python) -> Vec<Py<PyAny>> {
        self.inner.get().tc.iter()
            .map(|(f, t)| {
                PyTuple::new(py, &[f.into_pyobject(py).unwrap().into_any().unbind(),
                                   t.into_pyobject(py).unwrap().into_any().unbind()])
                    .unwrap().into_any().unbind()
            })
            .collect()
    }

    fn clear(&self) {
        let p = self.inner.get_mut();
        p.e.clear();
        p.tc.clear();
    }
}

/// Ascent RDFS: 7 ternary rules over T(s,p,o) triples.
/// Predicate IDs (rdf:type, rdfs:domain, etc.) must be passed as constructor args.
#[pyclass]
struct AscentRdfs {
    inner: SendWrap<AscentRDFS>,
}

#[pymethods]
impl AscentRdfs {
    #[new]
    fn new() -> Self {
        Self { inner: SendWrap(UnsafeCell::new(AscentRDFS::default())) }
    }

    fn insert(&self, s: usize, p: usize, o: usize) {
        self.inner.get_mut().triple.push((s, p, o));
    }

    fn run(&self) -> f64 {
        let start = Instant::now();
        self.inner.get_mut().run();
        start.elapsed().as_micros() as f64
    }

    fn t_len(&self) -> usize {
        self.inner.get().t.len()
    }

    fn clear(&self) {
        let p = self.inner.get_mut();
        p.triple.clear();
        p.t.clear();
    }
}

/// Ascent MST-TC BF: demand-driven TC with compile-time specialization.
/// Insert edges, set seed via seed_bf(node), then run.
#[pyclass]
struct AscentMstTcBfPy {
    inner: SendWrap<AscentMstTcBf>,
}

#[pymethods]
impl AscentMstTcBfPy {
    #[new]
    fn new() -> Self {
        Self { inner: SendWrap(UnsafeCell::new(AscentMstTcBf::default())) }
    }

    fn insert(&self, from: usize, to: usize) {
        self.inner.get_mut().e.push((from, to));
    }

    fn insert_many(&self, edges: Vec<(usize, usize)>) {
        self.inner.get_mut().e.extend(edges);
    }

    fn seed_bf(&self, node: usize) {
        self.inner.get_mut().magic_tc_bf.push((node,));
    }

    fn run(&self) -> f64 {
        let start = Instant::now();
        self.inner.get_mut().run();
        start.elapsed().as_micros() as f64
    }

    fn tc_len(&self) -> usize { self.inner.get().tc_bf.len() }
    fn magic_len(&self) -> usize { self.inner.get().magic_tc_bf.len() }

    fn tc_all(&self, py: Python) -> Vec<Py<PyAny>> {
        self.inner.get().tc_bf.iter()
            .map(|(f, t)| {
                PyTuple::new(py, &[f.into_pyobject(py).unwrap().into_any().unbind(),
                                   t.into_pyobject(py).unwrap().into_any().unbind()])
                    .unwrap().into_any().unbind()
            })
            .collect()
    }

    fn clear(&self) {
        let p = self.inner.get_mut();
        p.e.clear();
        p.tc_bf.clear();
        p.magic_tc_bf.clear();
    }
}

/// Ascent MST-TC BB: demand-driven point query with compile-time specialization.
#[pyclass]
struct AscentMstTcBbPy {
    inner: SendWrap<AscentMstTcBb>,
}

#[pymethods]
impl AscentMstTcBbPy {
    #[new]
    fn new() -> Self {
        Self { inner: SendWrap(UnsafeCell::new(AscentMstTcBb::default())) }
    }

    fn insert(&self, from: usize, to: usize) {
        self.inner.get_mut().e.push((from, to));
    }

    fn insert_many(&self, edges: Vec<(usize, usize)>) {
        self.inner.get_mut().e.extend(edges);
    }

    fn seed_bb(&self, source: usize) {
        self.inner.get_mut().magic_tc_bb.push((source,));
    }

    fn run(&self) -> f64 {
        let start = Instant::now();
        self.inner.get_mut().run();
        start.elapsed().as_micros() as f64
    }

    fn tc_len(&self) -> usize { self.inner.get().tc_bb.len() }
    fn magic_len(&self) -> usize { self.inner.get().magic_tc_bb.len() }

    fn tc_all(&self, py: Python) -> Vec<Py<PyAny>> {
        self.inner.get().tc_bb.iter()
            .map(|(f, t)| {
                PyTuple::new(py, &[f.into_pyobject(py).unwrap().into_any().unbind(),
                                   t.into_pyobject(py).unwrap().into_any().unbind()])
                    .unwrap().into_any().unbind()
            })
            .collect()
    }

    fn clear(&self) {
        let p = self.inner.get_mut();
        p.e.clear();
        p.tc_bb.clear();
        p.magic_tc_bb.clear();
    }
}

pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<AscentTC>()?;
    m.add_class::<AscentNonlinTC>()?;
    m.add_class::<AscentRdfs>()?;
    m.add_class::<AscentOwl2rl>()?;
    m.add_class::<AscentMstTcBfPy>()?;
    m.add_class::<AscentMstTcBbPy>()?;
    m.add_class::<AscentMstOwl2rlPy>()?;
    Ok(())
}

// ============================================================================
// OWL2RL: 128 rules, 104 binary predicates
// Generated from rules.py OWL2RL_ALL_RULES
// ============================================================================

ascent! {
    struct AscentOWL2RL;
    relation administrativestaff(usize, usize);
    relation advisor(usize, usize);
    relation affiliatedorganizationof(usize, usize);
    relation affiliateof(usize, usize);
    relation age(usize, usize);
    relation article(usize, usize);
    relation assistantprofessor(usize, usize);
    relation associateprofessor(usize, usize);
    relation book(usize, usize);
    relation chair(usize, usize);
    relation clericalstaff(usize, usize);
    relation college(usize, usize);
    relation conferencepaper(usize, usize);
    relation course(usize, usize);
    relation dean(usize, usize);
    relation degreefrom(usize, usize);
    relation department(usize, usize);
    relation director(usize, usize);
    relation doctoraldegreefrom(usize, usize);
    relation emailaddress(usize, usize);
    relation employee(usize, usize);
    relation faculty(usize, usize);
    relation fullprofessor(usize, usize);
    relation graduatecourse(usize, usize);
    relation graduatestudent(usize, usize);
    relation hasalumnus(usize, usize);
    relation headof(usize, usize);
    relation institute(usize, usize);
    relation journalarticle(usize, usize);
    relation lecturer(usize, usize);
    relation listedcourse(usize, usize);
    relation manual(usize, usize);
    relation mastersdegreefrom(usize, usize);
    relation member(usize, usize);
    relation memberof(usize, usize);
    relation name(usize, usize);
    relation organization(usize, usize);
    relation orgpublication(usize, usize);
    relation person(usize, usize);
    relation postdoc(usize, usize);
    relation professor(usize, usize);
    relation program(usize, usize);
    relation publication(usize, usize);
    relation publicationauthor(usize, usize);
    relation publicationdate(usize, usize);
    relation publicationresearch(usize, usize);
    relation research(usize, usize);
    relation researchassistant(usize, usize);
    relation researchgroup(usize, usize);
    relation researchinterest(usize, usize);
    relation researchproject(usize, usize);
    relation schedule(usize, usize);
    relation software(usize, usize);
    relation softwaredocumentation(usize, usize);
    relation softwareversion(usize, usize);
    relation specification(usize, usize);
    relation src_advisor(usize, usize);
    relation src_assistantprofessor(usize, usize);
    relation src_associateprofessor(usize, usize);
    relation src_course(usize, usize);
    relation src_department(usize, usize);
    relation src_doctoraldegreefrom(usize, usize);
    relation src_emailaddress(usize, usize);
    relation src_fullprofessor(usize, usize);
    relation src_graduatecourse(usize, usize);
    relation src_graduatestudent(usize, usize);
    relation src_headof(usize, usize);
    relation src_lecturer(usize, usize);
    relation src_mastersdegreefrom(usize, usize);
    relation src_memberof(usize, usize);
    relation src_name(usize, usize);
    relation src_publication(usize, usize);
    relation src_publicationauthor(usize, usize);
    relation src_researchassistant(usize, usize);
    relation src_researchgroup(usize, usize);
    relation src_researchinterest(usize, usize);
    relation src_suborganizationof(usize, usize);
    relation src_takescourse(usize, usize);
    relation src_teacherof(usize, usize);
    relation src_teachingassistant(usize, usize);
    relation src_teachingassistantof(usize, usize);
    relation src_telephone(usize, usize);
    relation src_undergraduatedegreefrom(usize, usize);
    relation src_undergraduatestudent(usize, usize);
    relation src_university(usize, usize);
    relation src_worksfor(usize, usize);
    relation student(usize, usize);
    relation suborganizationof(usize, usize);
    relation systemsstaff(usize, usize);
    relation takescourse(usize, usize);
    relation teacherof(usize, usize);
    relation teachingassistant(usize, usize);
    relation teachingassistantof(usize, usize);
    relation technicalreport(usize, usize);
    relation telephone(usize, usize);
    relation tenured(usize, usize);
    relation title(usize, usize);
    relation undergraduatedegreefrom(usize, usize);
    relation undergraduatestudent(usize, usize);
    relation university(usize, usize);
    relation unofficialpublication(usize, usize);
    relation visitingprofessor(usize, usize);
    relation work(usize, usize);
    relation worksfor(usize, usize);

    advisor(x, y) <-- src_advisor(x, y);
    assistantprofessor(x, x) <-- src_assistantprofessor(x, _fv1), if *x == *_fv1;
    associateprofessor(x, x) <-- src_associateprofessor(x, _fv2), if *x == *_fv2;
    course(x, x) <-- src_course(x, _fv3), if *x == *_fv3;
    department(x, x) <-- src_department(x, _fv4), if *x == *_fv4;
    doctoraldegreefrom(x, y) <-- src_doctoraldegreefrom(x, y);
    emailaddress(x, y) <-- src_emailaddress(x, y);
    fullprofessor(x, x) <-- src_fullprofessor(x, _fv5), if *x == *_fv5;
    graduatecourse(x, x) <-- src_graduatecourse(x, _fv6), if *x == *_fv6;
    graduatestudent(x, x) <-- src_graduatestudent(x, _fv7), if *x == *_fv7;
    headof(x, y) <-- src_headof(x, y);
    lecturer(x, x) <-- src_lecturer(x, _fv8), if *x == *_fv8;
    mastersdegreefrom(x, y) <-- src_mastersdegreefrom(x, y);
    memberof(x, y) <-- src_memberof(x, y);
    publicationauthor(x, y) <-- src_publicationauthor(x, y);
    researchassistant(x, x) <-- src_researchassistant(x, _fv9), if *x == *_fv9;
    researchgroup(x, x) <-- src_researchgroup(x, _fv10), if *x == *_fv10;
    suborganizationof(x, y) <-- src_suborganizationof(x, y);
    takescourse(x, y) <-- src_takescourse(x, y);
    teacherof(x, y) <-- src_teacherof(x, y);
    teachingassistant(x, x) <-- src_teachingassistant(x, _fv11), if *x == *_fv11;
    teachingassistantof(x, y) <-- src_teachingassistantof(x, y);
    telephone(x, y) <-- src_telephone(x, y);
    undergraduatedegreefrom(x, y) <-- src_undergraduatedegreefrom(x, y);
    undergraduatestudent(x, x) <-- src_undergraduatestudent(x, _fv12), if *x == *_fv12;
    university(x, x) <-- src_university(x, _fv13), if *x == *_fv13;
    worksfor(x, y) <-- src_worksfor(x, y);
    employee(x, x) <-- administrativestaff(x, _fv14), if *x == *_fv14;
    professor(x, x) <-- assistantprofessor(x, _fv15), if *x == *_fv15;
    professor(x, x) <-- associateprofessor(x, _fv16), if *x == *_fv16;
    person(x, x) <-- chair(x, _fv17), if *x == *_fv17;
    professor(x, x) <-- chair(x, _fv18), if *x == *_fv18;
    administrativestaff(x, x) <-- clericalstaff(x, _fv19), if *x == *_fv19;
    organization(x, x) <-- college(x, _fv20), if *x == *_fv20;
    article(x, x) <-- conferencepaper(x, _fv21), if *x == *_fv21;
    professor(x, x) <-- dean(x, _fv22), if *x == *_fv22;
    organization(x, x) <-- department(x, _fv23), if *x == *_fv23;
    person(x, x) <-- director(x, _fv24), if *x == *_fv24;
    person(x, x) <-- employee(x, _fv25), if *x == *_fv25;
    employee(x, x) <-- faculty(x, _fv26), if *x == *_fv26;
    professor(x, x) <-- fullprofessor(x, _fv27), if *x == *_fv27;
    course(x, x) <-- graduatecourse(x, _fv28), if *x == *_fv28;
    person(x, x) <-- graduatestudent(x, _fv29), if *x == *_fv29;
    organization(x, x) <-- institute(x, _fv30), if *x == *_fv30;
    article(x, x) <-- journalarticle(x, _fv31), if *x == *_fv31;
    faculty(x, x) <-- lecturer(x, _fv32), if *x == *_fv32;
    faculty(x, x) <-- postdoc(x, _fv33), if *x == *_fv33;
    faculty(x, x) <-- professor(x, _fv34), if *x == *_fv34;
    organization(x, x) <-- program(x, _fv35), if *x == *_fv35;
    person(x, x) <-- researchassistant(x, _fv36), if *x == *_fv36;
    organization(x, x) <-- researchgroup(x, _fv37), if *x == *_fv37;
    person(x, x) <-- student(x, _fv38), if *x == *_fv38;
    administrativestaff(x, x) <-- systemsstaff(x, _fv39), if *x == *_fv39;
    article(x, x) <-- technicalreport(x, _fv40), if *x == *_fv40;
    person(x, x) <-- teachingassistant(x, _fv41), if *x == *_fv41;
    person(x, x) <-- advisor(x, y);
    professor(y, y) <-- advisor(x, y);
    organization(x, x) <-- affiliatedorganizationof(x, y);
    organization(y, y) <-- affiliatedorganizationof(x, y);
    organization(x, x) <-- affiliateof(x, y);
    person(y, y) <-- affiliateof(x, y);
    person(x, x) <-- age(x, y);
    person(x, x) <-- degreefrom(x, y);
    university(y, y) <-- degreefrom(x, y);
    person(x, x) <-- doctoraldegreefrom(x, y);
    university(y, y) <-- doctoraldegreefrom(x, y);
    person(x, x) <-- emailaddress(x, y);
    person(y, y) <-- hasalumnus(x, y);
    university(x, x) <-- hasalumnus(x, y);
    course(y, y) <-- listedcourse(x, y);
    schedule(x, x) <-- listedcourse(x, y);
    person(x, x) <-- mastersdegreefrom(x, y);
    university(y, y) <-- mastersdegreefrom(x, y);
    organization(x, x) <-- member(x, y);
    person(y, y) <-- member(x, y);
    organization(x, x) <-- orgpublication(x, y);
    person(y, y) <-- publicationauthor(x, y);
    research(y, y) <-- publicationresearch(x, y);
    research(y, y) <-- researchproject(x, y);
    researchgroup(x, x) <-- researchproject(x, y);
    software(x, x) <-- softwaredocumentation(x, y);
    software(x, x) <-- softwareversion(x, y);
    organization(x, x) <-- suborganizationof(x, y);
    organization(y, y) <-- suborganizationof(x, y);
    course(y, y) <-- teacherof(x, y);
    faculty(x, x) <-- teacherof(x, y);
    course(y, y) <-- teachingassistantof(x, y);
    teachingassistant(x, x) <-- teachingassistantof(x, y);
    person(x, x) <-- telephone(x, y);
    professor(x, x) <-- tenured(x, y);
    person(x, x) <-- title(x, y);
    hasalumnus(y, x) <-- degreefrom(x, y);
    degreefrom(x, y) <-- doctoraldegreefrom(x, y);
    degreefrom(y, x) <-- hasalumnus(x, y);
    worksfor(x, y) <-- headof(x, y);
    degreefrom(x, y) <-- mastersdegreefrom(x, y);
    memberof(y, x) <-- member(x, y);
    member(y, x) <-- memberof(x, y);
    dean(x, x) <-- headof(x, y), college(y, _fv42), if *y == *_fv42;
    chair(x, x) <-- person(x, _fv43), headof(x, y), department(y, _fv44), if *x == *_fv43, if *y == *_fv44;
    director(x, x) <-- person(x, _fv45), headof(x, y), program(y, _fv46), if *x == *_fv45, if *y == *_fv46;
    student(x, x) <-- person(x, _fv47), takescourse(x, y), course(y, _fv48), if *x == *_fv47, if *y == *_fv48;
    teachingassistant(x, x) <-- person(x, _fv49), teachingassistantof(x, y), course(y, _fv50), if *x == *_fv49, if *y == *_fv50;
    employee(x, x) <-- person(x, _fv51), worksfor(x, y), organization(y, _fv52), if *x == *_fv51, if *y == *_fv52;
    suborganizationof(x, z) <-- suborganizationof(x, y), suborganizationof(y, z);
    person(x, x) <-- undergraduatedegreefrom(x, y);
    university(y, y) <-- undergraduatedegreefrom(x, y);
    degreefrom(x, y) <-- undergraduatedegreefrom(x, y);
    student(x, x) <-- undergraduatestudent(x, _fv53), if *x == *_fv53;
    organization(x, x) <-- university(x, _fv54), if *x == *_fv54;
    professor(x, x) <-- visitingprofessor(x, _fv55), if *x == *_fv55;
    memberof(x, y) <-- worksfor(x, y);
    name(x, y) <-- src_name(x, y);
    publication(x, x) <-- src_publication(x, _fv56), if *x == *_fv56;
    researchinterest(x, y) <-- src_researchinterest(x, y);
    publication(x, x) <-- article(x, _fv57), if *x == *_fv57;
    publication(x, x) <-- book(x, _fv58), if *x == *_fv58;
    work(x, x) <-- course(x, _fv59), if *x == *_fv59;
    publication(x, x) <-- manual(x, _fv60), if *x == *_fv60;
    publication(y, y) <-- orgpublication(x, y);
    publication(x, x) <-- publicationauthor(x, y);
    publication(x, x) <-- publicationdate(x, y);
    publication(x, x) <-- publicationresearch(x, y);
    work(x, x) <-- research(x, _fv61), if *x == *_fv61;
    publication(x, x) <-- software(x, _fv62), if *x == *_fv62;
    publication(y, y) <-- softwaredocumentation(x, y);
    publication(x, x) <-- specification(x, _fv63), if *x == *_fv63;
    publication(x, x) <-- unofficialpublication(x, _fv64), if *x == *_fv64;
}

/// Ascent OWL2RL entailment: 128 rules over binary predicates.
/// Facts are inserted by predicate name + (usize, usize) pair.
#[pyclass]
struct AscentOwl2rl {
    inner: SendWrap<AscentOWL2RL>,
}

#[pymethods]
impl AscentOwl2rl {
    #[new]
    fn new() -> Self {
        Self { inner: SendWrap(UnsafeCell::new(AscentOWL2RL::default())) }
    }

    /// Insert a fact into a source (EDB) relation.
    /// Only src_* predicates are EDB; all others are derived.
    fn insert(&self, predicate: &str, a: usize, b: usize) {
        let p = self.inner.get_mut();
        match predicate {
            "src_advisor" => p.src_advisor.push((a, b)),
            "src_assistantprofessor" => p.src_assistantprofessor.push((a, b)),
            "src_associateprofessor" => p.src_associateprofessor.push((a, b)),
            "src_course" => p.src_course.push((a, b)),
            "src_department" => p.src_department.push((a, b)),
            "src_doctoraldegreefrom" => p.src_doctoraldegreefrom.push((a, b)),
            "src_emailaddress" => p.src_emailaddress.push((a, b)),
            "src_fullprofessor" => p.src_fullprofessor.push((a, b)),
            "src_graduatecourse" => p.src_graduatecourse.push((a, b)),
            "src_graduatestudent" => p.src_graduatestudent.push((a, b)),
            "src_headof" => p.src_headof.push((a, b)),
            "src_lecturer" => p.src_lecturer.push((a, b)),
            "src_mastersdegreefrom" => p.src_mastersdegreefrom.push((a, b)),
            "src_memberof" => p.src_memberof.push((a, b)),
            "src_name" => p.src_name.push((a, b)),
            "src_publication" => p.src_publication.push((a, b)),
            "src_publicationauthor" => p.src_publicationauthor.push((a, b)),
            "src_researchassistant" => p.src_researchassistant.push((a, b)),
            "src_researchgroup" => p.src_researchgroup.push((a, b)),
            "src_researchinterest" => p.src_researchinterest.push((a, b)),
            "src_suborganizationof" => p.src_suborganizationof.push((a, b)),
            "src_takescourse" => p.src_takescourse.push((a, b)),
            "src_teacherof" => p.src_teacherof.push((a, b)),
            "src_teachingassistant" => p.src_teachingassistant.push((a, b)),
            "src_teachingassistantof" => p.src_teachingassistantof.push((a, b)),
            "src_telephone" => p.src_telephone.push((a, b)),
            "src_undergraduatedegreefrom" => p.src_undergraduatedegreefrom.push((a, b)),
            "src_undergraduatestudent" => p.src_undergraduatestudent.push((a, b)),
            "src_university" => p.src_university.push((a, b)),
            "src_worksfor" => p.src_worksfor.push((a, b)),
            _ => {} // ignore unknown predicates
        }
    }

    fn run(&self) -> f64 {
        let start = Instant::now();
        self.inner.get_mut().run();
        start.elapsed().as_micros() as f64
    }

    /// Count all derived facts across all relations.
    fn total_facts(&self) -> usize {
        let p = self.inner.get();
        let mut total = 0;
        // Count all IDB relations
        total += p.advisor.len() + p.administrativestaff.len();
        total += p.assistantprofessor.len() + p.associateprofessor.len();
        total += p.course.len() + p.department.len();
        total += p.dean.len() + p.chair.len() + p.director.len();
        total += p.employee.len() + p.faculty.len();
        total += p.fullprofessor.len() + p.graduatecourse.len();
        total += p.graduatestudent.len() + p.lecturer.len();
        total += p.person.len() + p.professor.len();
        total += p.student.len() + p.organization.len();
        total += p.researchassistant.len() + p.researchgroup.len();
        total += p.teachingassistant.len() + p.university.len();
        total += p.suborganizationof.len() + p.memberof.len();
        total += p.member.len() + p.worksfor.len();
        total += p.degreefrom.len() + p.hasalumnus.len();
        total += p.doctoraldegreefrom.len() + p.mastersdegreefrom.len();
        total += p.undergraduatedegreefrom.len();
        total += p.emailaddress.len() + p.telephone.len();
        total += p.headof.len() + p.teacherof.len();
        total += p.teachingassistantof.len() + p.takescourse.len();
        total += p.publicationauthor.len();
        total += p.article.len() + p.publication.len();
        total += p.name.len() + p.researchinterest.len();
        total += p.software.len() + p.softwaredocumentation.len();
        total += p.age.len() + p.affiliatedorganizationof.len();
        total += p.affiliateof.len() + p.title.len() + p.tenured.len();
        total
    }

    fn professor_count(&self) -> usize { self.inner.get().professor.len() }
    fn student_count(&self) -> usize { self.inner.get().student.len() }
    fn employee_count(&self) -> usize { self.inner.get().employee.len() }
}
// Auto-generated MST-transformed OWL2RL for professor BF query
// 218 rules, 151 predicates
// Uses fresh variables + if-guards for repeated vars (Ascent requirement)
ascent! {
    struct AscentMstOwl2rl;
    relation administrativestaff_bb(usize, usize);
    relation advisor_bf(usize, usize);
    relation advisor_fb(usize, usize);
    relation affiliatedorganizationof(usize, usize);
    relation affiliateof(usize, usize);
    relation age(usize, usize);
    relation assistantprofessor_bb(usize, usize);
    relation associateprofessor_bb(usize, usize);
    relation chair_bb(usize, usize);
    relation clericalstaff(usize, usize);
    relation college(usize, usize);
    relation course_bb(usize, usize);
    relation dean_bb(usize, usize);
    relation degreefrom_bf(usize, usize);
    relation degreefrom_fb(usize, usize);
    relation department_bb(usize, usize);
    relation director_bb(usize, usize);
    relation doctoraldegreefrom_bf(usize, usize);
    relation doctoraldegreefrom_fb(usize, usize);
    relation emailaddress_bf(usize, usize);
    relation employee_bb(usize, usize);
    relation faculty_bb(usize, usize);
    relation fullprofessor_bb(usize, usize);
    relation graduatecourse_bb(usize, usize);
    relation graduatestudent_bb(usize, usize);
    relation hasalumnus_bf(usize, usize);
    relation hasalumnus_fb(usize, usize);
    relation headof_bf(usize, usize);
    relation headof_fb(usize, usize);
    relation institute(usize, usize);
    relation lecturer_bb(usize, usize);
    relation listedcourse(usize, usize);
    relation magic_administrativestaff_bb(usize, usize);
    relation magic_advisor_bf(usize);
    relation magic_advisor_fb(usize);
    relation magic_assistantprofessor_bb(usize, usize);
    relation magic_associateprofessor_bb(usize, usize);
    relation magic_chair_bb(usize, usize);
    relation magic_course_bb(usize, usize);
    relation magic_dean_bb(usize, usize);
    relation magic_degreefrom_bf(usize);
    relation magic_degreefrom_fb(usize);
    relation magic_department_bb(usize, usize);
    relation magic_director_bb(usize, usize);
    relation magic_doctoraldegreefrom_bf(usize);
    relation magic_doctoraldegreefrom_fb(usize);
    relation magic_emailaddress_bf(usize);
    relation magic_employee_bb(usize, usize);
    relation magic_faculty_bb(usize, usize);
    relation magic_fullprofessor_bb(usize, usize);
    relation magic_graduatecourse_bb(usize, usize);
    relation magic_graduatestudent_bb(usize, usize);
    relation magic_hasalumnus_bf(usize);
    relation magic_hasalumnus_fb(usize);
    relation magic_headof_bf(usize);
    relation magic_headof_fb(usize);
    relation magic_lecturer_bb(usize, usize);
    relation magic_mastersdegreefrom_bf(usize);
    relation magic_mastersdegreefrom_fb(usize);
    relation magic_member_bf(usize);
    relation magic_member_fb(usize);
    relation magic_memberof_bf(usize);
    relation magic_memberof_fb(usize);
    relation magic_organization_bb(usize, usize);
    relation magic_person_bb(usize, usize);
    relation magic_professor_bb(usize, usize);
    relation magic_professor_bf(usize);
    relation magic_publicationauthor_fb(usize);
    relation magic_researchassistant_bb(usize, usize);
    relation magic_researchgroup_bb(usize, usize);
    relation magic_student_bb(usize, usize);
    relation magic_suborganizationof_bf(usize);
    relation magic_suborganizationof_fb(usize);
    relation magic_takescourse_bf(usize);
    relation magic_teacherof_bf(usize);
    relation magic_teacherof_fb(usize);
    relation magic_teachingassistant_bb(usize, usize);
    relation magic_teachingassistantof_bf(usize);
    relation magic_teachingassistantof_fb(usize);
    relation magic_telephone_bf(usize);
    relation magic_undergraduatedegreefrom_bf(usize);
    relation magic_undergraduatedegreefrom_fb(usize);
    relation magic_undergraduatestudent_bb(usize, usize);
    relation magic_university_bb(usize, usize);
    relation magic_worksfor_bf(usize);
    relation magic_worksfor_fb(usize);
    relation mastersdegreefrom_bf(usize, usize);
    relation mastersdegreefrom_fb(usize, usize);
    relation member_bf(usize, usize);
    relation member_fb(usize, usize);
    relation memberof_bf(usize, usize);
    relation memberof_fb(usize, usize);
    relation organization_bb(usize, usize);
    relation orgpublication(usize, usize);
    relation person_bb(usize, usize);
    relation postdoc(usize, usize);
    relation professor_bb(usize, usize);
    relation professor_bf(usize, usize);
    relation program(usize, usize);
    relation publicationauthor_fb(usize, usize);
    relation researchassistant_bb(usize, usize);
    relation researchgroup_bb(usize, usize);
    relation researchproject(usize, usize);
    relation src_advisor(usize, usize);
    relation src_assistantprofessor(usize, usize);
    relation src_associateprofessor(usize, usize);
    relation src_course(usize, usize);
    relation src_department(usize, usize);
    relation src_doctoraldegreefrom(usize, usize);
    relation src_emailaddress(usize, usize);
    relation src_fullprofessor(usize, usize);
    relation src_graduatecourse(usize, usize);
    relation src_graduatestudent(usize, usize);
    relation src_headof(usize, usize);
    relation src_lecturer(usize, usize);
    relation src_mastersdegreefrom(usize, usize);
    relation src_memberof(usize, usize);
    relation src_publicationauthor(usize, usize);
    relation src_researchassistant(usize, usize);
    relation src_researchgroup(usize, usize);
    relation src_suborganizationof(usize, usize);
    relation src_takescourse(usize, usize);
    relation src_teacherof(usize, usize);
    relation src_teachingassistant(usize, usize);
    relation src_teachingassistantof(usize, usize);
    relation src_telephone(usize, usize);
    relation src_undergraduatedegreefrom(usize, usize);
    relation src_undergraduatestudent(usize, usize);
    relation src_university(usize, usize);
    relation src_worksfor(usize, usize);
    relation student_bb(usize, usize);
    relation suborganizationof_bf(usize, usize);
    relation suborganizationof_fb(usize, usize);
    relation suborganizationof_ff(usize, usize);
    relation systemsstaff(usize, usize);
    relation takescourse_bf(usize, usize);
    relation teacherof_bf(usize, usize);
    relation teacherof_fb(usize, usize);
    relation teachingassistant_bb(usize, usize);
    relation teachingassistantof_bf(usize, usize);
    relation teachingassistantof_fb(usize, usize);
    relation telephone_bf(usize, usize);
    relation tenured(usize, usize);
    relation title(usize, usize);
    relation undergraduatedegreefrom_bf(usize, usize);
    relation undergraduatedegreefrom_fb(usize, usize);
    relation undergraduatestudent_bb(usize, usize);
    relation university_bb(usize, usize);
    relation visitingprofessor(usize, usize);
    relation worksfor_bf(usize, usize);
    relation worksfor_fb(usize, usize);

    magic_advisor_bf(x) <-- magic_person_bb(x, _fv1), if *x == *_fv1;
    magic_degreefrom_bf(x) <-- magic_hasalumnus_fb(x);
    magic_degreefrom_bf(x) <-- magic_person_bb(x, _fv2), if *x == *_fv2;
    magic_doctoraldegreefrom_bf(x) <-- magic_degreefrom_bf(x);
    magic_doctoraldegreefrom_bf(x) <-- magic_person_bb(x, _fv3), if *x == *_fv3;
    magic_emailaddress_bf(x) <-- magic_person_bb(x, _fv4), if *x == *_fv4;
    magic_hasalumnus_bf(x) <-- magic_degreefrom_fb(x);
    magic_hasalumnus_bf(x) <-- magic_university_bb(x, _fv5), if *x == *_fv5;
    magic_headof_bf(x) <-- magic_worksfor_bf(x);
    magic_headof_bf(x) <-- magic_chair_bb(x, _fv6), person_bb(x, _fv7), if *x == *_fv6, if *x == *_fv7;
    magic_headof_bf(x) <-- magic_dean_bb(x, _fv8), if *x == *_fv8;
    magic_headof_bf(x) <-- magic_director_bb(x, _fv9), person_bb(x, _fv10), if *x == *_fv9, if *x == *_fv10;
    magic_mastersdegreefrom_bf(x) <-- magic_degreefrom_bf(x);
    magic_mastersdegreefrom_bf(x) <-- magic_person_bb(x, _fv11), if *x == *_fv11;
    magic_member_bf(x) <-- magic_memberof_fb(x);
    magic_member_bf(x) <-- magic_organization_bb(x, _fv12), if *x == *_fv12;
    magic_memberof_bf(x) <-- magic_member_fb(x);
    magic_suborganizationof_bf(x) <-- magic_organization_bb(x, _fv13), if *x == *_fv13;
    magic_takescourse_bf(x) <-- magic_student_bb(x, _fv14), person_bb(x, _fv15), if *x == *_fv14, if *x == *_fv15;
    magic_teacherof_bf(x) <-- magic_faculty_bb(x, _fv16), if *x == *_fv16;
    magic_teachingassistantof_bf(x) <-- magic_teachingassistant_bb(x, _fv17), if *x == *_fv17;
    magic_teachingassistantof_bf(x) <-- magic_teachingassistant_bb(x, _fv18), person_bb(x, _fv19), if *x == *_fv18, if *x == *_fv19;
    magic_telephone_bf(x) <-- magic_person_bb(x, _fv20), if *x == *_fv20;
    magic_undergraduatedegreefrom_bf(x) <-- magic_degreefrom_bf(x);
    magic_undergraduatedegreefrom_bf(x) <-- magic_person_bb(x, _fv21), if *x == *_fv21;
    magic_worksfor_bf(x) <-- magic_memberof_bf(x);
    magic_worksfor_bf(x) <-- magic_employee_bb(x, _fv22), person_bb(x, _fv23), if *x == *_fv22, if *x == *_fv23;
    administrativestaff_bb(x, x) <-- magic_administrativestaff_bb(x, _fv24), clericalstaff(x, _fv25), if *x == *_fv24, if *x == *_fv25;
    administrativestaff_bb(x, x) <-- magic_administrativestaff_bb(x, _fv26), systemsstaff(x, _fv27), if *x == *_fv26, if *x == *_fv27;
    assistantprofessor_bb(x, x) <-- magic_assistantprofessor_bb(x, _fv28), src_assistantprofessor(x, _fv29), if *x == *_fv28, if *x == *_fv29;
    associateprofessor_bb(x, x) <-- magic_associateprofessor_bb(x, _fv30), src_associateprofessor(x, _fv31), if *x == *_fv30, if *x == *_fv31;
    chair_bb(x, x) <-- magic_chair_bb(x, _fv32), person_bb(x, _fv33), headof_bf(x, y), department_bb(y, _fv34), if *x == *_fv32, if *x == *_fv33, if *y == *_fv34;
    course_bb(x, x) <-- magic_course_bb(x, _fv35), graduatecourse_bb(x, _fv36), if *x == *_fv35, if *x == *_fv36;
    course_bb(x, x) <-- magic_course_bb(x, _fv37), src_course(x, _fv38), if *x == *_fv37, if *x == *_fv38;
    dean_bb(x, x) <-- magic_dean_bb(x, _fv39), headof_bf(x, y), college(y, _fv40), if *x == *_fv39, if *y == *_fv40;
    department_bb(x, x) <-- magic_department_bb(x, _fv41), src_department(x, _fv42), if *x == *_fv41, if *x == *_fv42;
    director_bb(x, x) <-- magic_director_bb(x, _fv43), person_bb(x, _fv44), headof_bf(x, y), program(y, _fv45), if *x == *_fv43, if *x == *_fv44, if *y == *_fv45;
    employee_bb(x, x) <-- magic_employee_bb(x, _fv46), administrativestaff_bb(x, _fv47), if *x == *_fv46, if *x == *_fv47;
    employee_bb(x, x) <-- magic_employee_bb(x, _fv48), faculty_bb(x, _fv49), if *x == *_fv48, if *x == *_fv49;
    employee_bb(x, x) <-- magic_employee_bb(x, _fv50), person_bb(x, _fv51), worksfor_bf(x, y), organization_bb(y, _fv52), if *x == *_fv50, if *x == *_fv51, if *y == *_fv52;
    faculty_bb(x, x) <-- magic_faculty_bb(x, _fv53), lecturer_bb(x, _fv54), if *x == *_fv53, if *x == *_fv54;
    faculty_bb(x, x) <-- magic_faculty_bb(x, _fv55), postdoc(x, _fv56), if *x == *_fv55, if *x == *_fv56;
    faculty_bb(x, x) <-- magic_faculty_bb(x, _fv57), professor_bb(x, _fv58), if *x == *_fv57, if *x == *_fv58;
    faculty_bb(x, x) <-- magic_faculty_bb(x, _fv59), teacherof_bf(x, y), if *x == *_fv59;
    fullprofessor_bb(x, x) <-- magic_fullprofessor_bb(x, _fv60), src_fullprofessor(x, _fv61), if *x == *_fv60, if *x == *_fv61;
    graduatecourse_bb(x, x) <-- magic_graduatecourse_bb(x, _fv62), src_graduatecourse(x, _fv63), if *x == *_fv62, if *x == *_fv63;
    graduatestudent_bb(x, x) <-- magic_graduatestudent_bb(x, _fv64), src_graduatestudent(x, _fv65), if *x == *_fv64, if *x == *_fv65;
    lecturer_bb(x, x) <-- magic_lecturer_bb(x, _fv66), src_lecturer(x, _fv67), if *x == *_fv66, if *x == *_fv67;
    magic_administrativestaff_bb(x, x) <-- magic_employee_bb(x, _fv68), if *x == *_fv68;
    magic_assistantprofessor_bb(x, x) <-- magic_professor_bf(x);
    magic_assistantprofessor_bb(x, x) <-- magic_professor_bb(x, _fv69), if *x == *_fv69;
    magic_associateprofessor_bb(x, x) <-- magic_professor_bf(x);
    magic_associateprofessor_bb(x, x) <-- magic_professor_bb(x, _fv70), if *x == *_fv70;
    magic_chair_bb(x, x) <-- magic_professor_bf(x);
    magic_chair_bb(x, x) <-- magic_person_bb(x, _fv71), if *x == *_fv71;
    magic_chair_bb(x, x) <-- magic_professor_bb(x, _fv72), if *x == *_fv72;
    magic_dean_bb(x, x) <-- magic_professor_bf(x);
    magic_dean_bb(x, x) <-- magic_professor_bb(x, _fv73), if *x == *_fv73;
    magic_department_bb(x, x) <-- magic_organization_bb(x, _fv74), if *x == *_fv74;
    magic_director_bb(x, x) <-- magic_person_bb(x, _fv75), if *x == *_fv75;
    magic_employee_bb(x, x) <-- magic_person_bb(x, _fv76), if *x == *_fv76;
    magic_faculty_bb(x, x) <-- magic_employee_bb(x, _fv77), if *x == *_fv77;
    magic_fullprofessor_bb(x, x) <-- magic_professor_bf(x);
    magic_fullprofessor_bb(x, x) <-- magic_professor_bb(x, _fv78), if *x == *_fv78;
    magic_graduatecourse_bb(x, x) <-- magic_course_bb(x, _fv79), if *x == *_fv79;
    magic_graduatestudent_bb(x, x) <-- magic_person_bb(x, _fv80), if *x == *_fv80;
    magic_lecturer_bb(x, x) <-- magic_faculty_bb(x, _fv81), if *x == *_fv81;
    magic_person_bb(x, x) <-- magic_chair_bb(x, _fv82), if *x == *_fv82;
    magic_person_bb(x, x) <-- magic_director_bb(x, _fv83), if *x == *_fv83;
    magic_person_bb(x, x) <-- magic_employee_bb(x, _fv84), if *x == *_fv84;
    magic_person_bb(x, x) <-- magic_student_bb(x, _fv85), if *x == *_fv85;
    magic_person_bb(x, x) <-- magic_teachingassistant_bb(x, _fv86), if *x == *_fv86;
    magic_professor_bb(x, x) <-- magic_faculty_bb(x, _fv87), if *x == *_fv87;
    magic_researchassistant_bb(x, x) <-- magic_person_bb(x, _fv88), if *x == *_fv88;
    magic_researchgroup_bb(x, x) <-- magic_organization_bb(x, _fv89), if *x == *_fv89;
    magic_student_bb(x, x) <-- magic_person_bb(x, _fv90), if *x == *_fv90;
    magic_teachingassistant_bb(x, x) <-- magic_person_bb(x, _fv91), if *x == *_fv91;
    magic_undergraduatestudent_bb(x, x) <-- magic_student_bb(x, _fv92), if *x == *_fv92;
    magic_university_bb(x, x) <-- magic_organization_bb(x, _fv93), if *x == *_fv93;
    organization_bb(x, x) <-- magic_organization_bb(x, _fv94), college(x, _fv95), if *x == *_fv94, if *x == *_fv95;
    organization_bb(x, x) <-- magic_organization_bb(x, _fv96), department_bb(x, _fv97), if *x == *_fv96, if *x == *_fv97;
    organization_bb(x, x) <-- magic_organization_bb(x, _fv98), institute(x, _fv99), if *x == *_fv98, if *x == *_fv99;
    organization_bb(x, x) <-- magic_organization_bb(x, _fv100), program(x, _fv101), if *x == *_fv100, if *x == *_fv101;
    organization_bb(x, x) <-- magic_organization_bb(x, _fv102), researchgroup_bb(x, _fv103), if *x == *_fv102, if *x == *_fv103;
    organization_bb(x, x) <-- magic_organization_bb(x, _fv104), university_bb(x, _fv105), if *x == *_fv104, if *x == *_fv105;
    organization_bb(x, x) <-- magic_organization_bb(x, _fv106), affiliatedorganizationof(x, y), if *x == *_fv106;
    organization_bb(x, x) <-- magic_organization_bb(x, _fv107), affiliateof(x, y), if *x == *_fv107;
    organization_bb(x, x) <-- magic_organization_bb(x, _fv108), member_bf(x, y), if *x == *_fv108;
    organization_bb(x, x) <-- magic_organization_bb(x, _fv109), orgpublication(x, y), if *x == *_fv109;
    organization_bb(x, x) <-- magic_organization_bb(x, _fv110), suborganizationof_bf(x, y), if *x == *_fv110;
    person_bb(x, x) <-- magic_person_bb(x, _fv111), chair_bb(x, _fv112), if *x == *_fv111, if *x == *_fv112;
    person_bb(x, x) <-- magic_person_bb(x, _fv113), director_bb(x, _fv114), if *x == *_fv113, if *x == *_fv114;
    person_bb(x, x) <-- magic_person_bb(x, _fv115), employee_bb(x, _fv116), if *x == *_fv115, if *x == *_fv116;
    person_bb(x, x) <-- magic_person_bb(x, _fv117), graduatestudent_bb(x, _fv118), if *x == *_fv117, if *x == *_fv118;
    person_bb(x, x) <-- magic_person_bb(x, _fv119), researchassistant_bb(x, _fv120), if *x == *_fv119, if *x == *_fv120;
    person_bb(x, x) <-- magic_person_bb(x, _fv121), student_bb(x, _fv122), if *x == *_fv121, if *x == *_fv122;
    person_bb(x, x) <-- magic_person_bb(x, _fv123), teachingassistant_bb(x, _fv124), if *x == *_fv123, if *x == *_fv124;
    person_bb(x, x) <-- magic_person_bb(x, _fv125), advisor_bf(x, y), if *x == *_fv125;
    person_bb(x, x) <-- magic_person_bb(x, _fv126), age(x, y), if *x == *_fv126;
    person_bb(x, x) <-- magic_person_bb(x, _fv127), degreefrom_bf(x, y), if *x == *_fv127;
    person_bb(x, x) <-- magic_person_bb(x, _fv128), doctoraldegreefrom_bf(x, y), if *x == *_fv128;
    person_bb(x, x) <-- magic_person_bb(x, _fv129), emailaddress_bf(x, y), if *x == *_fv129;
    person_bb(x, x) <-- magic_person_bb(x, _fv130), mastersdegreefrom_bf(x, y), if *x == *_fv130;
    person_bb(x, x) <-- magic_person_bb(x, _fv131), telephone_bf(x, y), if *x == *_fv131;
    person_bb(x, x) <-- magic_person_bb(x, _fv132), title(x, y), if *x == *_fv132;
    person_bb(x, x) <-- magic_person_bb(x, _fv133), undergraduatedegreefrom_bf(x, y), if *x == *_fv133;
    professor_bb(x, x) <-- magic_professor_bb(x, _fv134), assistantprofessor_bb(x, _fv135), if *x == *_fv134, if *x == *_fv135;
    professor_bb(x, x) <-- magic_professor_bb(x, _fv136), associateprofessor_bb(x, _fv137), if *x == *_fv136, if *x == *_fv137;
    professor_bb(x, x) <-- magic_professor_bb(x, _fv138), chair_bb(x, _fv139), if *x == *_fv138, if *x == *_fv139;
    professor_bb(x, x) <-- magic_professor_bb(x, _fv140), dean_bb(x, _fv141), if *x == *_fv140, if *x == *_fv141;
    professor_bb(x, x) <-- magic_professor_bb(x, _fv142), fullprofessor_bb(x, _fv143), if *x == *_fv142, if *x == *_fv143;
    professor_bb(x, x) <-- magic_professor_bb(x, _fv144), visitingprofessor(x, _fv145), if *x == *_fv144, if *x == *_fv145;
    professor_bb(x, x) <-- magic_professor_bb(x, _fv146), tenured(x, y), if *x == *_fv146;
    professor_bf(x, x) <-- magic_professor_bf(x), assistantprofessor_bb(x, _fv147), if *x == *_fv147;
    professor_bf(x, x) <-- magic_professor_bf(x), associateprofessor_bb(x, _fv148), if *x == *_fv148;
    professor_bf(x, x) <-- magic_professor_bf(x), chair_bb(x, _fv149), if *x == *_fv149;
    professor_bf(x, x) <-- magic_professor_bf(x), dean_bb(x, _fv150), if *x == *_fv150;
    professor_bf(x, x) <-- magic_professor_bf(x), fullprofessor_bb(x, _fv151), if *x == *_fv151;
    professor_bf(x, x) <-- magic_professor_bf(x), visitingprofessor(x, _fv152), if *x == *_fv152;
    professor_bf(x, x) <-- magic_professor_bf(x), tenured(x, y);
    researchassistant_bb(x, x) <-- magic_researchassistant_bb(x, _fv153), src_researchassistant(x, _fv154), if *x == *_fv153, if *x == *_fv154;
    researchgroup_bb(x, x) <-- magic_researchgroup_bb(x, _fv155), src_researchgroup(x, _fv156), if *x == *_fv155, if *x == *_fv156;
    researchgroup_bb(x, x) <-- magic_researchgroup_bb(x, _fv157), researchproject(x, y), if *x == *_fv157;
    student_bb(x, x) <-- magic_student_bb(x, _fv158), person_bb(x, _fv159), takescourse_bf(x, y), course_bb(y, _fv160), if *x == *_fv158, if *x == *_fv159, if *y == *_fv160;
    student_bb(x, x) <-- magic_student_bb(x, _fv161), undergraduatestudent_bb(x, _fv162), if *x == *_fv161, if *x == *_fv162;
    teachingassistant_bb(x, x) <-- magic_teachingassistant_bb(x, _fv163), person_bb(x, _fv164), teachingassistantof_bf(x, y), course_bb(y, _fv165), if *x == *_fv163, if *x == *_fv164, if *y == *_fv165;
    teachingassistant_bb(x, x) <-- magic_teachingassistant_bb(x, _fv166), src_teachingassistant(x, _fv167), if *x == *_fv166, if *x == *_fv167;
    teachingassistant_bb(x, x) <-- magic_teachingassistant_bb(x, _fv168), teachingassistantof_bf(x, y), if *x == *_fv168;
    undergraduatestudent_bb(x, x) <-- magic_undergraduatestudent_bb(x, _fv169), src_undergraduatestudent(x, _fv170), if *x == *_fv169, if *x == *_fv170;
    university_bb(x, x) <-- magic_university_bb(x, _fv171), src_university(x, _fv172), if *x == *_fv171, if *x == *_fv172;
    university_bb(x, x) <-- magic_university_bb(x, _fv173), hasalumnus_bf(x, y), if *x == *_fv173;
    advisor_bf(x, y) <-- magic_advisor_bf(x), src_advisor(x, y);
    advisor_fb(x, y) <-- magic_advisor_fb(y), src_advisor(x, y);
    degreefrom_bf(x, y) <-- magic_degreefrom_bf(x), doctoraldegreefrom_bf(x, y);
    degreefrom_bf(x, y) <-- magic_degreefrom_bf(x), mastersdegreefrom_bf(x, y);
    degreefrom_bf(x, y) <-- magic_degreefrom_bf(x), undergraduatedegreefrom_bf(x, y);
    degreefrom_fb(x, y) <-- magic_degreefrom_fb(y), doctoraldegreefrom_fb(x, y);
    degreefrom_fb(x, y) <-- magic_degreefrom_fb(y), mastersdegreefrom_fb(x, y);
    degreefrom_fb(x, y) <-- magic_degreefrom_fb(y), undergraduatedegreefrom_fb(x, y);
    doctoraldegreefrom_bf(x, y) <-- magic_doctoraldegreefrom_bf(x), src_doctoraldegreefrom(x, y);
    doctoraldegreefrom_fb(x, y) <-- magic_doctoraldegreefrom_fb(y), src_doctoraldegreefrom(x, y);
    emailaddress_bf(x, y) <-- magic_emailaddress_bf(x), src_emailaddress(x, y);
    headof_bf(x, y) <-- magic_headof_bf(x), src_headof(x, y);
    headof_fb(x, y) <-- magic_headof_fb(y), src_headof(x, y);
    mastersdegreefrom_bf(x, y) <-- magic_mastersdegreefrom_bf(x), src_mastersdegreefrom(x, y);
    mastersdegreefrom_fb(x, y) <-- magic_mastersdegreefrom_fb(y), src_mastersdegreefrom(x, y);
    memberof_bf(x, y) <-- magic_memberof_bf(x), src_memberof(x, y);
    memberof_bf(x, y) <-- magic_memberof_bf(x), worksfor_bf(x, y);
    memberof_fb(x, y) <-- magic_memberof_fb(y), src_memberof(x, y);
    memberof_fb(x, y) <-- magic_memberof_fb(y), worksfor_fb(x, y);
    publicationauthor_fb(x, y) <-- magic_publicationauthor_fb(y), src_publicationauthor(x, y);
    suborganizationof_bf(x, y) <-- magic_suborganizationof_bf(x), src_suborganizationof(x, y);
    suborganizationof_fb(x, y) <-- magic_suborganizationof_fb(y), src_suborganizationof(x, y);
    suborganizationof_ff(x, y) <-- src_suborganizationof(x, y);
    takescourse_bf(x, y) <-- magic_takescourse_bf(x), src_takescourse(x, y);
    teacherof_bf(x, y) <-- magic_teacherof_bf(x), src_teacherof(x, y);
    teacherof_fb(x, y) <-- magic_teacherof_fb(y), src_teacherof(x, y);
    teachingassistantof_bf(x, y) <-- magic_teachingassistantof_bf(x), src_teachingassistantof(x, y);
    teachingassistantof_fb(x, y) <-- magic_teachingassistantof_fb(y), src_teachingassistantof(x, y);
    telephone_bf(x, y) <-- magic_telephone_bf(x), src_telephone(x, y);
    undergraduatedegreefrom_bf(x, y) <-- magic_undergraduatedegreefrom_bf(x), src_undergraduatedegreefrom(x, y);
    undergraduatedegreefrom_fb(x, y) <-- magic_undergraduatedegreefrom_fb(y), src_undergraduatedegreefrom(x, y);
    worksfor_bf(x, y) <-- magic_worksfor_bf(x), headof_bf(x, y);
    worksfor_bf(x, y) <-- magic_worksfor_bf(x), src_worksfor(x, y);
    worksfor_fb(x, y) <-- magic_worksfor_fb(y), headof_fb(x, y);
    worksfor_fb(x, y) <-- magic_worksfor_fb(y), src_worksfor(x, y);
    suborganizationof_bf(x, z) <-- magic_suborganizationof_bf(x), suborganizationof_bf(x, y), suborganizationof_bf(y, z);
    suborganizationof_fb(x, z) <-- magic_suborganizationof_fb(z), suborganizationof_ff(x, y), suborganizationof_fb(y, z);
    suborganizationof_ff(x, z) <-- suborganizationof_ff(x, y), suborganizationof_ff(y, z);
    magic_advisor_fb(y) <-- magic_professor_bf(y);
    magic_advisor_fb(y) <-- magic_professor_bb(y, _fv174), if *y == *_fv174;
    magic_degreefrom_fb(y) <-- magic_hasalumnus_bf(y);
    magic_degreefrom_fb(y) <-- magic_university_bb(y, _fv175), if *y == *_fv175;
    magic_doctoraldegreefrom_fb(y) <-- magic_degreefrom_fb(y);
    magic_doctoraldegreefrom_fb(y) <-- magic_university_bb(y, _fv176), if *y == *_fv176;
    magic_hasalumnus_fb(y) <-- magic_degreefrom_bf(y);
    magic_hasalumnus_fb(y) <-- magic_person_bb(y, _fv177), if *y == *_fv177;
    magic_headof_fb(y) <-- magic_worksfor_fb(y);
    magic_mastersdegreefrom_fb(y) <-- magic_degreefrom_fb(y);
    magic_mastersdegreefrom_fb(y) <-- magic_university_bb(y, _fv178), if *y == *_fv178;
    magic_member_fb(y) <-- magic_memberof_bf(y);
    magic_member_fb(y) <-- magic_person_bb(y, _fv179), if *y == *_fv179;
    magic_memberof_fb(y) <-- magic_member_bf(y);
    magic_publicationauthor_fb(y) <-- magic_person_bb(y, _fv180), if *y == *_fv180;
    magic_suborganizationof_bf(y) <-- magic_suborganizationof_bf(x), suborganizationof_bf(x, y);
    magic_suborganizationof_fb(y) <-- magic_organization_bb(y, _fv181), if *y == *_fv181;
    magic_teacherof_fb(y) <-- magic_course_bb(y, _fv182), if *y == *_fv182;
    magic_teachingassistantof_fb(y) <-- magic_course_bb(y, _fv183), if *y == *_fv183;
    magic_undergraduatedegreefrom_fb(y) <-- magic_degreefrom_fb(y);
    magic_undergraduatedegreefrom_fb(y) <-- magic_university_bb(y, _fv184), if *y == *_fv184;
    magic_worksfor_fb(y) <-- magic_memberof_fb(y);
    degreefrom_bf(y, x) <-- magic_degreefrom_bf(y), hasalumnus_fb(x, y);
    degreefrom_fb(y, x) <-- magic_degreefrom_fb(x), hasalumnus_bf(x, y);
    hasalumnus_bf(y, x) <-- magic_hasalumnus_bf(y), degreefrom_fb(x, y);
    hasalumnus_fb(y, x) <-- magic_hasalumnus_fb(x), degreefrom_bf(x, y);
    member_bf(y, x) <-- magic_member_bf(y), memberof_fb(x, y);
    member_fb(y, x) <-- magic_member_fb(x), memberof_bf(x, y);
    memberof_bf(y, x) <-- magic_memberof_bf(y), member_fb(x, y);
    memberof_fb(y, x) <-- magic_memberof_fb(x), member_bf(x, y);
    course_bb(y, y) <-- magic_course_bb(y, _fv185), listedcourse(x, y), if *y == *_fv185;
    course_bb(y, y) <-- magic_course_bb(y, _fv186), teacherof_fb(x, y), if *y == *_fv186;
    course_bb(y, y) <-- magic_course_bb(y, _fv187), teachingassistantof_fb(x, y), if *y == *_fv187;
    magic_course_bb(y, y) <-- magic_student_bb(x, _fv188), person_bb(x, _fv189), takescourse_bf(x, y), if *x == *_fv188, if *x == *_fv189;
    magic_course_bb(y, y) <-- magic_teachingassistant_bb(x, _fv190), person_bb(x, _fv191), teachingassistantof_bf(x, y), if *x == *_fv190, if *x == *_fv191;
    magic_department_bb(y, y) <-- magic_chair_bb(x, _fv192), person_bb(x, _fv193), headof_bf(x, y), if *x == *_fv192, if *x == *_fv193;
    magic_organization_bb(y, y) <-- magic_employee_bb(x, _fv194), person_bb(x, _fv195), worksfor_bf(x, y), if *x == *_fv194, if *x == *_fv195;
    organization_bb(y, y) <-- magic_organization_bb(y, _fv196), affiliatedorganizationof(x, y), if *y == *_fv196;
    organization_bb(y, y) <-- magic_organization_bb(y, _fv197), suborganizationof_fb(x, y), if *y == *_fv197;
    person_bb(y, y) <-- magic_person_bb(y, _fv198), affiliateof(x, y), if *y == *_fv198;
    person_bb(y, y) <-- magic_person_bb(y, _fv199), hasalumnus_fb(x, y), if *y == *_fv199;
    person_bb(y, y) <-- magic_person_bb(y, _fv200), member_fb(x, y), if *y == *_fv200;
    person_bb(y, y) <-- magic_person_bb(y, _fv201), publicationauthor_fb(x, y), if *y == *_fv201;
    professor_bb(y, y) <-- magic_professor_bb(y, _fv202), advisor_fb(x, y), if *y == *_fv202;
    professor_bf(y, y) <-- magic_professor_bf(y), advisor_fb(x, y);
    university_bb(y, y) <-- magic_university_bb(y, _fv203), degreefrom_fb(x, y), if *y == *_fv203;
    university_bb(y, y) <-- magic_university_bb(y, _fv204), doctoraldegreefrom_fb(x, y), if *y == *_fv204;
    university_bb(y, y) <-- magic_university_bb(y, _fv205), mastersdegreefrom_fb(x, y), if *y == *_fv205;
    university_bb(y, y) <-- magic_university_bb(y, _fv206), undergraduatedegreefrom_fb(x, y), if *y == *_fv206;
}
/// Ascent MST-transformed OWL2RL for professor BF query.
/// 218 rules, 151 predicates. Demand-driven + compile-time specialized.
#[pyclass]
struct AscentMstOwl2rlPy {
    inner: SendWrap<AscentMstOwl2rl>,
}

#[pymethods]
impl AscentMstOwl2rlPy {
    #[new]
    fn new() -> Self {
        Self { inner: SendWrap(UnsafeCell::new(AscentMstOwl2rl::default())) }
    }

    /// Insert an EDB fact (same interface as AscentOwl2rl).
    fn insert(&self, predicate: &str, a: usize, b: usize) {
        let p = self.inner.get_mut();
        match predicate {
            "src_advisor" => p.src_advisor.push((a, b)),
            "src_assistantprofessor" => p.src_assistantprofessor.push((a, b)),
            "src_associateprofessor" => p.src_associateprofessor.push((a, b)),
            "src_course" => p.src_course.push((a, b)),
            "src_department" => p.src_department.push((a, b)),
            "src_doctoraldegreefrom" => p.src_doctoraldegreefrom.push((a, b)),
            "src_emailaddress" => p.src_emailaddress.push((a, b)),
            "src_fullprofessor" => p.src_fullprofessor.push((a, b)),
            "src_graduatecourse" => p.src_graduatecourse.push((a, b)),
            "src_graduatestudent" => p.src_graduatestudent.push((a, b)),
            "src_headof" => p.src_headof.push((a, b)),
            "src_lecturer" => p.src_lecturer.push((a, b)),
            "src_mastersdegreefrom" => p.src_mastersdegreefrom.push((a, b)),
            "src_memberof" => p.src_memberof.push((a, b)),
            "src_publicationauthor" => p.src_publicationauthor.push((a, b)),
            "src_researchassistant" => p.src_researchassistant.push((a, b)),
            "src_researchgroup" => p.src_researchgroup.push((a, b)),
            "src_suborganizationof" => p.src_suborganizationof.push((a, b)),
            "src_takescourse" => p.src_takescourse.push((a, b)),
            "src_teacherof" => p.src_teacherof.push((a, b)),
            "src_teachingassistant" => p.src_teachingassistant.push((a, b)),
            "src_teachingassistantof" => p.src_teachingassistantof.push((a, b)),
            "src_telephone" => p.src_telephone.push((a, b)),
            "src_undergraduatedegreefrom" => p.src_undergraduatedegreefrom.push((a, b)),
            "src_undergraduatestudent" => p.src_undergraduatestudent.push((a, b)),
            "src_university" => p.src_university.push((a, b)),
            "src_worksfor" => p.src_worksfor.push((a, b)),
            _ => {}
        }
    }

    /// Insert the magic seed fact for the professor BF query.
    /// The seed is magic_professor_bf(entity_hash).
    fn seed(&self, entity_hash: usize) {
        self.inner.get_mut().magic_professor_bf.push((entity_hash,));
    }

    fn run(&self) -> f64 {
        let start = Instant::now();
        self.inner.get_mut().run();
        start.elapsed().as_micros() as f64
    }

    fn professor_bf_count(&self) -> usize { self.inner.get().professor_bf.len() }
    fn professor_bb_count(&self) -> usize { self.inner.get().professor_bb.len() }
}
