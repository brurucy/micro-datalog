//! Semi-naive evaluation loop using Free Join.
//!
//! This module replaces the SPJ-based semi_naive_evaluation with an m-way
//! Free Join plan that handles multi-relation delta decomposition correctly.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::engine::storage::RelationStorage;
use datalog_syntax::{AnonymousGroundAtom, Program, Rule, Term, TypedValue};

// ============================================================================
// Free Join plan types
// ============================================================================

/// A variable name in Datalog
pub type Var = String;

/// Identifies a relation and which columns bind which variables
#[derive(Clone, Debug)]
pub struct SubAtom {
    /// The relation name
    pub relation: String,
    /// Maps relation column index -> variable name for columns relevant at this level
    pub bindings: Vec<(usize, Var)>,
}

/// One level of the Free Join plan tree
#[derive(Clone, Debug)]
pub struct FreeJoinNode {
    /// Variables newly bound at this level
    pub new_vars: Vec<Var>,
    /// The subatom(s) to iterate over. First is primary; others for intersection.
    pub iterate: Vec<SubAtom>,
    /// Subatoms to probe (hash lookup, must all succeed)
    pub probe: Vec<SubAtom>,
    /// Constant filters to verify after binding
    pub filters: Vec<(Var, TypedValue)>,
    /// Child nodes (next levels in the plan)
    pub children: Vec<FreeJoinNode>,
}

/// Complete plan for evaluating one rule body
#[derive(Clone, Debug)]
pub struct FreeJoinPlan {
    pub root: FreeJoinNode,
    pub head_symbol: String,
    /// Maps head column index -> variable or constant
    pub projection: Vec<ProjectionEntry>,
    /// Body relations in order (for delta scheduling). Only positive atoms.
    /// Each entry is (relation_name, atom_index_in_body).
    pub idb_body_relations: Vec<(String, usize)>,
    /// All body relations (including EDB, for trie building)
    pub all_body_relations: Vec<String>,
}

#[derive(Clone, Debug)]
pub enum ProjectionEntry {
    Variable(Var),
    Constant(TypedValue),
}

/// Delta mode for a relation during one evaluation pass
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeltaMode {
    /// Use only new facts (delta)
    DeltaOnly,
    /// Use only old facts (before this iteration)
    OldOnly,
    /// Use all facts (old + delta)
    Full,
}

// ============================================================================
// Trie storage types
// ============================================================================

/// A trie node for one column level
#[derive(Default, Clone, Debug)]
pub enum TrieNode {
    #[default]
    Empty,
    Interior {
        children: HashMap<TypedValue, TrieNode>,
    },
    Leaf {
        facts: Vec<Arc<AnonymousGroundAtom>>,
    },
}

impl TrieNode {
    /// Look up a specific value at this level, returning the subtrie
    pub fn lookup(&self, key: &TypedValue) -> Option<&TrieNode> {
        match self {
            TrieNode::Interior { children } => children.get(key),
            _ => None,
        }
    }

    /// Iterate over all (key, subtrie) pairs at this level
    pub fn iter_entries(&self) -> Box<dyn Iterator<Item = (&TypedValue, &TrieNode)> + '_> {
        match self {
            TrieNode::Interior { children } => Box::new(children.iter()),
            TrieNode::Empty => Box::new(std::iter::empty()),
            TrieNode::Leaf { .. } => Box::new(std::iter::empty()),
        }
    }

    /// Check if this node is non-empty (has children or facts)
    pub fn is_present(&self) -> bool {
        match self {
            TrieNode::Empty => false,
            TrieNode::Interior { children } => !children.is_empty(),
            TrieNode::Leaf { facts } => !facts.is_empty(),
        }
    }

    /// Insert a fact into the trie following the given column order
    pub fn insert(&mut self, fact: &Arc<AnonymousGroundAtom>, columns: &[usize], depth: usize) {
        if depth >= columns.len() {
            match self {
                TrieNode::Leaf { facts } => facts.push(fact.clone()),
                TrieNode::Empty => {
                    *self = TrieNode::Leaf {
                        facts: vec![fact.clone()],
                    };
                }
                _ => panic!("expected leaf at max depth"),
            }
            return;
        }

        let key = fact[columns[depth]].clone();
        match self {
            TrieNode::Interior { children } => {
                children
                    .entry(key)
                    .or_insert(TrieNode::Empty)
                    .insert(fact, columns, depth + 1);
            }
            TrieNode::Empty => {
                let mut children = HashMap::new();
                let mut child = TrieNode::Empty;
                child.insert(fact, columns, depth + 1);
                children.insert(key, child);
                *self = TrieNode::Interior { children };
            }
            TrieNode::Leaf { .. } => panic!("unexpected leaf at interior depth"),
        }
    }
}

/// Storage for one relation with multiple trie indices (different column orderings)
#[derive(Debug)]
pub struct RelationTrieStorage {
    /// Maps column ordering -> (main trie, delta trie)
    pub tries: HashMap<Vec<usize>, (TrieNode, TrieNode)>,
}

impl RelationTrieStorage {
    pub fn new() -> Self {
        RelationTrieStorage {
            tries: HashMap::new(),
        }
    }

    /// Navigate the appropriate trie (main, delta, or combined view)
    /// following a prefix of bound values.
    /// Returns the subtrie after navigating through all prefix values.
    pub fn navigate(
        &self,
        column_order: &[usize],
        prefix: &[TypedValue],
        mode: DeltaMode,
    ) -> Option<NavigationResult> {
        let (main, delta) = self.tries.get(column_order)?;

        match mode {
            DeltaMode::OldOnly => {
                let node = navigate_trie(main, prefix)?;
                Some(NavigationResult::Single(node))
            }
            DeltaMode::DeltaOnly => {
                let node = navigate_trie(delta, prefix)?;
                Some(NavigationResult::Single(node))
            }
            DeltaMode::Full => {
                let main_node = navigate_trie(main, prefix);
                let delta_node = navigate_trie(delta, prefix);
                match (main_node, delta_node) {
                    (Some(m), Some(d)) => Some(NavigationResult::Combined(m, d)),
                    (Some(m), None) => Some(NavigationResult::Single(m)),
                    (None, Some(d)) => Some(NavigationResult::Single(d)),
                    (None, None) => None,
                }
            }
        }
    }

    /// Check if any ordering has delta facts
    pub fn has_any_delta(&self) -> bool {
        self.tries.values().any(|(_, delta)| delta.is_present())
    }
}

/// Result of navigating a trie — either a single node or combined main+delta
#[derive(Debug)]
pub enum NavigationResult<'a> {
    Single(&'a TrieNode),
    Combined(&'a TrieNode, &'a TrieNode),
}

impl<'a> NavigationResult<'a> {
    /// Iterate over all (key, subtrie) pairs, merging main and delta
    pub fn iter_entries(&self) -> Box<dyn Iterator<Item = (TypedValue, NavigationResult<'_>)> + '_> {
        match self {
            NavigationResult::Single(node) => {
                Box::new(node.iter_entries().map(|(k, v)| {
                    (k.clone(), NavigationResult::Single(v))
                }))
            }
            NavigationResult::Combined(main, delta) => {
                // Collect all keys from both tries, iterate merged
                let mut keys: HashSet<TypedValue> = HashSet::new();
                for (k, _) in main.iter_entries() {
                    keys.insert(k.clone());
                }
                for (k, _) in delta.iter_entries() {
                    keys.insert(k.clone());
                }
                let main_ref = *main;
                let delta_ref = *delta;
                Box::new(keys.into_iter().map(move |k| {
                    let m = main_ref.lookup(&k);
                    let d = delta_ref.lookup(&k);
                    let nav = match (m, d) {
                        (Some(mn), Some(dn)) => NavigationResult::Combined(mn, dn),
                        (Some(mn), None) => NavigationResult::Single(mn),
                        (None, Some(dn)) => NavigationResult::Single(dn),
                        (None, None) => unreachable!(),
                    };
                    (k, nav)
                }))
            }
        }
    }

}

fn navigate_trie<'a>(node: &'a TrieNode, prefix: &[TypedValue]) -> Option<&'a TrieNode> {
    let mut current = node;
    for val in prefix {
        current = current.lookup(val)?;
    }
    if current.is_present() {
        Some(current)
    } else {
        None
    }
}

/// Top-level trie storage for all relations
#[derive(Debug, Default)]
pub struct TrieStorage {
    pub relations: HashMap<String, RelationTrieStorage>,
}

impl TrieStorage {
    /// Build tries from the Free Join plans (determines which column orderings are needed).
    /// IDB relations have their initial facts placed in both main and delta tries,
    /// matching semi-naive semantics where initial facts are treated as "new" for
    /// the first iteration. EDB relations only go into main tries.
    pub fn from_plans_and_storage(
        plans: &[FreeJoinPlan],
        relation_storage: &RelationStorage,
        idb_relations: &HashSet<String>,
    ) -> Self {
        let required = collect_required_orderings(plans);
        let mut storage = TrieStorage {
            relations: HashMap::new(),
        };

        for (rel_name, orderings) in &required {
            let is_idb = idb_relations.contains(rel_name);
            let mut rel_trie = RelationTrieStorage::new();
            for ordering in orderings {
                let mut main_trie = TrieNode::Empty;
                let mut delta_trie = TrieNode::Empty;
                // Populate from relation_storage
                if let Some(facts) = relation_storage.inner.get(rel_name) {
                    for fact in facts.iter() {
                        main_trie.insert(fact, ordering, 0);
                        // IDB facts are also placed in delta trie for the first iteration
                        if is_idb {
                            delta_trie.insert(fact, ordering, 0);
                        }
                    }
                }
                rel_trie
                    .tries
                    .insert(ordering.clone(), (main_trie, delta_trie));
            }
            storage.relations.insert(rel_name.clone(), rel_trie);
        }

        storage
    }

    /// Insert new facts into both main and delta tries for a relation
    pub fn insert_facts(
        &mut self,
        relation: &str,
        facts: &[Arc<AnonymousGroundAtom>],
        into_main: bool,
        into_delta: bool,
    ) {
        if let Some(rel_trie) = self.relations.get_mut(relation) {
            for (ordering, (main, delta)) in rel_trie.tries.iter_mut() {
                for fact in facts {
                    if into_main {
                        main.insert(fact, ordering, 0);
                    }
                    if into_delta {
                        delta.insert(fact, ordering, 0);
                    }
                }
            }
        }
    }

    /// Clear all delta tries
    pub fn clear_all_deltas(&mut self) {
        for rel_trie in self.relations.values_mut() {
            for (_, delta) in rel_trie.tries.values_mut() {
                *delta = TrieNode::Empty;
            }
        }
    }


    /// Check if a relation has any delta facts
    pub fn has_delta(&self, relation: &str) -> bool {
        self.relations
            .get(relation)
            .map_or(false, |r| r.has_any_delta())
    }

    /// Navigate a relation's trie
    pub fn navigate(
        &self,
        relation: &str,
        column_order: &[usize],
        prefix: &[TypedValue],
        mode: DeltaMode,
    ) -> Option<NavigationResult> {
        self.relations
            .get(relation)?
            .navigate(column_order, prefix, mode)
    }
}

// ============================================================================
// Bindings — variable-to-value environment during plan execution
// ============================================================================

#[derive(Debug, Clone)]
struct Bindings {
    values: Vec<(Var, TypedValue)>,
}

impl Bindings {
    fn new() -> Self {
        Bindings { values: Vec::with_capacity(8) }
    }

    fn get(&self, var: &str) -> Option<&TypedValue> {
        // Search from the end (most recently bound first)
        self.values.iter().rev().find(|(v, _)| v == var).map(|(_, val)| val)
    }

    fn bind(&mut self, var: &str, val: TypedValue) {
        self.values.push((var.to_string(), val));
    }

    fn unbind_last_n(&mut self, n: usize) {
        self.values.truncate(self.values.len() - n);
    }
}

// ============================================================================
// Plan compiler: Rule -> FreeJoinPlan
// ============================================================================

/// Compile all rules in a program to FreeJoinPlans.
pub fn compile_plans(program: &Program) -> Vec<FreeJoinPlan> {
    program
        .inner
        .iter()
        .map(|rule| compile_rule(rule))
        .collect()
}

/// Compile a single rule into a FreeJoinPlan.
pub fn compile_rule(rule: &Rule) -> FreeJoinPlan {
    // 1. Collect positive body atoms. Negated atoms (sign == false) are dropped;
    //    stratified negation is unimplemented. See test_negation (xfail).
    let positive_atoms: Vec<(usize, &datalog_syntax::Atom)> = rule
        .body
        .iter()
        .enumerate()
        .filter(|(_, atom)| atom.sign)
        .collect();

    // 2. Extract variable-to-atom incidence for positive atoms
    //    var -> [(atom_body_idx, col_idx)]
    let mut var_atoms: Vec<(Var, Vec<(usize, usize)>)> = Vec::new();
    let mut var_seen_order: Vec<Var> = Vec::new();

    for &(body_idx, atom) in &positive_atoms {
        for (col_idx, term) in atom.terms.iter().enumerate() {
            if let Term::Variable(v) = term {
                if !var_seen_order.contains(v) {
                    var_seen_order.push(v.clone());
                    var_atoms.push((v.clone(), Vec::new()));
                }
                let entry = var_atoms.iter_mut().find(|(name, _)| name == v).unwrap();
                entry.1.push((body_idx, col_idx));
            }
        }
    }

    // 3. Choose variable ordering
    let var_order = choose_variable_order(&positive_atoms, &var_atoms);

    // 4. Build plan tree
    let root = build_plan_tree(
        &positive_atoms,
        &var_order,
        &var_atoms,
        0,
        &HashSet::new(),
    );

    // 5. Build projection from head
    let projection = rule
        .head
        .terms
        .iter()
        .map(|t| match t {
            Term::Variable(v) => ProjectionEntry::Variable(v.clone()),
            Term::Constant(c) => ProjectionEntry::Constant(c.clone()),
        })
        .collect();

    // 6. Collect IDB body relations (positive only, in body order)
    //    Note: at this stage we don't know which are IDB vs EDB, so we store all.
    //    The evaluation loop will determine IDB status.
    let idb_body_relations: Vec<(String, usize)> = positive_atoms
        .iter()
        .map(|&(body_idx, atom)| (atom.symbol.clone(), body_idx))
        .collect();

    let all_body_relations: Vec<String> = rule
        .body
        .iter()
        .map(|atom| atom.symbol.clone())
        .collect();

    FreeJoinPlan {
        root,
        head_symbol: rule.head.symbol.clone(),
        projection,
        idb_body_relations,
        all_body_relations,
    }
}

/// Choose variable ordering: variables appearing in more atoms first,
/// breaking ties by preferring magic/demand predicates.
fn choose_variable_order(
    positive_atoms: &[(usize, &datalog_syntax::Atom)],
    var_atoms: &[(Var, Vec<(usize, usize)>)],
) -> Vec<Var> {
    let mut order: Vec<(Var, usize, bool)> = var_atoms
        .iter()
        .map(|(var, occurrences)| {
            let atom_indices: HashSet<usize> =
                occurrences.iter().map(|(atom_idx, _)| *atom_idx).collect();
            let count = atom_indices.len();
            let has_magic = occurrences.iter().any(|(atom_idx, _)| {
                let symbol = &positive_atoms
                    .iter()
                    .find(|(bi, _)| *bi == *atom_idx)
                    .unwrap()
                    .1
                    .symbol;
                symbol.starts_with("magic_") || symbol.starts_with("m_") || symbol.starts_with("d_")
            });
            (var.clone(), count, has_magic)
        })
        .collect();

    // Sort: more atom occurrences first, then magic predicates first, then alphabetical
    order.sort_by(|a, b| {
        b.1.cmp(&a.1)
            .then(b.2.cmp(&a.2))
            .then(a.0.cmp(&b.0))
    });

    order.into_iter().map(|(var, _, _)| var).collect()
}

/// Build the plan tree recursively, one level per variable.
fn build_plan_tree(
    positive_atoms: &[(usize, &datalog_syntax::Atom)],
    var_order: &[Var],
    var_atoms: &[(Var, Vec<(usize, usize)>)],
    level: usize,
    bound_vars: &HashSet<Var>,
) -> FreeJoinNode {
    if level >= var_order.len() {
        return FreeJoinNode {
            new_vars: vec![],
            iterate: vec![],
            probe: vec![],
            filters: vec![],
            children: vec![],
        };
    }

    let var = &var_order[level];
    let occurrences = &var_atoms.iter().find(|(v, _)| v == var).unwrap().1;

    // Constant filters collected inline below: each constant -> prefix binding + filters entry.
    let mut filters = Vec::new();

    // Build subatoms for each atom that mentions this variable.
    // IMPORTANT: bindings must be ordered so that already-bound variables come first
    // (they form the trie prefix), followed by the new variable being bound at this level.
    // This ensures the trie column ordering matches the navigation pattern.
    let mut subatoms: Vec<SubAtom> = Vec::new();
    for &(atom_body_idx, _col_idx) in occurrences {
        let atom = positive_atoms
            .iter()
            .find(|(bi, _)| *bi == atom_body_idx)
            .unwrap()
            .1;

        // Separate bindings into: already-bound (prefix) and new variable
        let mut prefix_bindings: Vec<(usize, Var)> = Vec::new();
        let mut new_bindings: Vec<(usize, Var)> = Vec::new();

        for (ci, term) in atom.terms.iter().enumerate() {
            match term {
                Term::Variable(v) => {
                    if bound_vars.contains(v) {
                        prefix_bindings.push((ci, v.clone()));
                    } else if v == var {
                        new_bindings.push((ci, v.clone()));
                    }
                }
                Term::Constant(c) => {
                    // Constants are treated as pre-bound: they become part of the prefix
                    let const_var = format!("__const_{}_{}_{}", atom.symbol, atom_body_idx, ci);
                    prefix_bindings.push((ci, const_var.clone()));
                    filters.push((const_var, c.clone()));
                }
            }
        }

        // Combine: prefix (bound) first, then new variable
        let mut bindings = prefix_bindings;
        bindings.extend(new_bindings);

        subatoms.push(SubAtom {
            relation: atom.symbol.clone(),
            bindings,
        });
    }

    // First subatom iterates, rest probe
    let iterate = if subatoms.is_empty() {
        vec![]
    } else {
        vec![subatoms.remove(0)]
    };
    let probe = subatoms;

    // Recurse
    let mut new_bound = bound_vars.clone();
    new_bound.insert(var.clone());

    let child = build_plan_tree(
        positive_atoms,
        var_order,
        var_atoms,
        level + 1,
        &new_bound,
    );

    FreeJoinNode {
        new_vars: vec![var.clone()],
        iterate,
        probe,
        filters,
        children: vec![child],
    }
}

/// Analyze plans to determine which trie orderings each relation needs.
pub fn collect_required_orderings(plans: &[FreeJoinPlan]) -> HashMap<String, Vec<Vec<usize>>> {
    let mut orderings: HashMap<String, HashSet<Vec<usize>>> = HashMap::new();

    for plan in plans {
        collect_orderings_from_node(&plan.root, &mut orderings);
    }

    orderings
        .into_iter()
        .map(|(rel, set)| (rel, set.into_iter().collect()))
        .collect()
}

fn collect_orderings_from_node(
    node: &FreeJoinNode,
    orderings: &mut HashMap<String, HashSet<Vec<usize>>>,
) {
    // Collect from iterate subatoms
    for subatom in &node.iterate {
        let cols: Vec<usize> = subatom.bindings.iter().map(|(col, _)| *col).collect();
        if !cols.is_empty() {
            orderings
                .entry(subatom.relation.clone())
                .or_default()
                .insert(cols);
        }
    }

    // Collect from probe subatoms
    for subatom in &node.probe {
        let cols: Vec<usize> = subatom.bindings.iter().map(|(col, _)| *col).collect();
        if !cols.is_empty() {
            orderings
                .entry(subatom.relation.clone())
                .or_default()
                .insert(cols);
        }
    }

    // Recurse into children
    for child in &node.children {
        collect_orderings_from_node(child, orderings);
    }
}

// ============================================================================
// Plan executor
// ============================================================================

/// Execute a Free Join plan with given delta modes, producing output tuples.
pub fn execute_free_join_plan(
    plan: &FreeJoinPlan,
    trie_storage: &TrieStorage,
    delta_modes: &HashMap<String, DeltaMode>,
) -> Vec<AnonymousGroundAtom> {
    let mut output = Vec::new();
    let mut bindings = Bindings::new();

    execute_node(
        &plan.root,
        trie_storage,
        delta_modes,
        &mut bindings,
        &mut output,
        &plan.projection,
    );

    output
}

fn execute_node(
    node: &FreeJoinNode,
    trie_storage: &TrieStorage,
    delta_modes: &HashMap<String, DeltaMode>,
    bindings: &mut Bindings,
    output: &mut Vec<AnonymousGroundAtom>,
    projection: &[ProjectionEntry],
) {
    // Base case: all variables bound, produce output
    if node.iterate.is_empty() && node.children.is_empty() {
        // Produce output tuple
        let tuple: AnonymousGroundAtom = projection
            .iter()
            .map(|entry| match entry {
                ProjectionEntry::Variable(var) => bindings.get(var).unwrap().clone(),
                ProjectionEntry::Constant(val) => val.clone(),
            })
            .collect();
        output.push(tuple);
        return;
    }

    if node.iterate.is_empty() {
        // No iterate at this level but has children — just recurse
        for child in &node.children {
            execute_node(child, trie_storage, delta_modes, bindings, output, projection);
        }
        return;
    }

    // Get the primary iterate subatom
    let iterate_subatom = &node.iterate[0];
    let mode = delta_modes
        .get(&iterate_subatom.relation)
        .copied()
        .unwrap_or(DeltaMode::Full);

    // Build prefix from already-bound variables
    let mut prefix: Vec<TypedValue> = Vec::new();

    for (_i, (_col, var)) in iterate_subatom.bindings.iter().enumerate() {
        if let Some(val) = bindings.get(var) {
            prefix.push(val.clone());
        } else {
            // This is a new variable — it's the one we'll iterate over
            break;
        }
    }

    let col_order: Vec<usize> = iterate_subatom.bindings.iter().map(|(col, _)| *col).collect();

    let nav_result = trie_storage.navigate(
        &iterate_subatom.relation,
        &col_order,
        &prefix,
        mode,
    );

    if let Some(nav) = nav_result {
        if node.new_vars.is_empty() {
            // No new variables to bind at this level — just verify existence and continue
            // Check probes
            let all_probes_succeed = check_probes(&node.probe, trie_storage, delta_modes, bindings);
            let filters_pass = check_filters(&node.filters, bindings);

            if all_probes_succeed && filters_pass {
                for child in &node.children {
                    execute_node(child, trie_storage, delta_modes, bindings, output, projection);
                }
            }
        } else {
            let new_var = &node.new_vars[0];

            // Iterate over all values at this trie level
            for (value, _subtrie) in nav.iter_entries() {
                // Bind the new variable
                bindings.bind(new_var, value.clone());
                let num_bound = 1;

                // Check constant filters
                let filters_pass = check_filters(&node.filters, bindings);
                if !filters_pass {
                    bindings.unbind_last_n(num_bound);
                    continue;
                }

                // Probe all probe subatoms
                let all_probes_succeed =
                    check_probes(&node.probe, trie_storage, delta_modes, bindings);

                if all_probes_succeed {
                    for child in &node.children {
                        execute_node(
                            child,
                            trie_storage,
                            delta_modes,
                            bindings,
                            output,
                            projection,
                        );
                    }
                }

                bindings.unbind_last_n(num_bound);
            }
        }
    }
}

fn check_probes(
    probes: &[SubAtom],
    trie_storage: &TrieStorage,
    delta_modes: &HashMap<String, DeltaMode>,
    bindings: &Bindings,
) -> bool {
    probes.iter().all(|probe_subatom| {
        let probe_mode = delta_modes
            .get(&probe_subatom.relation)
            .copied()
            .unwrap_or(DeltaMode::Full);
        let probe_prefix: Vec<TypedValue> = probe_subatom
            .bindings
            .iter()
            .filter_map(|(_, var)| bindings.get(var).cloned())
            .collect();
        let probe_col_order: Vec<usize> =
            probe_subatom.bindings.iter().map(|(col, _)| *col).collect();
        trie_storage
            .navigate(
                &probe_subatom.relation,
                &probe_col_order,
                &probe_prefix,
                probe_mode,
            )
            .is_some()
    })
}

fn check_filters(filters: &[(Var, TypedValue)], bindings: &Bindings) -> bool {
    filters.iter().all(|(var, expected)| {
        bindings.get(var).map_or(true, |v| v == expected)
    })
}

// ============================================================================
// Semi-naive delta evaluation for a single rule
// ============================================================================

/// Evaluate a single rule using Free Join with m-way delta decomposition.
/// For a rule with m IDB body relations, evaluates m times:
///   Pass i: relation i uses DeltaOnly, j<i uses OldOnly, j>i uses Full.
/// EDB relations always use Full.
/// Returns newly derived facts (not deduplicated).
pub fn evaluate_rule_delta(
    plan: &FreeJoinPlan,
    trie_storage: &TrieStorage,
    idb_relations: &HashSet<String>,
) -> Vec<AnonymousGroundAtom> {
    let mut all_results = Vec::new();

    // Only delta-decompose over IDB body relations
    let idb_body: Vec<&(String, usize)> = plan
        .idb_body_relations
        .iter()
        .filter(|(rel, _)| idb_relations.contains(rel))
        .collect();

    if idb_body.is_empty() {
        // Pure EDB rule — evaluate once with Full mode
        let delta_modes: HashMap<String, DeltaMode> = plan
            .all_body_relations
            .iter()
            .map(|r| (r.clone(), DeltaMode::Full))
            .collect();
        let results = execute_free_join_plan(plan, trie_storage, &delta_modes);
        all_results.extend(results);
        return all_results;
    }

    let m = idb_body.len();
    for i in 0..m {
        let delta_rel = &idb_body[i].0;

        // Skip if no deltas for this relation
        if !trie_storage.has_delta(delta_rel) {
            continue;
        }

        let mut delta_modes: HashMap<String, DeltaMode> = HashMap::new();

        // EDB relations always Full
        for rel in &plan.all_body_relations {
            if !idb_relations.contains(rel) {
                delta_modes.insert(rel.clone(), DeltaMode::Full);
            }
        }

        // IDB relations: j<i OldOnly, j==i DeltaOnly, j>i Full
        for (j, (rel, _)) in idb_body.iter().enumerate() {
            if j < i {
                delta_modes.insert(rel.clone(), DeltaMode::OldOnly);
            } else if j == i {
                delta_modes.insert(rel.clone(), DeltaMode::DeltaOnly);
            } else {
                delta_modes.insert(rel.clone(), DeltaMode::Full);
            }
        }

        let results = execute_free_join_plan(plan, trie_storage, &delta_modes);
        all_results.extend(results);
    }

    all_results
}

/// Evaluate a rule in Full mode (no delta decomposition).
/// Used for nonrecursive rules.
pub fn evaluate_rule_full(
    plan: &FreeJoinPlan,
    trie_storage: &TrieStorage,
) -> Vec<AnonymousGroundAtom> {
    let delta_modes: HashMap<String, DeltaMode> = plan
        .all_body_relations
        .iter()
        .map(|r| (r.clone(), DeltaMode::Full))
        .collect();
    execute_free_join_plan(plan, trie_storage, &delta_modes)
}

// ============================================================================
// Main evaluation functions
// ============================================================================

/// Replacement for `semi_naive_evaluation` using Free Join.
///
/// 1. Compiles all rules to FreeJoinPlans
/// 2. Determines which column orderings are needed per relation
/// 3. Builds TrieStorage from current RelationStorage
/// 4. Evaluates nonrecursive rules once (Full mode)
/// 5. Fixpoint loop for recursive rules with m-way delta
pub fn free_join_evaluation(
    relation_storage: &mut RelationStorage,
    nonrecursive_program: &Program,
    recursive_program: &Program,
) {
    // Compile all rules
    let nonrecursive_plans = compile_plans(nonrecursive_program);
    let recursive_plans = compile_plans(recursive_program);

    // Determine IDB relations (anything that appears as a rule head)
    let idb_relations: HashSet<String> = nonrecursive_program
        .inner
        .iter()
        .chain(recursive_program.inner.iter())
        .map(|r| r.head.symbol.clone())
        .collect();

    // Build trie storage
    let all_plans: Vec<FreeJoinPlan> = nonrecursive_plans
        .iter()
        .chain(recursive_plans.iter())
        .cloned()
        .collect();
    let mut trie_storage =
        TrieStorage::from_plans_and_storage(&all_plans, relation_storage, &idb_relations);

    // --- Nonrecursive pass: evaluate each rule in Full mode ---
    for plan in &nonrecursive_plans {
        let results = evaluate_rule_full(plan, &trie_storage);
        let current = relation_storage
            .get_relation_safe(&plan.head_symbol);

        let diff: Vec<Arc<AnonymousGroundAtom>> = results
            .into_iter()
            .filter(|fact| {
                current
                    .map_or(true, |rel| !rel.contains(fact))
            })
            .map(|fact| Arc::new(fact))
            .collect();

        if !diff.is_empty() {
            relation_storage.insert_all(
                &plan.head_symbol,
                diff.iter().cloned(),
            );
            // Insert into both main and delta tries
            trie_storage.insert_facts(&plan.head_symbol, &diff, true, true);
        }
    }

    // --- Recursive fixpoint loop ---
    loop {
        let previous_count = relation_storage.len();

        let mut new_facts_by_rel: HashMap<String, Vec<Arc<AnonymousGroundAtom>>> = HashMap::new();

        // Evaluate all recursive rules with delta decomposition
        for plan in &recursive_plans {
            let results = evaluate_rule_delta(plan, &trie_storage, &idb_relations);

            let current = relation_storage.get_relation(&plan.head_symbol);

            let diff: Vec<Arc<AnonymousGroundAtom>> = results
                .into_iter()
                .filter(|fact| !current.contains(fact))
                .map(|fact| Arc::new(fact))
                .collect();

            if !diff.is_empty() {
                relation_storage.insert_all(&plan.head_symbol, diff.iter().cloned());
                new_facts_by_rel
                    .entry(plan.head_symbol.clone())
                    .or_default()
                    .extend(diff);
            }
        }

        let current_count = relation_storage.len();
        if current_count == previous_count {
            return;
        }

        // Clear delta tries, repopulate with only new facts
        trie_storage.clear_all_deltas();
        for (rel_name, facts) in &new_facts_by_rel {
            // Insert into main tries (accumulate) and delta tries (new only)
            trie_storage.insert_facts(rel_name, facts, true, true);
        }
    }
}

// Stratified negation unimplemented; negated atoms dropped at compile_rule.

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::storage::RelationStorage;
    use crate::helpers::helpers::split_program;
    use datalog_rule_macro::program;
    use datalog_syntax::*;

    fn register_relations(storage: &mut RelationStorage, names: &[&str]) {
        for name in names {
            storage
                .inner
                .insert(name.to_string(), Default::default());
        }
    }

    fn insert_into(
        storage: &mut RelationStorage,
        relation_symbol: &str,
        facts: Vec<AnonymousGroundAtom>,
    ) {
        facts.into_iter().for_each(|fact| {
            storage
                .inner
                .get_mut(relation_symbol)
                .unwrap()
                .insert(Arc::new(fact));
        });
    }

    fn collect_relation(
        storage: &RelationStorage,
        name: &str,
    ) -> HashSet<AnonymousGroundAtom> {
        storage
            .get_relation(name)
            .into_iter()
            .map(|x| (**x).clone())
            .collect()
    }

    // ========================================================================
    // Plan compilation tests
    // ========================================================================

    #[test]
    fn test_compile_single_atom_rule() {
        // tc(X, Y) <- e(X, Y)
        let prog = program! { tc(?x, ?y) <- [e(?x, ?y)] };
        let plans = compile_plans(&prog);
        assert_eq!(plans.len(), 1);
        assert_eq!(plans[0].head_symbol, "tc");
        assert_eq!(plans[0].all_body_relations, vec!["e".to_string()]);
    }

    #[test]
    fn test_compile_two_atom_rule() {
        // tc(X, Z) <- e(X, Y), tc(Y, Z)
        let prog = program! { tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)] };
        let plans = compile_plans(&prog);
        assert_eq!(plans.len(), 1);
        let plan = &plans[0];
        assert_eq!(plan.head_symbol, "tc");
        // Y appears in both atoms, so it should be ordered first
        // The root level should iterate/probe on Y or the variable with most connections
    }

    #[test]
    fn test_compile_three_atom_rule() {
        // result(Y, Z) <- magic(X, Z), parent(X, Y), ancestor(Y, Z)
        let prog = program! {
            result(?y, ?z) <- [magic(?x, ?z), parent(?x, ?y), ancestor(?y, ?z)]
        };
        let plans = compile_plans(&prog);
        assert_eq!(plans.len(), 1);
        assert_eq!(plans[0].all_body_relations.len(), 3);
    }

    #[test]
    fn test_collect_required_orderings() {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let plans = compile_plans(&prog);
        let orderings = collect_required_orderings(&plans);
        // Both "e" and "tc" should have orderings
        assert!(orderings.contains_key("e"));
        assert!(orderings.contains_key("tc"));
    }

    // ========================================================================
    // Linear transitive closure
    // ========================================================================

    #[test]
    fn test_linear_tc_free_join() {
        let mut storage: RelationStorage = Default::default();
        register_relations(&mut storage, &["e", "tc"]);
        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()],
            ],
        );

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let (nonrecursive, recursive) = split_program(tc_program);

        free_join_evaluation(&mut storage, &nonrecursive, &recursive);

        let result = collect_relation(&storage, "tc");
        let expected: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            vec!["a".into(), "d".into()],
        ]
        .into_iter()
        .collect();

        assert_eq!(expected, result);
    }

    // ========================================================================
    // Nonlinear transitive closure
    // ========================================================================

    #[test]
    fn test_nonlinear_tc_free_join() {
        let mut storage: RelationStorage = Default::default();
        register_relations(&mut storage, &["e", "tc"]);
        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()],
            ],
        );

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
        };
        let (nonrecursive, recursive) = split_program(tc_program);

        free_join_evaluation(&mut storage, &nonrecursive, &recursive);

        let result = collect_relation(&storage, "tc");
        let expected: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
            vec!["a".into(), "c".into()],
            vec!["b".into(), "d".into()],
            vec!["a".into(), "d".into()],
        ]
        .into_iter()
        .collect();

        assert_eq!(expected, result);
    }

    // ========================================================================
    // Parity tests — same results as semi_naive_evaluation
    // ========================================================================

    #[test]
    fn test_parity_one_hop() {
        let mut storage_spj: RelationStorage = Default::default();
        let mut storage_fj: RelationStorage = Default::default();

        for storage in [&mut storage_spj, &mut storage_fj] {
            register_relations(storage, &["e", "hop"]);
            insert_into(
                storage,
                "e",
                vec![vec!["a".into(), "b".into()], vec!["b".into(), "c".into()]],
            );
        }

        let prog = program! { hop(?x, ?z) <- [e(?x, ?y), e(?y, ?z)] };
        let (nonrecursive, recursive) = split_program(prog.clone());

        crate::evaluation::semi_naive::semi_naive_evaluation(
            &mut storage_spj,
            &nonrecursive,
            &recursive,
        );

        let (nonrecursive2, recursive2) = split_program(prog);
        free_join_evaluation(&mut storage_fj, &nonrecursive2, &recursive2);

        assert_eq!(
            collect_relation(&storage_spj, "hop"),
            collect_relation(&storage_fj, "hop"),
        );
    }

    #[test]
    fn test_parity_linear_tc() {
        let mut storage_spj: RelationStorage = Default::default();
        let mut storage_fj: RelationStorage = Default::default();

        let edges = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
        ];

        for storage in [&mut storage_spj, &mut storage_fj] {
            register_relations(storage, &["e", "tc"]);
            insert_into(storage, "e", edges.clone());
        }

        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };

        let (nr, r) = split_program(prog.clone());
        crate::evaluation::semi_naive::semi_naive_evaluation(&mut storage_spj, &nr, &r);

        let (nr2, r2) = split_program(prog);
        free_join_evaluation(&mut storage_fj, &nr2, &r2);

        assert_eq!(
            collect_relation(&storage_spj, "tc"),
            collect_relation(&storage_fj, "tc"),
        );
    }

    #[test]
    fn test_parity_nonlinear_tc() {
        let mut storage_spj: RelationStorage = Default::default();
        let mut storage_fj: RelationStorage = Default::default();

        let edges = vec![
            vec!["a".into(), "b".into()],
            vec!["b".into(), "c".into()],
            vec!["c".into(), "d".into()],
        ];

        for storage in [&mut storage_spj, &mut storage_fj] {
            register_relations(storage, &["e", "tc"]);
            insert_into(storage, "e", edges.clone());
        }

        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
        };

        let (nr, r) = split_program(prog.clone());
        crate::evaluation::semi_naive::semi_naive_evaluation(&mut storage_spj, &nr, &r);

        let (nr2, r2) = split_program(prog);
        free_join_evaluation(&mut storage_fj, &nr2, &r2);

        assert_eq!(
            collect_relation(&storage_spj, "tc"),
            collect_relation(&storage_fj, "tc"),
        );
    }

    #[test]
    fn test_cross_product_free_join() {
        // Cross product: pair(X, Y) <- p(X), q(Y)
        // No shared variables between p and q — Free Join handles this
        // by processing each variable at a separate level.
        let mut storage: RelationStorage = Default::default();
        register_relations(&mut storage, &["p", "q", "pair"]);
        insert_into(&mut storage, "p", vec![vec!["a".into()], vec!["b".into()]]);
        insert_into(
            &mut storage,
            "q",
            vec![
                vec!["1".into()],
                vec!["2".into()],
                vec!["3".into()],
            ],
        );

        let prog = program! { pair(?x, ?y) <- [p(?x), q(?y)] };
        let (nr, r) = split_program(prog);
        free_join_evaluation(&mut storage, &nr, &r);

        let result = collect_relation(&storage, "pair");
        let expected: HashSet<AnonymousGroundAtom> = vec![
            vec!["a".into(), "1".into()],
            vec!["a".into(), "2".into()],
            vec!["a".into(), "3".into()],
            vec!["b".into(), "1".into()],
            vec!["b".into(), "2".into()],
            vec!["b".into(), "3".into()],
        ]
        .into_iter()
        .collect();
        assert_eq!(expected, result);
    }

    // ========================================================================
    // Additional correctness tests
    // ========================================================================

    #[test]
    fn test_longer_chain_tc() {
        let mut storage: RelationStorage = Default::default();
        register_relations(&mut storage, &["e", "tc"]);
        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "d".into()],
                vec!["d".into(), "e".into()],
                vec!["e".into(), "f".into()],
            ],
        );

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let (nonrecursive, recursive) = split_program(tc_program);
        free_join_evaluation(&mut storage, &nonrecursive, &recursive);

        let result = collect_relation(&storage, "tc");
        // 5 direct + 4 two-hop + 3 three-hop + 2 four-hop + 1 five-hop = 15
        assert_eq!(result.len(), 15);
        // Check specific long-range path
        assert!(result.contains(&vec!["a".into(), "f".into()]));
    }

    #[test]
    fn test_cyclic_graph_tc() {
        let mut storage: RelationStorage = Default::default();
        register_relations(&mut storage, &["e", "tc"]);
        insert_into(
            &mut storage,
            "e",
            vec![
                vec!["a".into(), "b".into()],
                vec!["b".into(), "c".into()],
                vec!["c".into(), "a".into()], // cycle
            ],
        );

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let (nonrecursive, recursive) = split_program(tc_program);
        free_join_evaluation(&mut storage, &nonrecursive, &recursive);

        let result = collect_relation(&storage, "tc");
        // Full closure of 3-node cycle: every pair including self-loops
        // (a,b), (b,c), (c,a), (a,c), (b,a), (c,b), (a,a), (b,b), (c,c)
        assert_eq!(result.len(), 9);
    }

    #[test]
    fn test_empty_base_relation() {
        let mut storage: RelationStorage = Default::default();
        register_relations(&mut storage, &["e", "tc"]);
        // e is empty

        let tc_program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };
        let (nonrecursive, recursive) = split_program(tc_program);
        free_join_evaluation(&mut storage, &nonrecursive, &recursive);

        let result = collect_relation(&storage, "tc");
        assert!(result.is_empty());
    }

}
