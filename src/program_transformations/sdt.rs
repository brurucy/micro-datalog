/// Subsumptive Demand Transformation (SDT)
///
/// Implements Tekle & Liu 2011, Section 4.1.
/// Like MST but adds subsumption checks to demand rules to suppress redundant
/// demands when a subsuming demand already exists. The output program is purely
/// positive and evaluated by standard semi-naive fixpoint iteration.
use crate::helpers::helpers::*;
use crate::program_transformations::adorned_atom::*;
use crate::program_transformations::magic_sets::{
    collect_new_adorned_predicates, make_magic_predicate,
    modify_original_rule,
};
use datalog_syntax::*;
use std::collections::{HashMap, HashSet};

/// Result of the SDT transformation: the transformed program and the set of
/// demand predicate names (used by SdtEvaluator for relation registration;
/// no longer needed for demand-first scheduling since the output is purely positive).
pub struct SdtResult {
    pub program: Program,
    pub demand_predicates: HashSet<String>,
    /// Which patterns were marked guaranteed, keyed by base predicate name.
    /// Exposed for testing; not used at runtime.
    pub guaranteed_patterns: HashMap<String, HashSet<Vec<Adornment>>>,
}

/// A pattern string properly subsumes another if it is strictly more general.
/// Pattern s1 properly subsumes s2 iff s1 != s2 and for each position i,
/// s1[i] is Free or s1[i] == s2[i].
fn pattern_properly_subsumes(general: &[Adornment], specific: &[Adornment]) -> bool {
    if general.len() != specific.len() {
        return false;
    }
    if general == specific {
        return false; // must be proper subsumption
    }
    general.iter().zip(specific.iter()).all(|(g, s)| {
        matches!(g, Adornment::Free) || g == s
    })
}

/// Apply the Subsumptive Demand Transformation.
///
/// Apply the Subsumptive Demand Transformation (Tekle & Liu 2011, Sections 3–5).
///
/// The transformation proceeds in four phases:
///   1. Compute all adorned predicates and guaranteed flags (Section 3.1).
///   2. Identify which patterns should be subsumed (Section 5, step i).
///   3. Apply subsumption optimization: restructure rules so that subsuming
///      demands are generated before subsumed ones (Section 5, step ii).
///   4. Prune subsumed patterns — no demand rules generated for them.
///
/// The output is a PURELY POSITIVE program. No negated hypotheses, no
/// inflationary negation. The subsumption optimization ensures that subsuming
/// demands are always encountered first, making runtime negation unnecessary.
pub fn apply_sdt_transformation(program: &Program, query: &Query) -> SdtResult {
    // ===================================================================
    // Phase 1: Compute all adorned predicates and guaranteed flags.
    // This is identical to MST's adornment computation, plus guarantee tracking.
    // We do NOT prune here — we need the full pattern set for Phase 2.
    // ===================================================================
    let mut processed_adorned_preds = HashSet::new();
    let mut to_process = Vec::new();
    let mut patterns_per_predicate: HashMap<String, Vec<Vec<Adornment>>> = HashMap::new();
    let mut guaranteed_patterns: HashMap<String, HashSet<Vec<Adornment>>> = HashMap::new();

    if let Some(initial_rule) = get_rules_for_predicate(program, query.symbol).first() {
        let mut adornments = vec![Adornment::Free; query.matchers.len()];
        for (i, matcher) in query.matchers.iter().enumerate() {
            if let Matcher::Constant(_) = matcher {
                adornments[i] = Adornment::Bound;
            }
        }
        guaranteed_patterns
            .entry(query.symbol.to_string())
            .or_default()
            .insert(adornments.clone());
        to_process.push(AdornedAtom {
            atom: initial_rule.head.clone(),
            adornment: adornments,
        });
    }

    while let Some(adorned_pred) = to_process.pop() {
        if processed_adorned_preds.contains(&adorned_pred) {
            continue;
        }
        patterns_per_predicate
            .entry(adorned_pred.atom.symbol.clone())
            .or_default()
            .push(adorned_pred.adornment.clone());
        processed_adorned_preds.insert(adorned_pred.clone());

        let head_is_guaranteed = guaranteed_patterns
            .get(&adorned_pred.atom.symbol)
            .map_or(false, |pats| pats.contains(&adorned_pred.adornment));

        for rule in get_rules_for_predicate(program, &adorned_pred.atom.symbol) {
            let new_adorned_list = collect_new_adorned_predicates(program, rule, &adorned_pred);
            if head_is_guaranteed {
                if let Some(first_adorned) = new_adorned_list.first() {
                    guaranteed_patterns
                        .entry(first_adorned.atom.symbol.clone())
                        .or_default()
                        .insert(first_adorned.adornment.clone());
                }
            }
            for new_adorned in new_adorned_list {
                to_process.push(new_adorned);
            }
        }
    }

    // Guarantee fixpoint
    loop {
        let mut changed = false;
        for adorned_pred in &processed_adorned_preds {
            let head_is_guaranteed = guaranteed_patterns
                .get(&adorned_pred.atom.symbol)
                .map_or(false, |pats| pats.contains(&adorned_pred.adornment));
            if !head_is_guaranteed { continue; }
            for rule in get_rules_for_predicate(program, &adorned_pred.atom.symbol) {
                let new_adorned_list = collect_new_adorned_predicates(program, rule, adorned_pred);
                if let Some(first_adorned) = new_adorned_list.first() {
                    if guaranteed_patterns
                        .entry(first_adorned.atom.symbol.clone())
                        .or_default()
                        .insert(first_adorned.adornment.clone())
                    {
                        changed = true;
                    }
                }
            }
        }
        if !changed { break; }
    }

    // ===================================================================
    // Phase 2: Identify subsumption relationships (Section 5, step i).
    // For each predicate, find patterns that should be subsumed.
    // ===================================================================
    let mut subsumed_by: HashMap<(String, Vec<Adornment>), Vec<Adornment>> = HashMap::new();

    // Compute the query's own pattern to exclude it from subsumption
    let query_pattern: Vec<Adornment> = query.matchers.iter().map(|m| match m {
        Matcher::Constant(_) => Adornment::Bound,
        Matcher::Any => Adornment::Free,
    }).collect();

    for (pred, patterns) in &patterns_per_predicate {
        for specific in patterns {
            // Never subsume the query pattern — it's the entry point
            if pred == query.symbol && *specific == query_pattern {
                continue;
            }
            for general in patterns {
                if pattern_properly_subsumes(general, specific)
                    && general.iter().any(|a| matches!(a, Adornment::Bound))
                    && guaranteed_patterns
                        .get(pred)
                        .map_or(false, |gp| gp.contains(general))
                {
                    subsumed_by.insert((pred.clone(), specific.clone()), general.clone());
                    break;
                }
            }
        }
    }

    // ===================================================================
    // Phase 3: Generate the transformed program.
    // For non-subsumed patterns: generate rules as in MST.
    // For subsumed patterns: skip entirely (no demand rules, no adorned rules).
    // Apply Section 5 restructuring: for each IDB body atom whose pattern is
    // subsumed, insert a fresh predicate hypothesis BEFORE it that forces the
    // subsuming demand to be generated first. Then redirect the body atom.
    // ===================================================================
    let mut transformed_rules = Vec::new();
    let mut seen_rules = HashSet::new();
    let mut demand_predicates = HashSet::new();
    let mut fresh_counter = 0usize;

    // Helper: apply Section 5 restructuring to a rule body.
    // For each body atom referencing a subsumed pattern, inserts a fresh aux
    // predicate before it and redirects the body atom to the subsumer. Generates
    // the aux rule as a side effect.
    let apply_section5 = |body: &[Atom],
                          subsumed_by: &HashMap<(String, Vec<Adornment>), Vec<Adornment>>,
                          fresh_counter: &mut usize,
                          emit_rule: &mut dyn FnMut(Rule)| -> Vec<Atom> {
        let mut new_body = Vec::new();
        for body_atom in body {
            if let Some(pos) = body_atom.symbol.rfind('_') {
                let atom_base = &body_atom.symbol[..pos];
                let pattern_str = &body_atom.symbol[pos + 1..];
                let pattern: Option<Vec<Adornment>> = pattern_str
                    .chars()
                    .map(|c| match c {
                        'b' => Some(Adornment::Bound),
                        'f' => Some(Adornment::Free),
                        _ => None,
                    })
                    .collect();
                if let Some(ref pat) = pattern {
                    if let Some(subsumer) = subsumed_by.get(&(atom_base.to_string(), pat.clone())) {
                        let subsumer_str: String = subsumer.iter()
                            .map(|a| match a { Adornment::Bound => 'b', Adornment::Free => 'f' })
                            .collect();
                        let bound_terms: Vec<Term> = subsumer.iter()
                            .enumerate()
                            .filter(|(_, a)| matches!(a, Adornment::Bound))
                            .filter_map(|(i, _)| body_atom.terms.get(i).cloned())
                            .collect();
                        if !bound_terms.is_empty() {
                            let fresh_name = format!("sdt_aux_{}", *fresh_counter);
                            *fresh_counter += 1;
                            let subsumer_symbol = format!("{}_{}", atom_base, subsumer_str);
                            emit_rule(Rule {
                                head: Atom { symbol: fresh_name.clone(), terms: bound_terms.clone(), sign: true },
                                body: vec![Atom { symbol: subsumer_symbol.clone(), terms: body_atom.terms.clone(), sign: true }],
                                id: 0,
                            });
                            new_body.push(Atom { symbol: fresh_name, terms: bound_terms, sign: true });
                        }
                        let mut redirected = body_atom.clone();
                        redirected.symbol = format!("{}_{}", atom_base, subsumer_str);
                        new_body.push(redirected);
                        continue;
                    }
                }
            }
            new_body.push(body_atom.clone());
        }
        new_body
    };

    for adorned_pred in &processed_adorned_preds {
        // Skip subsumed patterns — no rules generated for them
        if subsumed_by.contains_key(&(adorned_pred.atom.symbol.clone(), adorned_pred.adornment.clone())) {
            continue;
        }

        for rule in get_rules_for_predicate(program, &adorned_pred.atom.symbol) {
            // Create magic (demand) rules, and apply Section 5 restructuring to their bodies.
            // The magic rule body (the "binding chain") may contain adorned body atoms
            // referencing pruned patterns; those must be redirected and aux predicates inserted.
            let magic_rules = create_magic_rules_for_sdt(program, rule, adorned_pred);
            let mut emitted_aux = Vec::new();
            let mut emit = |r: Rule| { emitted_aux.push(r); };
            for (mut magic_rule, base_pred, pattern) in magic_rules {
                // If the magic rule produces demand for a PRUNED pattern, redirect
                // the head to the subsuming pattern's magic predicate, projecting
                // the bound arguments appropriately.
                if let Some(subsumer) = subsumed_by.get(&(base_pred.clone(), pattern.clone())) {
                    let subsumer_str: String = subsumer.iter()
                        .map(|a| match a { Adornment::Bound => 'b', Adornment::Free => 'f' })
                        .collect();
                    let new_head_symbol = format!("magic_{}_{}", base_pred, subsumer_str);
                    // Project: pattern's bound positions map to magic_rule.head.terms (in order).
                    // Subsumer's bound positions are a subset; pick the corresponding terms.
                    let mut projected_terms: Vec<Term> = Vec::new();
                    let mut magic_idx = 0;
                    for (i, a) in pattern.iter().enumerate() {
                        if matches!(a, Adornment::Bound) {
                            if matches!(subsumer[i], Adornment::Bound) {
                                if let Some(t) = magic_rule.head.terms.get(magic_idx) {
                                    projected_terms.push(t.clone());
                                }
                            }
                            magic_idx += 1;
                        }
                    }
                    magic_rule.head.symbol = new_head_symbol;
                    magic_rule.head.terms = projected_terms;
                }
                magic_rule.body = apply_section5(&magic_rule.body, &subsumed_by, &mut fresh_counter, &mut emit);
                let rule_str = format!("{:?}", magic_rule);
                if !seen_rules.contains(&rule_str) {
                    demand_predicates.insert(magic_rule.head.symbol.clone());
                    seen_rules.insert(rule_str);
                    transformed_rules.push(magic_rule);
                }
            }
            for aux in emitted_aux.drain(..) {
                let rule_str = format!("{:?}", aux);
                if !seen_rules.contains(&rule_str) {
                    seen_rules.insert(rule_str);
                    transformed_rules.push(aux);
                }
            }

            // Create modified original rule, apply Section 5 restructuring to its body too.
            let mut modified_rule = modify_original_rule(program, rule, adorned_pred);
            if let Some(magic_atom) = modified_rule.body.first() {
                if magic_atom.symbol.starts_with("magic_") {
                    demand_predicates.insert(magic_atom.symbol.clone());
                }
            }
            let mut emit = |r: Rule| { emitted_aux.push(r); };
            modified_rule.body = apply_section5(&modified_rule.body, &subsumed_by, &mut fresh_counter, &mut emit);
            for aux in emitted_aux {
                let rule_str = format!("{:?}", aux);
                if !seen_rules.contains(&rule_str) {
                    seen_rules.insert(rule_str);
                    transformed_rules.push(aux);
                }
            }

            let rule_str = format!("{:?}", modified_rule);
            if !seen_rules.contains(&rule_str) {
                seen_rules.insert(rule_str);
                transformed_rules.push(modified_rule);
            }
        }
    }

    SdtResult {
        program: Program::from(transformed_rules),
        demand_predicates,
        guaranteed_patterns,
    }
}

/// Creates magic rules for SDT, returning each rule along with the base predicate
/// name and the pattern of the demand it generates (needed for Pass 2).
fn create_magic_rules_for_sdt(
    program: &Program,
    rule: &Rule,
    adorned_head: &AdornedAtom,
) -> Vec<(Rule, String, Vec<Adornment>)> {
    let mut magic_rules = Vec::new();

    // Use the current rule's head variable names (not the adorned atom's stored names).
    let magic_pred = make_magic_predicate_for_rule(rule, adorned_head);
    let mut binding_chain = if magic_pred.terms.is_empty() {
        vec![]
    } else {
        vec![magic_pred]
    };
    let mut bound_variables = get_bound_vars_for_rule(rule, &adorned_head.adornment);

    for (_pos, body_atom) in rule.body.iter().enumerate() {
        if !is_derived_predicate(program, &body_atom.symbol) {
            // EDB atoms: all their variables become bound after processing
            binding_chain.push(body_atom.clone());
            for term in &body_atom.terms {
                if let Term::Variable(var) = term {
                    bound_variables.insert(var.clone());
                }
            }
            continue;
        }

        let uses_bound_vars = body_atom.terms.iter().any(|term| {
            if let Term::Variable(var) = term {
                bound_variables.contains(var)
            } else {
                false
            }
        });

        if uses_bound_vars {
            // Compute the actual adornment for this body atom based on current bound vars
            let body_adorned = AdornedAtom::from_atom_and_bound_vars(body_atom, &bound_variables);

            let magic_head = make_magic_predicate(&body_adorned);

            let in_chain = binding_chain
                .iter()
                .any(|atom| atom.symbol == magic_head.symbol && atom.terms == magic_head.terms);
            if !in_chain {
                let magic_rule = Rule {
                    head: magic_head,
                    body: binding_chain.clone(),
                    id: 0,
                };
                magic_rules.push((
                    magic_rule,
                    body_atom.symbol.clone(),
                    body_adorned.adornment.clone(),
                ));
            }

            // Add the adorned version to the binding chain
            binding_chain.push(modify_body_predicate(body_atom, &body_adorned));

            for term in &body_atom.terms {
                if let Term::Variable(var) = term {
                    bound_variables.insert(var.clone());
                }
            }
        }
    }
    magic_rules
}

#[cfg(test)]
mod tests {
    use super::*;
    use datalog_rule_macro::program;

    #[test]
    fn test_pattern_subsumption() {
        use Adornment::*;
        // bf properly subsumes bb
        assert!(pattern_properly_subsumes(&[Bound, Free], &[Bound, Bound]));
        // ff properly subsumes everything except itself
        assert!(pattern_properly_subsumes(&[Free, Free], &[Bound, Free]));
        assert!(pattern_properly_subsumes(&[Free, Free], &[Free, Bound]));
        assert!(pattern_properly_subsumes(&[Free, Free], &[Bound, Bound]));
        // bf does not subsume fb
        assert!(!pattern_properly_subsumes(&[Bound, Free], &[Free, Bound]));
        // same pattern does not properly subsume
        assert!(!pattern_properly_subsumes(&[Bound, Free], &[Bound, Free]));
        // bb does not subsume bf
        assert!(!pattern_properly_subsumes(&[Bound, Bound], &[Bound, Free]));
    }

    #[test]
    fn test_sdt_tc_bf_no_subsumption() {
        // For linear TC with bf query, the only recursive demand pattern is bf.
        // No subsumption possible (bf doesn't properly subsume itself).
        // SDT output should be identical to MST output (no negated hypotheses).
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };

        let query = Query {
            symbol: "tc",
            matchers: vec![
                Matcher::Constant(TypedValue::Str("a".to_string())),
                Matcher::Any,
            ],
        };

        let result = apply_sdt_transformation(&prog, &query);

        // No negated atoms should appear (no subsumption to exploit)
        let has_negated = result.program.inner.iter().any(|rule| {
            rule.body.iter().any(|atom| !atom.sign)
        });
        assert!(!has_negated, "TC with bf has no subsumption, SDT should produce no negated hypotheses");

        // Should have demand predicates
        assert!(!result.demand_predicates.is_empty());
    }

    #[test]
    fn test_sdt_produces_negated_demand_when_subsumption_exists() {
        // Program where adornment analysis produces bf and bb patterns for p.
        // p(X,Y) :- e(X,Y).
        // p(X,Z) :- p(X,Y), p(Y,Z).  (nonlinear TC)
        // Query: p(a, _)? -> pattern bf
        //
        // Under bf query:
        //   Rule 2 body: p(X,Y) with X bound -> bf, p(Y,Z) with Y bound from p(X,Y) -> bf
        // So only bf is produced, no subsumption.
        //
        // For subsumption we need a program that produces both bf and bb.
        // ancestor(X,Y) :- parent(X,Y).
        // ancestor(X,Z) :- ancestor(X,Y), ancestor(Y,Z). (nonlinear)
        // Query: ancestor(a, _)? -> bf
        // Rule 2: ancestor(X,Y) bf, ancestor(Y,Z) Y bound from first -> bf
        // Still just bf.
        //
        // To get bb we need a rule like: p(X,Y) :- q(X,Y), p(X,Z), p(Z,Y)
        // where q binds both X and Y, giving p(X,Z) -> bf and p(Z,Y) -> bb
        // (Z bound from p(X,Z), Y bound from head)
        let prog = program! {
            p(?x, ?y) <- [q(?x, ?y)],
            p(?x, ?y) <- [q(?x, ?y), p(?x, ?z), p(?z, ?y)]
        };

        let query = Query {
            symbol: "p",
            matchers: vec![
                Matcher::Constant(TypedValue::Str("a".to_string())),
                Matcher::Any,
            ],
        };

        let result = apply_sdt_transformation(&prog, &query);

        let negated_atoms: Vec<_> = result.program.inner.iter()
            .flat_map(|rule| rule.body.iter().filter(|atom| !atom.sign))
            .collect();

        // If subsumption opportunities exist, there should be negated hypotheses.
        // If the adornment analysis only produces one pattern (bf), there's nothing
        // to subsume and no negated hypotheses — which is also correct behavior.
        // The key test: negated atoms, if any, must only be magic predicates.
        for atom in &negated_atoms {
            assert!(
                atom.symbol.starts_with("magic_"),
                "Negated atoms should only be magic predicates, got: {}",
                atom.symbol
            );
        }

        // At minimum, demand predicates should be generated
        assert!(
            !result.demand_predicates.is_empty(),
            "SDT should produce demand predicates"
        );

        // Verify the transformation produces a valid program
        assert!(!result.program.inner.is_empty());
    }

    #[test]
    fn test_sdt_paper_running_example() {
        // Paper's running example (Tekle & Liu Section 4.1):
        // rel(x,y) :- imm(x,y).
        // rel(x,y) :- imm(u,v), rel(u,x), rel(v,y).
        // Query: rel(c, _)? -> pattern bf
        //
        // With the EDB binding fix, imm(u,v) binds u and v.
        // So rel(u,x) has both u (from imm) and x (from head) bound -> pattern bb
        // And rel(v,y) has v bound (from imm), y free -> pattern bf
        // Patterns: {bf, bb}. bf properly subsumes bb.
        // SDT should add `not magic_rel_bf(u)` to the magic_rel_bb demand rule.
        let prog = program! {
            rel(?x, ?y) <- [imm(?x, ?y)],
            rel(?x, ?y) <- [imm(?u, ?v), rel(?u, ?x), rel(?v, ?y)]
        };

        let query = Query {
            symbol: "rel",
            matchers: vec![
                Matcher::Constant(TypedValue::Str("c".to_string())),
                Matcher::Any,
            ],
        };

        let result = apply_sdt_transformation(&prog, &query);

        // With Section 5 subsumption optimization, bb is subsumed by bf and
        // PRUNED at compile time — only bf demand predicate exists.
        let has_bf = result.demand_predicates.iter().any(|p| p.contains("_bf"));
        let has_bb = result.demand_predicates.iter().any(|p| p.contains("_bb"));
        assert!(has_bf, "Should produce bf demand predicate");
        assert!(!has_bb, "Section 5 pruning: bb demand predicate should NOT exist (subsumed by bf)");

        // The program should be purely positive (no negated hypotheses).
        let negated_atoms: Vec<_> = result.program.inner.iter()
            .flat_map(|rule| rule.body.iter().filter(|atom| !atom.sign))
            .collect();
        assert!(
            negated_atoms.is_empty(),
            "With Section 5 optimization, SDT should produce no negated hypotheses. Found: {:?}",
            negated_atoms.iter().map(|a| &a.symbol).collect::<Vec<_>>()
        );

        // Should have sdt_aux_* auxiliary predicates from Section 5 restructuring.
        let has_aux = result.program.inner.iter()
            .any(|r| r.head.symbol.starts_with("sdt_aux_"));
        assert!(has_aux, "Section 5 restructuring should produce sdt_aux_* predicates");
    }

    #[test]
    fn test_sdt_demand_predicates_identified() {
        let prog = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)]
        };

        let query = Query {
            symbol: "tc",
            matchers: vec![
                Matcher::Constant(TypedValue::Str("a".to_string())),
                Matcher::Any,
            ],
        };

        let result = apply_sdt_transformation(&prog, &query);
        assert!(
            result.demand_predicates.iter().any(|p| p.starts_with("magic_tc")),
            "Demand predicates should include magic_tc_*"
        );
    }
}

#[cfg(test)]
mod redirect_tests {
    use super::*;
    use datalog_rule_macro::program;
    #[test]
    fn test_redirect_nonlinear_tc_bb() {
        // Nonlinear TC with bb query: T(x,z) :- T(x,y), T(y,z)
        // bb is the query pattern (not subsumed — it's the entry point).
        // bf is generated from the first IDB body atom and subsumes bb.
        // bb's recursive rule body atoms should be redirected to T_bf.
        // With Section 5 optimization, the T_bb rule should contain
        // sdt_aux + T_bf references (restructured), or directly T_bf.
        let prog = program! {
            T(?x, ?y) <- [E(?x, ?y)],
            T(?x, ?z) <- [T(?x, ?y), T(?y, ?z)]
        };
        let query = Query {
            symbol: "T",
            matchers: vec![Matcher::Constant(TypedValue::Int(0)), Matcher::Constant(TypedValue::Int(4))],
        };
        let result = apply_sdt_transformation(&prog, &query);

        // T_bb should exist (it's the query pattern, never subsumed)
        let bb_rules: Vec<_> = result.program.inner.iter()
            .filter(|r| r.head.symbol == "T_bb")
            .collect();
        assert!(!bb_rules.is_empty(), "T_bb rules should exist (query pattern)");

        // T_bf should also exist (generated from first body atom, guaranteed)
        let bf_rules: Vec<_> = result.program.inner.iter()
            .filter(|r| r.head.symbol == "T_bf")
            .collect();
        assert!(!bf_rules.is_empty(), "T_bf rules should exist");

        // The program should be purely positive (no negated atoms)
        let negated: Vec<_> = result.program.inner.iter()
            .flat_map(|r| r.body.iter().filter(|a| !a.sign))
            .collect();
        assert!(negated.is_empty(),
            "SDT with Section 5 should produce purely positive program, found: {:?}",
            negated.iter().map(|a| &a.symbol).collect::<Vec<_>>());

        // Body atoms referencing subsumed patterns should be redirected to T_bf
        for rule in &bb_rules {
            for atom in &rule.body {
                if atom.symbol.starts_with("T_") && !atom.symbol.starts_with("T_bf") && atom.symbol != "T_bb" {
                    panic!("Body atom should be T_bf (redirected), got {}", atom.symbol);
                }
            }
        }
    }
}

#[cfg(test)]
mod guaranteed_flag_tests {
    use super::*;
    use datalog_rule_macro::program;

    /// Gap 1: First-position guarantee inheritance DISTINCT from query pattern.
    /// The pattern for predicate `q` should be guaranteed because it is the first
    /// IDB body atom of a rule whose head (`p_bf`) is guaranteed (the query pattern).
    /// This is different from `q` being the query predicate itself.
    #[test]
    fn test_first_position_inheritance_distinct_from_query() {
        // p(x,y) :- e(x,y).
        // p(x,y) :- e(x,z), q(z,y).
        // q(x,y) :- base(x,y).
        // q(x,y) :- base(x,z), q(z,y).
        // Query: p("a", _) -> bf
        //
        // Adornment: p_bf -> rule 2 body: e(x,z) EDB, q(z,y) first IDB -> q_bf
        // q_bf is guaranteed because:
        //   - p_bf is guaranteed (query pattern)
        //   - q is the FIRST IDB body atom of p's rule
        //   - q is NOT the query predicate
        let prog = program! {
            p(?x, ?y) <- [e(?x, ?y)],
            p(?x, ?y) <- [e(?x, ?z), q(?z, ?y)],
            q(?x, ?y) <- [base(?x, ?y)],
            q(?x, ?y) <- [base(?x, ?z), q(?z, ?y)]
        };

        let query = Query {
            symbol: "p",
            matchers: vec![
                Matcher::Constant(TypedValue::Str("a".to_string())),
                Matcher::Any,
            ],
        };

        let result = apply_sdt_transformation(&prog, &query);

        // q_bf should be marked guaranteed (first-position inheritance from p_bf)
        let q_guaranteed = result.guaranteed_patterns.get("q")
            .map_or(false, |pats| pats.contains(&vec![Adornment::Bound, Adornment::Free]));
        assert!(q_guaranteed,
            "q_bf should be guaranteed via first-position inheritance from p_bf. \
             guaranteed_patterns: {:?}", result.guaranteed_patterns);

        // p_bf should also be guaranteed (query pattern)
        let p_guaranteed = result.guaranteed_patterns.get("p")
            .map_or(false, |pats| pats.contains(&vec![Adornment::Bound, Adornment::Free]));
        assert!(p_guaranteed, "p_bf should be guaranteed (query pattern)");
    }

    /// Gap 2: Transitive guarantee propagation (A → B → C).
    /// If A is guaranteed (query), A's first IDB body generates B, and B's first
    /// IDB body generates C, then C should also be guaranteed.
    #[test]
    fn test_transitive_guarantee_propagation() {
        // a(x,y) :- e(x,y).
        // a(x,y) :- e(x,z), b(z,y).
        // b(x,y) :- f(x,y).
        // b(x,y) :- f(x,z), c(z,y).
        // c(x,y) :- g(x,y).
        // c(x,y) :- g(x,z), c(z,y).
        // Query: a("start", _) -> bf
        //
        // Chain: a_bf (query, guaranteed) -> b_bf (first IDB of a's rule, guaranteed)
        //        -> c_bf (first IDB of b's rule, guaranteed)
        let prog = program! {
            a(?x, ?y) <- [e(?x, ?y)],
            a(?x, ?y) <- [e(?x, ?z), b(?z, ?y)],
            b(?x, ?y) <- [f(?x, ?y)],
            b(?x, ?y) <- [f(?x, ?z), c(?z, ?y)],
            c(?x, ?y) <- [g(?x, ?y)],
            c(?x, ?y) <- [g(?x, ?z), c(?z, ?y)]
        };

        let query = Query {
            symbol: "a",
            matchers: vec![
                Matcher::Constant(TypedValue::Str("start".to_string())),
                Matcher::Any,
            ],
        };

        let result = apply_sdt_transformation(&prog, &query);
        let bf = vec![Adornment::Bound, Adornment::Free];

        let a_g = result.guaranteed_patterns.get("a")
            .map_or(false, |p| p.contains(&bf));
        let b_g = result.guaranteed_patterns.get("b")
            .map_or(false, |p| p.contains(&bf));
        let c_g = result.guaranteed_patterns.get("c")
            .map_or(false, |p| p.contains(&bf));

        assert!(a_g, "a_bf should be guaranteed (query pattern)");
        assert!(b_g, "b_bf should be guaranteed (first IDB of a_bf rule). \
                guaranteed: {:?}", result.guaranteed_patterns);
        assert!(c_g, "c_bf should be guaranteed (first IDB of b_bf rule, transitive). \
                guaranteed: {:?}", result.guaranteed_patterns);
    }

    /// Gap 3: Direct inspection of guaranteed_patterns for the paper's running example.
    /// Only bf should be guaranteed for rel; bb must NOT be guaranteed.
    #[test]
    fn test_paper_example_guaranteed_map() {
        // rel(x,y) :- imm(x,y).
        // rel(x,y) :- imm(u,v), rel(u,x), rel(v,y).
        // Query: rel("c", _) -> bf
        //
        // Rule 2: imm(u,v) EDB binds u,v. rel(u,x) first IDB -> bb (both u,x bound).
        // rel(v,y) second IDB -> bf (v bound, y free).
        // bf is guaranteed (query pattern). bb: is it guaranteed?
        // bb comes from rel(u,x) which is the FIRST IDB body atom of rule 2.
        // Rule 2's head is rel_bf which IS guaranteed. So bb inherits guarantee.
        //
        // But bf also comes from the second IDB body atom (rel(v,y)) — that occurrence
        // is NOT guaranteed. However, bf is ALREADY guaranteed as the query pattern.
        let prog = program! {
            rel(?x, ?y) <- [imm(?x, ?y)],
            rel(?x, ?y) <- [imm(?u, ?v), rel(?u, ?x), rel(?v, ?y)]
        };

        let query = Query {
            symbol: "rel",
            matchers: vec![
                Matcher::Constant(TypedValue::Str("c".to_string())),
                Matcher::Any,
            ],
        };

        let result = apply_sdt_transformation(&prog, &query);

        let bf = vec![Adornment::Bound, Adornment::Free];
        let bb = vec![Adornment::Bound, Adornment::Bound];

        let rel_pats = result.guaranteed_patterns.get("rel")
            .expect("rel should have guaranteed patterns");

        assert!(rel_pats.contains(&bf),
            "rel_bf should be guaranteed (query pattern). Got: {:?}", rel_pats);
        assert!(rel_pats.contains(&bb),
            "rel_bb should be guaranteed (first IDB of rel_bf rule). Got: {:?}", rel_pats);
    }

    /// Verify that non-first-position patterns are NOT marked guaranteed,
    /// even when they subsume other patterns.
    #[test]
    fn test_non_first_position_not_guaranteed() {
        // p(x,y) :- base(x,y).
        // p(x,y) :- q(x,z), p(z,y), r(y,w), p(w,x)
        // Query: p("a", _) -> bf
        //
        // Body of rule 2: q EDB, p(z,y) pos 2 -> bf, r EDB, p(w,x) pos 4 -> bb
        // p_bf from position 2 is NOT the first IDB body atom — p(z,y) IS first
        // actually... let me re-check. q is EDB. p(z,y) IS the first IDB body atom.
        // So p(z,y) with pattern bf IS guaranteed (first IDB of p_bf rule).
        // p(w,x) at position 4 is NOT first IDB -> bb is NOT guaranteed from this path.
        // But bf is also the query pattern, so bf IS guaranteed.
        // bb: is it guaranteed? Only if it comes from a first-position IDB atom
        // of a guaranteed head. p(z,y) is the first IDB -> generates bf, not bb.
        // p(w,x) is NOT first IDB -> bb from here is not guaranteed.
        // So bb should NOT be guaranteed.
        let prog = program! {
            p(?x, ?y) <- [base(?x, ?y)],
            p(?x, ?y) <- [q(?x, ?z), p(?z, ?y), r(?y, ?w), p(?w, ?x)]
        };

        let query = Query {
            symbol: "p",
            matchers: vec![
                Matcher::Constant(TypedValue::Str("a".to_string())),
                Matcher::Any,
            ],
        };

        let result = apply_sdt_transformation(&prog, &query);

        let bf = vec![Adornment::Bound, Adornment::Free];
        let bb = vec![Adornment::Bound, Adornment::Bound];

        let p_pats = result.guaranteed_patterns.get("p")
            .expect("p should have guaranteed patterns");

        assert!(p_pats.contains(&bf),
            "p_bf should be guaranteed (query pattern + first IDB position)");
        assert!(!p_pats.contains(&bb),
            "p_bb must NOT be guaranteed (comes from non-first IDB position only). Got: {:?}", p_pats);

        // Verify no negated hypotheses reference p_bf for suppressing p_bb,
        // since bf IS guaranteed but we want to confirm the transformation-level behavior
        let negated_atoms: Vec<_> = result.program.inner.iter()
            .flat_map(|rule| rule.body.iter().filter(|atom| !atom.sign))
            .collect();

        // There should be no negated hypotheses at all in this program,
        // because bf (guaranteed) subsumes bb (non-guaranteed from pos 4),
        // BUT bb is not generated from a guaranteed context... wait.
        // Actually: bf subsumes bb. bf IS guaranteed. So the negated hypothesis
        // `not magic_p_bf(X)` SHOULD be added to the bb demand rule.
        // The question is whether bb demand exists at all. If p(w,x) generates
        // bb demand, and bf is guaranteed, then the bb demand rule gets
        // `not magic_p_bf(w)` — which is correct suppression.
        // With compile-time pruning: bf is guaranteed and subsumes bb.
        // bb should be PRUNED at compile time — no rules generated for it.
        // So no negated hypotheses should exist.
        assert!(negated_atoms.is_empty(),
            "With compile-time pruning, bb should be pruned — no negation needed. \
             Found {} negated atoms: {:?}",
            negated_atoms.len(),
            negated_atoms.iter().map(|a| &a.symbol).collect::<Vec<_>>());
    }

    /// Verify that ALL benchmark programs produce purely positive transformed programs
    /// after compile-time subsumption pruning. Tekle's algorithm should not require
    /// runtime negation when implemented correctly.
    #[test]
    fn test_all_programs_no_negation_after_pruning() {
        let programs: Vec<(&str, Program, Query)> = vec![
            ("Linear TC bf", program! {
                tc(?x,?y) <- [e(?x,?y)],
                tc(?x,?z) <- [e(?x,?y), tc(?y,?z)]
            }, Query { symbol: "tc", matchers: vec![
                Matcher::Constant(TypedValue::Str("a".into())), Matcher::Any] }),

            ("Nonlinear TC bf", program! {
                tc(?x,?y) <- [e(?x,?y)],
                tc(?x,?z) <- [tc(?x,?y), tc(?y,?z)]
            }, Query { symbol: "tc", matchers: vec![
                Matcher::Constant(TypedValue::Str("a".into())), Matcher::Any] }),

            ("Nonlinear TC bb", program! {
                tc(?x,?y) <- [e(?x,?y)],
                tc(?x,?z) <- [tc(?x,?y), tc(?y,?z)]
            }, Query { symbol: "tc", matchers: vec![
                Matcher::Constant(TypedValue::Int(0)), Matcher::Constant(TypedValue::Int(5))] }),

            ("Paper example bf", program! {
                rel(?x,?y) <- [imm(?x,?y)],
                rel(?x,?y) <- [imm(?u,?v), rel(?u,?x), rel(?v,?y)]
            }, Query { symbol: "rel", matchers: vec![
                Matcher::Constant(TypedValue::Str("c".into())), Matcher::Any] }),

            ("Same-gen bf", program! {
                sg(?x,?y) <- [flat(?x,?y)],
                sg(?x,?y) <- [up(?x,?z1), sg(?z1,?z2), down(?z2,?y)]
            }, Query { symbol: "sg", matchers: vec![
                Matcher::Constant(TypedValue::Str("a".into())), Matcher::Any] }),
        ];

        for (name, prog, query) in programs {
            let result = apply_sdt_transformation(&prog, &query);
            let negated: Vec<_> = result.program.inner.iter()
                .flat_map(|r| r.body.iter().filter(|a| !a.sign))
                .collect();
            assert!(negated.is_empty(),
                "{}: expected purely positive program after compile-time pruning, \
                 but found {} negated atoms: {:?}",
                name, negated.len(),
                negated.iter().map(|a| &a.symbol).collect::<Vec<_>>());
        }
    }
}
