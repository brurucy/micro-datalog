use crate::engine::storage::RelationStorage;
use datalog_syntax::Program;

pub fn semi_positive_evaluation(
    relation_storage: &mut RelationStorage,
    nonrecursive_delta_program: &Program,
    recursive_delta_program: &Program
) {
    // Apply non-recursive rules to initialize base facts
    relation_storage.materialize_nonrecursive_delta_program(&nonrecursive_delta_program);

    // Set of negated atoms that appear in recursive rules (to ensure semi-positive)
    let negated_atoms = recursive_delta_program.get_negated_atoms();

/* Assuming that this is redundant ? 
    for rule in recursive_delta_program.inner.iter() {
        for atom in rule.body.iter() {
            // Check if any negated atom is dependent on a head atom of another rule
            if atom.sign == false && negated_atoms.contains(&&rule.head) {
                panic!(
                    "Semi-positive evaluation failed: Negated atom {} in rule body depends on another recursive rule head",
                    atom.symbol
                );
            }
        }
    }
        */

    // Perform iterative semi-positive evaluation
    loop {
        let previous_non_delta_fact_count = relation_storage.len();

        // Apply recursive rules to derive new facts
        relation_storage.materialize_recursive_delta_program(&recursive_delta_program);

        let current_non_delta_fact_count = relation_storage.len();
        let new_fact_count = current_non_delta_fact_count - previous_non_delta_fact_count;

        // Stop if no new facts are derived
        if new_fact_count == 0 {
            return;
        }
    }
}
