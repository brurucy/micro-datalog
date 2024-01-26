use crate::helpers::helpers::{add_prefix, DELTA_PREFIX};
use datalog_syntax::{Program, Rule};
use std::collections::HashSet;

pub fn make_delta_program(program: &Program, update: bool) -> Program {
    let idb_relation_symbols: HashSet<_> = program
        .inner
        .iter()
        .map(|rule| rule.head.symbol.clone())
        .collect();

    // Using a HashSet to efficiently check for duplicates during insertion
    let mut delta_rules_set = HashSet::new();

    for rule in &program.inner {
        let mut delta_rule = rule.clone();
        add_prefix(&mut delta_rule.head.symbol, DELTA_PREFIX);

        let contains_idb = rule
            .body
            .iter()
            .any(|atom| idb_relation_symbols.contains(&atom.symbol));

        if !contains_idb && !update {
            // If the body does not contain any IDB relation symbols and it's not an update phase,
            // add the delta rule directly to the set.
            delta_rules_set.insert(delta_rule);
        } else {
            // Otherwise, consider each body atom and deltaify if necessary.
            for (index, body_atom) in rule.body.iter().enumerate() {
                if update || idb_relation_symbols.contains(&body_atom.symbol) {
                    let mut new_rule = delta_rule.clone();
                    add_prefix(&mut new_rule.body[index].symbol, DELTA_PREFIX);
                    delta_rules_set.insert(new_rule);
                }
            }
        }
    }

    // Convert HashSet back into Vec and construct the Program.
    // HashSet's into_iter will consume the set and avoid cloning its items.
    let delta_program: Vec<Rule> = delta_rules_set.into_iter().collect();

    Program::from(delta_program)
}

#[cfg(test)]
mod test {
    use crate::program_transformations::delta_program::make_delta_program;
    use datalog_rule_macro::*;
    use datalog_syntax::*;
    use pretty_assertions::assert_eq;

    // make program! support not
    #[test]
    fn test_make_sne_program_nonlinear_update() {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
        };

        let actual_program = make_delta_program(&program, true);
        let expected_program = program! {
            Δtc(?x, ?y) <- [Δe(?x, ?y)],
            Δtc(?x, ?z) <- [Δtc(?x, ?y), tc(?y, ?z)],
            Δtc(?x, ?z) <- [tc(?x, ?y), Δtc(?y, ?z)],
        };

        assert_eq!(expected_program, actual_program)
    }

    #[test]
    fn test_make_sne_program_nonlinear_initial() {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)],
        };

        let actual_program = make_delta_program(&program, false);
        let expected_program = program! {
            Δtc(?x, ?y) <- [e(?x, ?y)],
            Δtc(? x, ?z) <- [Δtc(? x, ?y), tc(? y, ?z)],
            Δtc(? x, ?z) <-[tc(? x, ?y), Δtc(? y, ?z)],
        };

        assert_eq!(expected_program, actual_program)
    }

    #[test]
    fn test_make_sne_program_linear_initial() {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };

        let actual_program = make_delta_program(&program, false);
        let expected_program = program! {
            Δtc(?x, ?y) <- [e(?x, ?y)],
            Δtc(?x, ?z) <- [e(?x, ?y), Δtc(?y, ?z)],
        };

        assert_eq!(expected_program, actual_program)
    }

    #[test]
    fn test_make_sne_program_linear_update() {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)],
        };

        let actual_program = make_delta_program(&program, true);
        let expected_program = program! {
            Δtc(?x, ?y) <- [Δe(?x, ?y)],
            Δtc(?x, ?z) <- [Δe(?x, ?y), tc(?y, ?z)],
            Δtc(?x, ?z) <- [e(?x, ?y), Δtc(?y, ?z)],
        };

        assert_eq!(expected_program, actual_program)
    }
}
