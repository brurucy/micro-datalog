use datalog_syntax::Program;
use indexmap::IndexSet;

pub const OVERDELETION_PREFIX: &str = "delete_";
pub const REDERIVATION_PREFIX: &str = "rederive_";

pub fn add_prefix(symbol: &mut String, prefix: &str) {
    *symbol = format!("{}{}", prefix, symbol);
}

pub fn split_program(program: Program) -> (Program, Program) {
    let mut nonrecursive = vec![];
    let mut recursive = vec![];

    let idb_relations = program.inner.iter().map(|r| r.head.symbol.as_str()).collect::<IndexSet<_>>();

    program.inner.iter().for_each(|rule| {
        if rule
            .body
            .iter()
            .map(|body_atom| &body_atom.symbol)
            .any(|body_atom_symbol| idb_relations.contains(body_atom_symbol.as_str()))
        {
            recursive.push(rule.clone());
        } else {
            nonrecursive.push(rule.clone());
        }
    });

    (Program::from(nonrecursive), Program::from(recursive))
}

#[cfg(test)]
mod tests {
    use crate::helpers::helpers::split_program;
    use datalog_rule_macro::program;
    use datalog_syntax::*;

    #[test]
    fn test_split_program_complex() {
        let stratified_program = program! {
            // Stratum 1: Base rule
            base(?x, ?y) <- [edge(?x, ?y)],

            // Stratum 2: Derived rule depends on Stratum 1
            derived(?x, ?y) <- [base(?x, ?y)],
            derived(?x, ?z) <- [base(?x, ?y), derived(?y, ?z)],

            // Stratum 3: Another level of derivation
            top(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)],
        };

        let expected_nonrecursive_program = program! {
            base(?x, ?y) <- [edge(?x, ?y)],
        };

        let expected_recursive_program = program! {
            derived(?x, ?y) <- [base(?x, ?y)],
            derived(?x, ?z) <- [base(?x, ?y), derived(?y, ?z)],
            top(?x, ?z) <- [derived(?x, ?y), base(?y, ?z)],
        };

        let (nonrecursive_program, recursive_program) = split_program(stratified_program);

        assert_eq!(expected_nonrecursive_program, nonrecursive_program);
        assert_eq!(expected_recursive_program, recursive_program);
    }

    #[test]
    fn test_split_program() {
        let program = program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(? x, ?z) <- [e(? x, ?y), tc(? y, ?z)]
        };

        let expected_nonrecursive_program = program! { tc(?x, ?y) <- [e(?x, ?y)] };
        let expected_recursive_program = program! { tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)] };

        let (actual_nonrecursive_program, actual_recursive_program) = split_program(program);

        assert_eq!(expected_nonrecursive_program, actual_nonrecursive_program);
        assert_eq!(expected_recursive_program, actual_recursive_program);
    }
}
