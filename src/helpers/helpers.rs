use datalog_syntax::Program;

pub const DELTA_PREFIX: &str = "Δ";
pub const OVERDELETION_PREFIX: &str = "delete_";
pub const REDERIVATION_PREFIX: &str = "rederive_";

pub fn add_prefix(symbol: &mut String, prefix: &str) {
    *symbol = format!("{}{}", prefix, symbol);
}

pub fn strip_prefix(symbol: &mut String, prefix: &str) {
    *symbol = symbol.strip_prefix(prefix).unwrap().to_string();
}

pub fn split_program(program: Program) -> (Program, Program) {
    let mut nonrecursive = vec![];
    let mut recursive = vec![];

    program.inner.into_iter().for_each(|rule| {
        let head_symbol = rule.head.symbol.as_str();

        if rule
            .body
            .iter()
            .map(|body_atom| &body_atom.symbol)
            .any(|body_atom_symbol| head_symbol == body_atom_symbol)
        {
            recursive.push(rule);
        } else {
            nonrecursive.push(rule);
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
