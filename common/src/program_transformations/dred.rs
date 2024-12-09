use crate::helpers::helpers::{ add_prefix, OVERDELETION_PREFIX, REDERIVATION_PREFIX };
use datalog_syntax::{ Program, Rule, StratifiedProgram };
use std::collections::HashSet;
use dependency_graph::{ generate_rule_dependency_graph, stratify };


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StratifiedProgram {
    pub strata: Vec<Vec<Rule>>, // Each `Vec<Rule>` represents one stratum
}

impl From<Vec<Rule>> for StratifiedProgram {
    fn from(value: Vec<Rule>) -> Self {
        // Generate the dependency graph and compute strata
        let rule_graph = generate_rule_dependency_graph(&value);
        let stratification = stratify(&rule_graph);

        // Assign unique IDs within each stratum and sort the rules
        let mut strata = stratification
            .into_iter()
            .map(|stratum| {
                let mut sorted_stratum: Vec<Rule> = stratum.into_iter().cloned().collect();
                sorted_stratum.sort(); // Sort rules within the stratum
                sorted_stratum
            })
            .collect::<Vec<_>>();

        // Assign IDs to the rules across all strata
        let mut id_counter = 0;
        for stratum in &mut strata {
            for rule in stratum {
                rule.id = id_counter;
                id_counter += 1;
            }
        }

        Self { strata }
    }
}

pub fn make_overdeletion_program(program: &Program) -> Program {
    let mut overdeletion_rules_set = HashSet::new();

    for rule in &program.inner {
        let mut overdeletion_rule = rule.clone();
        add_prefix(&mut overdeletion_rule.head.symbol, OVERDELETION_PREFIX);

        for (index, _) in rule.body.iter().enumerate() {
            let mut new_rule = overdeletion_rule.clone();
            add_prefix(&mut new_rule.body[index].symbol, OVERDELETION_PREFIX);
            overdeletion_rules_set.insert(new_rule);
        }
    }

    let overdeletion_program: Vec<Rule> = overdeletion_rules_set.into_iter().collect();

    Program::from(overdeletion_program)
}

pub fn make_overdeletion_program_stratified(program: &StratifiedProgram) -> StratifiedProgram {
    let mut overdeletion_rules_set = HashSet::new();

    // Iterate over strata in the StratifiedProgram
    for stratum in &program.strata {
        for rule in stratum {
            let mut overdeletion_rule = rule.clone();
            add_prefix(&mut overdeletion_rule.head.symbol, OVERDELETION_PREFIX);

            // Generate new rules for each body atom
            for (index, _) in rule.body.iter().enumerate() {
                let mut new_rule = overdeletion_rule.clone();
                add_prefix(&mut new_rule.body[index].symbol, OVERDELETION_PREFIX);
                overdeletion_rules_set.insert(new_rule);
            }
        }
    }

    // Convert the set of rules into a Program
    let overdeletion_program: Vec<Rule> = overdeletion_rules_set.into_iter().collect();
    StratifiedProgram::from(overdeletion_program)
}

pub fn make_rederivation_program_stratified(program: &StratifiedProgram) -> StratifiedProgram {
    let mut rederivation_rules_set = HashSet::new();

    for stratum in stratification {
        for rule in stratum {
            let mut rederivation_rule = rule.clone();

            let mut rederivation_head = rederivation_rule.head.clone();
            add_prefix(&mut rederivation_head.symbol, OVERDELETION_PREFIX);
            rederivation_rule.body.insert(0, rederivation_head);

            add_prefix(&mut rederivation_rule.head.symbol, REDERIVATION_PREFIX);
            rederivation_rules_set.insert(rederivation_rule);
        }
    }

    let rederivation_program: Vec<Rule> = rederivation_rules_set.into_iter().collect();
    StratifiedProgram::from(rederivation_program)
}

pub fn make_rederivation_program(program: &Program) -> Program {
    let mut rederivation_rules_set = HashSet::new();

    for rule in &program.inner {
        let mut rederivaton_rule = rule.clone();

        let mut rederivation_head = rederivaton_rule.head.clone();
        add_prefix(&mut rederivation_head.symbol, OVERDELETION_PREFIX);
        rederivaton_rule.body.insert(0, rederivation_head);

        add_prefix(&mut rederivaton_rule.head.symbol, REDERIVATION_PREFIX);
        rederivation_rules_set.insert(rederivaton_rule);
    }

    let rederivation_program: Vec<Rule> = rederivation_rules_set.into_iter().collect();

    Program::from(rederivation_program)
}

#[cfg(test)]
mod test {
    use crate::program_transformations::dred::{
        make_overdeletion_program,
        make_rederivation_program,
    };
    use datalog_rule_macro::*;
    use datalog_syntax::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_make_overdeletion_program() {
        let program =
            program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
        };

        let expected_program =
            program! {
            delete_tc(?x, ?y) <- [delete_e(?x, ?y)],
            delete_tc(?x, ?z) <- [delete_tc(?x, ?y), tc(?y, ?z)],
            delete_tc(?x, ?z) <- [tc(?x, ?y), delete_tc(?y, ?z)],
        };
        let actual_program = make_overdeletion_program(&program);

        assert_eq!(expected_program, actual_program)
    }

    #[test]
    fn test_make_rederivation_program() {
        let program =
            program! {
            tc(?x, ?y) <- [e(?x, ?y)],
            tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
        };

        let expected_program =
            program! {
            rederive_tc(?x, ?y) <- [delete_tc(?x, ?y), e(?x, ?y)],
            rederive_tc(?x, ?z) <- [delete_tc(?x, ?z), tc(?x, ?y), tc(?y, ?z)],
        };
        let actual_program = make_rederivation_program(&program);

        assert_eq!(expected_program, actual_program)
    }

    #[test]
    fn test_make_overdeletion_program_stratified() {
        let program =
            program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
    };
        let stratified_program = StratifiedProgram::from(program.inner);

        let expected_stratified_program = StratifiedProgram::from(
            vec![
                rule!(delete_tc(?x, ?y) <- [delete_e(?x, ?y)]),
                rule!(delete_tc(?x, ?z) <- [delete_tc(?x, ?y), tc(?y, ?z)]),
                rule!(delete_tc(?x, ?z) <- [tc(?x, ?y), delete_tc(?y, ?z)])
            ]
        );

        let actual_stratified_program = make_overdeletion_program_stratified(&stratified_program);

        assert_eq!(expected_stratified_program, actual_stratified_program);
    }

    #[test]
    fn test_make_rederivation_program_stratified() {
        let program =
            program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [tc(?x, ?y), tc(?y, ?z)]
    };
        let stratified_program = StratifiedProgram::from(program.inner);

        let expected_stratified_program = StratifiedProgram::from(
            vec![
                rule!(rederive_tc(?x, ?y) <- [delete_tc(?x, ?y), e(?x, ?y)]),
                rule!(rederive_tc(?x, ?z) <- [delete_tc(?x, ?z), tc(?x, ?y), tc(?y, ?z)])
            ]
        );

        let actual_stratified_program = make_rederivation_program_stratified(&stratified_program);

        assert_eq!(expected_stratified_program, actual_stratified_program);
    }
}
