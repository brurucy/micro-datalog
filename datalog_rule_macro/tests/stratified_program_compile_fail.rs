#[allow(dead_code)]
mod compile_fail_tests {
    use datalog_rule_macro::stratified_program;

    // This should cause a compile-time error
    stratified_program! {
        tc(?x, ?y) <- [e(?x, ?y)];
        e(?x, ?y) <- [!tc(?x, ?y)]
    }
}
