#[allow(dead_code)]
mod compile_fail_tests {
    use datalog_rule_macro::semipositive_program;

    // This should cause a compile-time error
    semipositive_program! {
        tc(?x, ?y) <- [e(?x, ?y)],
        tc(?x, ?z) <- [e(?x, ?y), !tc(?y, ?z)]
    }
}
