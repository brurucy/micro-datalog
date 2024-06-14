#[cfg(test)]
mod tests {
    use datalog_rule_macro::rule;
    use datalog_syntax::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_simple_rule() {
        let rule_output = rule! { tc(?x, ?z) <- [e(?x, ?y), tc(?y, ?z)] };

        let expected_output = Rule {
            head: Atom {
                terms: vec![
                    Term::Variable("x".to_string()),
                    Term::Variable("z".to_string()),
                ],
                symbol: "tc".to_string(),
                sign: true,
            },
            body: vec![
                Atom {
                    terms: vec![
                        Term::Variable("x".to_string()),
                        Term::Variable("y".to_string()),
                    ],
                    symbol: "e".to_string(),
                    sign: true,
                },
                Atom {
                    terms: vec![
                        Term::Variable("y".to_string()),
                        Term::Variable("z".to_string()),
                    ],
                    symbol: "tc".to_string(),
                    sign: true,
                },
            ],
            id: 0,
        };

        assert_eq!(rule_output, expected_output);
    }

    #[test]
    fn test_more_complex_rule() {
        let rule_output = rule! { tc(?x, 13) <- [e(?x, "haha"), tc(?y, true)] };

        let expected_output = Rule {
            head: Atom {
                terms: vec![
                    Term::Variable("x".to_string()),
                    Term::Constant(TypedValue::from(13)),
                ],
                symbol: "tc".to_string(),
                sign: true,
            },
            body: vec![
                Atom {
                    terms: vec![
                        Term::Variable("x".to_string()),
                        Term::Constant(TypedValue::from("haha")),
                    ],
                    symbol: "e".to_string(),
                    sign: true,
                },
                Atom {
                    terms: vec![
                        Term::Variable("y".to_string()),
                        Term::Constant(TypedValue::from(true)),
                    ],
                    symbol: "tc".to_string(),
                    sign: true,
                },
            ],
            id: 0,
        };

        assert_eq!(rule_output, expected_output);
    }
}
