extern crate common;
extern crate proc_macro;

use common::program_transformations::dependency_graph::{generate_rule_dependency_graph, stratify};
use datalog_syntax::{Atom, Rule, Term, TypedValue};
use proc_macro::TokenStream;
use quote::quote;
use std::collections::{HashMap, HashSet};
use syn::parse::{Parse, ParseStream};
use syn::{bracketed, parenthesized, Expr, Ident, Result, Token};

enum TermArg {
    Variable(Ident),
    Constant(Expr),
}

struct AtomArgs {
    name: Ident,
    args: Vec<TermArg>,
    sign: bool,
}

struct RuleMacroInput {
    head: AtomArgs,
    body: Vec<AtomArgs>,
}

impl Parse for TermArg {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![?]) {
            input.parse::<Token![?]>()?;
            let ident: Ident = input.parse()?;
            Ok(TermArg::Variable(ident))
        } else {
            let expr: Expr = input.parse()?;
            Ok(TermArg::Constant(expr))
        }
    }
}

impl Parse for RuleMacroInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let head = input.parse::<AtomArgs>()?;
        let mut distinguished_variables: HashMap<String, (&Ident, bool)> = head
            .args
            .iter()
            .filter(|term| matches!(term, TermArg::Variable(_)))
            .map(|variable| match variable {
                TermArg::Variable(ident) => (ident.to_string(), (ident, false)),
                _ => unreachable!(),
            })
            .collect();

        input.parse::<Token![<-]>()?;
        let content2;
        bracketed!(content2 in input);
        let body: syn::punctuated::Punctuated<AtomArgs, Token![,]> =
            content2.parse_terminated(AtomArgs::parse)?;
        let body_vec: Vec<AtomArgs> = body.into_iter().collect();
        body_vec.iter().for_each(|body_atom| {
            body_atom
                .args
                .iter()
                .filter(|term| matches!(term, TermArg::Variable(_)))
                .for_each(|variable| match variable {
                    TermArg::Variable(ident) => {
                        let owned_ident = ident.to_string();

                        if distinguished_variables.contains_key(&owned_ident) {
                            distinguished_variables.get_mut(&owned_ident).unwrap().1 = true;
                        }
                    }
                    _ => unreachable!(),
                });
        });

        for (key, value) in distinguished_variables {
            if !value.1 {
                return Err(syn::Error::new(
                    value.0.span(),
                    format!("variable {} not found in the body", key),
                ));
            }
        }

        Ok(RuleMacroInput {
            head,
            body: body_vec,
        })
    }
}

impl Parse for AtomArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let sign = if input.peek(Token![!]) {
            input.parse::<Token![!]>()?;
            false
        } else {
            true
        };

        let name: Ident = input.parse()?;
        let content;
        parenthesized!(content in input);
        let args = content
            .parse_terminated::<TermArg, Token![,]>(TermArg::parse)?
            .into_iter()
            .collect();

        Ok(AtomArgs { name, args, sign })
    }
}

#[proc_macro]
pub fn rule(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as RuleMacroInput);

    let head_name = &input.head.name;
    let head_terms: Vec<_> = input
        .head
        .args
        .iter()
        .map(|arg| match arg {
            TermArg::Variable(ident) => quote! { Term::Variable(stringify!(#ident).to_string()) },
            TermArg::Constant(expr) => quote! { Term::Constant(TypedValue::from(#expr)) },
        })
        .collect();

    let body_atoms: Vec<_> = input.body
        .iter()
        .map(|atom| {
            let name = &atom.name;
            let terms: Vec<_> = atom.args
                .iter()
                .map(|arg| {
                    match arg {
                        TermArg::Variable(ident) => {
                            quote! { Term::Variable(stringify!(#ident).to_string()) }
                        }
                        TermArg::Constant(expr) =>
                            quote! { Term::Constant(TypedValue::from(#expr)) },
                    }
                })
                .collect();
            let sign = atom.sign;
            quote! { Atom { terms: vec![#(#terms),*], symbol: stringify!(#name).to_string(), sign: #sign } }
        })
        .collect();

    let expanded = quote! {
        Rule {
            head: Atom { terms: vec![#(#head_terms),*], symbol: stringify!(#head_name).to_string(), sign: true },
            body: vec![#(#body_atoms),*],
            id: 0
        }
    };

    expanded.into()
}

struct ProgramMacroInput {
    rules: syn::punctuated::Punctuated<RuleMacroInput, Token![,]>,
}

impl Parse for ProgramMacroInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let rules = input.parse_terminated(RuleMacroInput::parse)?;
        Ok(ProgramMacroInput { rules })
    }
}

#[proc_macro]
pub fn program(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as ProgramMacroInput);

    let rules: Vec<_> = input.rules
        .into_iter()
        .map(|rule_input| {
            let head_name = &rule_input.head.name;
            let head_terms: Vec<_> = rule_input.head.args
                .iter()
                .map(|arg| {
                    match arg {
                        TermArg::Variable(ident) =>
                            quote! { Term::Variable(stringify!(#ident).to_string()) },
                        TermArg::Constant(expr) =>
                            quote! { Term::Constant(TypedValue::from(#expr)) },
                    }
                })
                .collect();

            let body_atoms: Vec<_> = rule_input.body
                .iter()
                .map(|atom| {
                    let name = &atom.name;
                    let terms: Vec<_> = atom.args
                        .iter()
                        .map(|arg| {
                            match arg {
                                TermArg::Variable(ident) => {
                                    quote! { Term::Variable(stringify!(#ident).to_string()) }
                                }
                                TermArg::Constant(expr) =>
                                    quote! { Term::Constant(TypedValue::from(#expr)) },
                            }
                        })
                        .collect();
                    quote! { Atom { terms: vec![#(#terms),*], symbol: stringify!(#name).to_string(), sign: true } }
                })
                .collect();

            quote! {
            Rule {
                head: Atom { terms: vec![#(#head_terms),*], symbol: stringify!(#head_name).to_string(), sign: true },
                body: vec![#(#body_atoms),*],
                id: 0
            }
        }
        })
        .collect();

    let expanded = quote! {
        Program::from( vec![#(#rules),*] )
    };

    expanded.into()
}

#[proc_macro]
pub fn semipositive_program(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as ProgramMacroInput);

    let mut heads = HashSet::new();
    for rule in &input.rules {
        heads.insert(&rule.head.name);
    }

    for rule in &input.rules {
        for atom in &rule.body {
            if !atom.sign && heads.contains(&atom.name) {
                let message = format!(
                    "Negated atom '{}' appears in the head of another rule!",
                    atom.name
                );
                return syn::Error::new(atom.name.span(), message)
                    .to_compile_error()
                    .into();
            }
        }
    }

    let rules: Vec<_> = input.rules
        .into_iter()
        .map(|rule_input| {
            let head_name = &rule_input.head.name;
            let head_terms: Vec<_> = rule_input.head.args
                .iter()
                .map(|arg| {
                    match arg {
                        TermArg::Variable(ident) =>
                            quote! { Term::Variable(stringify!(#ident).to_string()) },
                        TermArg::Constant(expr) =>
                            quote! { Term::Constant(TypedValue::from(#expr)) },
                    }
                })
                .collect();

            let body_atoms: Vec<_> = rule_input.body
                .iter()
                .map(|atom| {
                    let name = &atom.name;
                    let terms: Vec<_> = atom.args
                        .iter()
                        .map(|arg| {
                            match arg {
                                TermArg::Variable(ident) => {
                                    quote! { Term::Variable(stringify!(#ident).to_string()) }
                                }
                                TermArg::Constant(expr) =>
                                    quote! { Term::Constant(TypedValue::from(#expr)) },
                            }
                        })
                        .collect();
                    let sign = atom.sign;
                    quote! { Atom { terms: vec![#(#terms),*], symbol: stringify!(#name).to_string(), sign: #sign } }
                })
                .collect();

            quote! {
            Rule {
                head: Atom { terms: vec![#(#head_terms),*], symbol: stringify!(#head_name).to_string(), sign: true },
                body: vec![#(#body_atoms),*],
                id: 0
            }
        }
        })
        .collect();

    let expanded = quote! {
        Program::from( vec![#(#rules),*] )
    };

    expanded.into()
}

fn string_to_ident_with_span(symbol: &str, span: syn::__private::Span) -> Ident {
    Ident::new(symbol, span)
}

fn expr_to_typed_value(expr: &Expr) -> TypedValue {
    match expr {
        Expr::Lit(expr_lit) => match &expr_lit.lit {
            syn::Lit::Str(lit_str) => TypedValue::from(lit_str.value()),
            syn::Lit::Int(lit_int) => TypedValue::from(lit_int.base10_parse::<usize>().unwrap()),
            syn::Lit::Bool(lit_bool) => TypedValue::from(lit_bool.value),
            _ => panic!("Unsupported literal type"),
        },
        _ => panic!("Unsupported expression type"),
    }
}

#[proc_macro]
pub fn stratified_program(input: TokenStream) -> TokenStream {
    let input_clone = input.clone();
    let parsed_input = syn::parse_macro_input!(input as ProgramMacroInput);

    let mut program_rules: Vec<_> = vec![];

    for rule in parsed_input.rules {
        // let head_name = &rule.head.name;
        let head_terms: Vec<_> = rule
            .head
            .args
            .iter()
            .map(|arg| match arg {
                TermArg::Variable(ident) => Term::Variable(ident.to_string()),
                TermArg::Constant(expr) => Term::Constant(expr_to_typed_value(expr)),
            })
            .collect();

        let body_atoms: Vec<_> = rule
            .body
            .iter()
            .map(|atom| {
                let atom_name = &atom.name;
                let atom_terms: Vec<_> = atom
                    .args
                    .iter()
                    .map(|arg| match arg {
                        TermArg::Variable(ident) => Term::Variable(ident.to_string()),
                        TermArg::Constant(expr) => Term::Constant(expr_to_typed_value(expr)),
                    })
                    .collect();
                Atom {
                    terms: atom_terms,
                    symbol: atom_name.to_string(),
                    sign: atom.sign,
                }
            })
            .collect();

        program_rules.push(Rule {
            head: Atom {
                terms: head_terms,
                symbol: stringify!(head_name).to_string(),
                sign: true,
            },
            body: body_atoms,
            id: 0,
        });
    }

    let rule_graph = generate_rule_dependency_graph(&program_rules);
    let stratification = stratify(&rule_graph);

    // Check for cycles with negation
    for cycle in &stratification {
        for rule in cycle {
            for atom in &rule.body {
                if !atom.sign && cycle.iter().any(|r| r.head.symbol == atom.symbol) {
                    let message = format!("Negated dependencies form a cycle in SCC: {:?}", cycle);
                    let ident_with_span =
                        string_to_ident_with_span(&atom.symbol, syn::__private::Span::call_site());
                    return syn::Error::new(ident_with_span.span(), message)
                        .to_compile_error()
                        .into();
                }
            }
        }
    }

    semipositive_program(input_clone)
}
