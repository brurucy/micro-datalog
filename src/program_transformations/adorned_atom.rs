use datalog_syntax::*;
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Adornment {
    Bound,
    Free,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AdornedAtom {
    pub atom: Atom,
    pub adornment: Vec<Adornment>,
}

impl AdornedAtom {
    pub fn get_pattern_string(&self) -> String {
        self.adornment.iter()
            .map(|a| match a {
                Adornment::Bound => "b",
                Adornment::Free => "f",
            })
            .collect()
    }

    pub fn from_atom_and_bound_vars(atom: &Atom, bound_vars: &HashSet<String>) -> Self {
        let adornment = atom.terms.iter()
            .map(|term| match term {
                Term::Constant(_) => Adornment::Bound,
                Term::Variable(var) => {
                    if bound_vars.contains(var) {
                        Adornment::Bound
                    } else {
                        Adornment::Free
                    }
                }
            })
            .collect();

        AdornedAtom {
            atom: atom.clone(),
            adornment,
        }
    }

    pub fn from_modified_atom(atom: Atom) -> Self {
        let parts: Vec<&str> = atom.symbol.split('_').collect();
        
        if parts.len() <= 1 {
            // If there's no underscore or only one part, return the original atom
            // with all terms marked as free
            let adornment = vec![Adornment::Free; atom.terms.len()];
            return AdornedAtom {
                atom: atom.clone(),
                adornment,
            };
        }
        
        // Split into: all parts except last, and the last part
        let (prefix_parts, last_part) = parts.split_at(parts.len() - 1);
        let prefix = prefix_parts.join("_");
        let suffix = last_part[0];
        
        // Create adornment based on the suffix characters
        let adornment: Vec<Adornment> = suffix.chars()
            .map(|c| match c {
                'b' => Adornment::Bound,
                'f' => Adornment::Free,
                _ => Adornment::Free, // Default to free for any other characters
            })
            .collect();
        
        AdornedAtom {
            atom: Atom { terms: atom.terms, symbol: prefix, sign: atom.sign },
            adornment,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_adorn_atom() {
        let mut bound_vars = HashSet::new();
        bound_vars.insert("X".to_string());
        
        let atom = Atom {
            symbol: "p".to_string(),
            terms: vec![
                Term::Variable("X".to_string()),
                Term::Variable("Y".to_string()),
                Term::Constant(TypedValue::from("a")),
            ],
            sign: true,
        };

        let adorned = AdornedAtom::from_atom_and_bound_vars(&atom, &bound_vars);
        assert_eq!(adorned.adornment, vec![
            Adornment::Bound,  // X is bound
            Adornment::Free,   // Y is free
            Adornment::Bound,  // constant is bound
        ]);
    }
}