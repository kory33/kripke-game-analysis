use std::fmt::Display;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Formula<V> {
    Var(V),
    True,
    False,
    Not(Box<Formula<V>>),
    MBox(Box<Formula<V>>),
    MDia(Box<Formula<V>>),
    And(Box<Formula<V>>, Box<Formula<V>>),
    Or(Box<Formula<V>>, Box<Formula<V>>),
    Imp(Box<Formula<V>>, Box<Formula<V>>),
    Iff(Box<Formula<V>>, Box<Formula<V>>),
}

mod printing {
    pub enum PrintPosition {
        TopLevel,
        UnderUnaryOp,
        InAndClause,
        InOrClause,
        InImpRhs,
        InImpLhs,
        InIffClause,
    }

    impl<V: ToString> super::Formula<V> {
        pub fn to_string_at(&self, position: PrintPosition) -> String {
            use PrintPosition::*;

            match self {
                super::Formula::Var(v) => v.to_string(),
                super::Formula::True => "⊤".to_string(),
                super::Formula::False => "⊥".to_string(),
                super::Formula::Not(formula) => {
                    format!("¬{}", formula.to_string_at(UnderUnaryOp))
                }
                super::Formula::MBox(formula) => {
                    format!("□{}", formula.to_string_at(UnderUnaryOp))
                }
                super::Formula::MDia(formula) => {
                    format!("◇{}", formula.to_string_at(UnderUnaryOp))
                }
                super::Formula::And(formula, formula1) => {
                    let s = format!(
                        "{} ∧ {}",
                        formula.to_string_at(InAndClause),
                        formula1.to_string_at(InAndClause)
                    );

                    match position {
                        UnderUnaryOp | InOrClause => {
                            format!("({})", s)
                        }
                        _ => s,
                    }
                }
                super::Formula::Or(formula, formula1) => {
                    let s = format!(
                        "{} ∨ {}",
                        formula.to_string_at(InOrClause),
                        formula1.to_string_at(InOrClause)
                    );
                    match position {
                        UnderUnaryOp | InAndClause => {
                            format!("({})", s)
                        }
                        _ => s,
                    }
                }
                super::Formula::Imp(formula, formula1) => {
                    let s = format!(
                        "{} → {}",
                        formula.to_string_at(PrintPosition::InImpLhs),
                        formula1.to_string_at(PrintPosition::InImpRhs)
                    );
                    match position {
                        UnderUnaryOp | InAndClause | InOrClause | InImpLhs | InIffClause => {
                            format!("({})", s)
                        }
                        _ => s,
                    }
                }
                super::Formula::Iff(formula, formula1) => {
                    let s = format!(
                        "{} ↔ {}",
                        formula.to_string_at(PrintPosition::InIffClause),
                        formula1.to_string_at(PrintPosition::InIffClause)
                    );
                    match position {
                        TopLevel => s,
                        _ => {
                            format!("({})", s)
                        }
                    }
                }
            }
        }
    }
}

impl<V: Display> Display for Formula<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.to_string_at(printing::PrintPosition::TopLevel)
        )
    }
}

impl<V: Eq> Formula<V> {
    pub fn variables_dedup(&self) -> Vec<&V> {
        match self {
            Formula::Var(v) => vec![v],
            Formula::True | Formula::False => vec![],
            Formula::Not(f) | Formula::MBox(f) | Formula::MDia(f) => f.variables_dedup(),
            Formula::And(f1, f2)
            | Formula::Or(f1, f2)
            | Formula::Imp(f1, f2)
            | Formula::Iff(f1, f2) => {
                let mut vars = f1.variables_dedup();
                for v in f2.variables_dedup() {
                    if !vars.contains(&v) {
                        vars.push(v);
                    }
                }
                vars
            }
        }
    }
}
