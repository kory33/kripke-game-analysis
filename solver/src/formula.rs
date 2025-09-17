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
