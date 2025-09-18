use std::fmt::Debug;

use combine::Parser;

use crate::formula::Formula;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok<V> {
    Var(V),
    True,
    False,
    LParen,
    RParen,
    Not,
    Box,
    Dia,
    And,
    Or,
    Imp,
    Iff,
}

mod tokenize {
    use super::Tok;
    use combine::parser::char::{char, space, string};
    use combine::parser::choice::choice;
    use combine::parser::combinator::attempt;
    use combine::parser::repeat::{many1, skip_many};
    use combine::{Parser, Stream};

    // Whitespace helpers (ws0 = optional whitespace). We avoid nested skip_many(spaces())
    // because `spaces()` itself can succeed without consuming, which inside another
    // skip_many caused an infinite loop. Using `space()` (single char) prevents that.
    fn ws0<I>() -> impl Parser<I, Output = ()>
    where
        I: Stream<Token = char>,
    {
        skip_many(space())
    }

    fn token<V, I>(parse_var: impl Parser<I, Output = V>) -> impl Parser<I, Output = Tok<V>>
    where
        I: Stream<Token = char>,
    {
        choice((
            choice((string("<->"), string("↔"))).map(|_| Tok::Iff),
            choice((string("->"), string("→"))).map(|_| Tok::Imp),
            choice((string("[]"), string("□"))).map(|_| Tok::Box),
            choice((string("<>"), string("◇"))).map(|_| Tok::Dia),
            choice((string("T"), string("⊤"))).map(|_| Tok::True),
            choice((string("F"), string("⊥"))).map(|_| Tok::False),
            char('(').map(|_| Tok::LParen),
            char(')').map(|_| Tok::RParen),
            choice((char('¬'), char('~'))).map(|_| Tok::Not),
            choice((char('∧'), char('^'), char('&'))).map(|_| Tok::And),
            choice((char('∨'), char('v'), char('|'))).map(|_| Tok::Or),
            attempt(parse_var).map(|v| Tok::Var(v)),
        ))
    }

    pub fn tokens<V, I>(
        parse_var: impl Parser<I, Output = V>,
    ) -> impl Parser<I, Output = Vec<Tok<V>>>
    where
        I: Stream<Token = char>,
    {
        ws0().with(many1(token(parse_var).skip(ws0())))
    }
}

mod parse {
    use super::Tok;
    use crate::formula::Formula;
    use combine::between;
    use combine::parser;
    use combine::token;
    use combine::{ParseError, Parser, Stream, satisfy_map};

    fn parse_atom<V: Eq + Clone, I>() -> impl Parser<I, Output = Formula<V>>
    where
        I: Stream<Token = Tok<V>>,
    {
        let parse_var = || {
            satisfy_map(|t: Tok<V>| match t {
                Tok::Var(v) => Some(Formula::Var(v)),
                _ => None,
            })
        };
        let parse_true = || token(Tok::True).map(|_| Formula::True);
        let parse_false = || token(Tok::False).map(|_| Formula::False);

        parse_var().or(parse_true()).or(parse_false()).or(between(
            token(Tok::LParen),
            token(Tok::RParen),
            parse_formula(),
        ))
    }

    fn parse_prefix<V: Eq + Clone, I>() -> impl Parser<I, Output = Formula<V>>
    where
        I: Stream<Token = Tok<V>>,
    {
        use combine::Parser;
        use combine::parser::repeat::many;

        // prefix := (Not | Box | Dia)* atom
        many(token(Tok::Not).or(token(Tok::Box)).or(token(Tok::Dia)))
            .and(parse_atom())
            .map(|(ops, base): (Vec<Tok<V>>, Formula<V>)| {
                ops.into_iter().rev().fold(base, |acc, op| match op {
                    Tok::Not => Formula::Not(Box::new(acc)),
                    Tok::Box => Formula::MBox(Box::new(acc)),
                    Tok::Dia => Formula::MDia(Box::new(acc)),
                    _ => unreachable!(),
                })
            })
    }

    fn parse_and<V: Clone + Eq, I>() -> impl Parser<I, Output = Formula<V>>
    where
        I: Stream<Token = Tok<V>>,
    {
        use combine::Parser;
        use combine::parser::repeat::many;
        use combine::parser::token::token;

        // and := prefix (And prefix)* (left associative)
        parse_prefix()
            .and(many(token(Tok::And).with(parse_prefix())))
            .map(|(first, rest): (Formula<V>, Vec<Formula<V>>)| {
                rest.into_iter()
                    .fold(first, |a, b| Formula::And(Box::new(a), Box::new(b)))
            })
    }

    fn parse_or<V: Clone + Eq, I>() -> impl Parser<I, Output = Formula<V>>
    where
        I: Stream<Token = Tok<V>>,
    {
        use combine::Parser;
        use combine::parser::repeat::many;
        use combine::parser::token::token;

        // or := and (Or and)*
        parse_and().and(many(token(Tok::Or).with(parse_and()))).map(
            |(first, rest): (Formula<V>, Vec<Formula<V>>)| {
                rest.into_iter()
                    .fold(first, |a, b| Formula::Or(Box::new(a), Box::new(b)))
            },
        )
    }

    fn parse_imp<V: Clone + Eq, I>() -> impl Parser<I, Output = Formula<V>>
    where
        I: Stream<Token = Tok<V>>,
    {
        use combine::Parser;
        use combine::parser::repeat::many;
        use combine::parser::token::token;

        // imp := or (Imp or)* right associative
        parse_or().and(many(token(Tok::Imp).with(parse_or()))).map(
            |(first, rest): (Formula<V>, Vec<Formula<V>>)| {
                rest.into_iter()
                    .rev()
                    .fold(first, |l, r| Formula::Imp(Box::new(l), Box::new(r)))
            },
        )
    }

    fn parse_iff<V: Clone + Eq, I>() -> impl Parser<I, Output = Formula<V>>
    where
        I: Stream<Token = Tok<V>>,
    {
        use combine::Parser;
        use combine::parser::repeat::many;
        use combine::parser::token::token;

        // iff := imp (Iff imp)* left associative
        parse_imp()
            .and(many(token(Tok::Iff).with(parse_imp())))
            .map(|(first, rest): (Formula<V>, Vec<Formula<V>>)| {
                rest.into_iter()
                    .fold(first, |l, r| Formula::Iff(Box::new(l), Box::new(r)))
            })
    }

    fn parse_formula_<V: Clone + Eq, I>() -> impl Parser<I, Output = Formula<V>>
    where
        I: Stream<Token = Tok<V>>,
    {
        parse_iff()
    }

    parser! {
        pub fn parse_formula[V, I]()(I) -> Formula<V>
        where [
            V: Clone + Eq,
            I: Stream<Token = Tok<V>>,
        ]
        {
            parse_formula_()
        }
    }
}

/// Parse a modal formula from a string into a `Formula<String>`.
///
/// Supported syntax (ASCII alternatives in parentheses):
///   Constants:  ⊤ (T), ⊥ (F)
///   Variables:  one or more ASCII alphabetic characters (e.g. p, q, state1 is not supported – only letters)
///   Unary:      ~ (¬)  [] (□)  <> (◇)
///   Binary:     ^ & ∧, | v ∨, -> →, <-> ↔
///   Precedence  (tightest to loosest): unary prefix ops, And, Or, Implication, Iff
///   Parentheses: ( ... )
#[allow(dead_code)]
pub fn parse_formula_str<'a, V: Clone + Eq + Debug>(
    input: &'a str,
    tokenize_vars: impl Parser<combine::easy::Stream<&'a str>, Output = V>,
) -> Result<Formula<V>, String> {
    use combine::EasyParser;

    let (toks, remainder) = match tokenize::tokens(tokenize_vars).easy_parse(input) {
        Ok(ok) => ok,
        Err(e) => return Err(format!("tokenization error: {e}")),
    };
    if !remainder.is_empty() {
        return Err(format!(
            "unexpected trailing input starting at: {}",
            remainder
        ));
    }

    match parse::parse_formula().easy_parse(toks.as_slice()) {
        Ok((formula, remaining)) => {
            if remaining.is_empty() {
                Ok(formula)
            } else {
                Err(format!(
                    "unexpected trailing tokens after formula {:?}: {:?}",
                    formula, remaining
                ))
            }
        }
        Err(e) => Err(format!("parse error: {:?}", e)),
    }
}
