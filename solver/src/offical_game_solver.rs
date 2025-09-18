#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum OfficialGamePropVar {
    P,
    Q,
    R,
    S,
}

mod parsing {
    use super::OfficialGamePropVar;

    pub fn parse_official_game_formula(
        _s: &str,
    ) -> Result<crate::formula::Formula<OfficialGamePropVar>, String> {
        use combine::Parser;
        use combine::parser::char::string;
        use combine::parser::choice::choice;

        crate::parser::parse_formula_str(
            _s,
            choice((
                string("P").map(|_| OfficialGamePropVar::P),
                string("Q").map(|_| OfficialGamePropVar::Q),
                string("R").map(|_| OfficialGamePropVar::R),
                string("S").map(|_| OfficialGamePropVar::S),
            )),
        )
        .map_err(|e| format!("Parse error: {}", e))
    }
}
