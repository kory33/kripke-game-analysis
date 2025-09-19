use std::{collections::HashMap, fmt::Display, sync::LazyLock, u8};

use itertools::Itertools;

use crate::{finite_kripke_frame::FiniteKripkeFrame, formula::Formula};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum OfficialGamePropVar {
    P,
    Q,
    R,
    S,
}

impl Display for OfficialGamePropVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OfficialGamePropVar::P => write!(f, "p"),
            OfficialGamePropVar::Q => write!(f, "q"),
            OfficialGamePropVar::R => write!(f, "r"),
            OfficialGamePropVar::S => write!(f, "s"),
        }
    }
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
                choice((string("P"), string("p"))).map(|_| OfficialGamePropVar::P),
                choice((string("Q"), string("q"))).map(|_| OfficialGamePropVar::Q),
                choice((string("R"), string("r"))).map(|_| OfficialGamePropVar::R),
                choice((string("S"), string("s"))).map(|_| OfficialGamePropVar::S),
            )),
        )
        .map_err(|e| format!("Parse error: {}", e))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StrategyAgainstFixedWorldCount {
    ProceedWithExhaustiveSearch,
    AskQueryAndThen {
        query: Formula<OfficialGamePropVar>,
        cont: HashMap</* answer world count */ u8, Box<StrategyAgainstFixedWorldCount>>,
    },
}

#[derive(Debug)]
#[allow(dead_code)]
pub struct KripkeGameStrategy(
    HashMap</* accessibility relation size */ u8, StrategyAgainstFixedWorldCount>,
);

// When searching for a strategy, instead of considering the explicit pair (relation count, query-answer history)
// as a game state, we actually only need to consider the set of all equivalence classes of worlds that
// conform to the pair (relation count, query-answer history).
type PossibleFramesForState = Vec<&'static FiniteKripkeFrame<4>>;

struct GameHistoryElement {
    query: Formula<OfficialGamePropVar>,
    answer_count: u8,
    possible_frames_split: HashMap<u8, Vec<&'static FiniteKripkeFrame<4>>>,
}

struct DiagnosticTrace {
    game_history: Vec<GameHistoryElement>,
    relation_count: u8,
}

impl DiagnosticTrace {
    fn history_to_string(&self) -> String {
        format!(
            "[{}]",
            &self.game_history.iter().format_with(" / ", |e, f| {
                f(&format_args!(
                    "{} ~> {} (splits: {{{}}})",
                    e.query,
                    e.answer_count,
                    e.possible_frames_split
                        .iter()
                        .sorted_by_key(|e| e.0)
                        .format_with(", ", |(k, v), f| { f(&format_args!("{}: {}", k, v.len())) })
                ))
            })
        )
    }
}

fn come_up_with_strategy_for(
    remaining_moves: u8,
    possible_frames: PossibleFramesForState,

    trace: &mut DiagnosticTrace,
) -> StrategyAgainstFixedWorldCount {
    static QUERIES_TO_TRY: LazyLock<Vec<Formula<OfficialGamePropVar>>> = LazyLock::new(|| {
        vec![
            // 1. nodes with self-loops
            "p → ◇p",
            // 2. nodes such that the only outgoing edge (if any) is a self-loop
            "p → □p",
            // 3. nodes with an edge to (1)-nodes
            "◇(p → ◇p)",
            // 4. nodes having 2-way edges into (1)-nodes
            "r → ◇((p → ◇p) ∧ ◇r)",
            // 5. nodes in size-2 cycle
            "p → ◇◇p",
            // 6. nodes where all outgoing edges are two-way
            "p → □◇p",
            // 7. nodes with an edge into (2)-nodes
            "◇(p → □p)",
            // 8. sink nodes
            "□⊥",
            // 9. nodes with an edge to a (8)-node
            "◇□⊥",
            // 10. nodes where all outgoing edges lead to (1)-nodes
            "□(p → ◇p)",
            // 11. nodes in size-3 cycle
            "p → ◇◇◇p",
            // 12. nodes in size-4 cycle
            "p → ◇◇◇◇p",
            // 13. nodes with an outgoing edge
            "◇⊤",
            // 14. nodes with an edge to (10)-nodes
            "◇□(p → ◇p)",
            // 15. a query separating [5602, 5767, 6019, 6050, 6373, 7334]
            "(p → ◇p) ∧ (q → ◇◇◇q)",
        ]
        .into_iter()
        .map(|s| parsing::parse_official_game_formula(s).unwrap())
        .collect()
    });

    if remaining_moves == 0 {
        panic!(
            "Ran out of moves with {} possible frames left (|R| = {}). Past moves: {}. Possible frames: {:?}. Run the following command to visualize them: \n####\n{}\n####",
            possible_frames.len(),
            trace.relation_count,
            trace.history_to_string(),
            possible_frames
                .iter()
                .map(|f| f.to_u16_id())
                .collect::<Vec<_>>(),
            format!(
                // works in GNU bash (version 5.0.17(1)-release) + graphviz (version 13.1.2) + Chromium (version 140.0.7339.127)
                r#"graph_data=$(cat <<EOF
{}
EOF
); svg_html='<!DOCTYPE html>'; while IFS= read -r line; do svg_html+="<div style=\"margin-right: 100px; display: inline\">$(echo "$line" | dot -Tsvg)</div>"; done <<< "$graph_data"; chromium $(echo -n "data:text/html;base64,"; echo "$svg_html" | base64 -w 0)"#,
                possible_frames
                    .iter()
                    .map(|f| f.into_graphviz_dot_string())
                    .join("\n"),
            )
        );
    } else if possible_frames.len() <= remaining_moves as usize {
        StrategyAgainstFixedWorldCount::ProceedWithExhaustiveSearch
    } else {
        let (query, resulting_possible_frames) = QUERIES_TO_TRY
            .iter()
            .map(|formula| {
                let mut frames_grouped_by_answer_count: HashMap<
                    u8,
                    Vec<&'static FiniteKripkeFrame<4>>,
                > = HashMap::new();
                for frame in &possible_frames {
                    frames_grouped_by_answer_count
                        .entry(frame.number_of_worlds_validating(formula))
                        .or_insert_with(Vec::new)
                        .push(frame);
                }
                (formula, frames_grouped_by_answer_count)
            })
            .min_by_key(|(_, grouping)| grouping.values().map(|v| v.len()).max().unwrap_or(0))
            .unwrap();

        let mut cont = HashMap::new();
        let resulting_possible_frames_cloned = resulting_possible_frames.clone();
        for (answer_count, frames) in resulting_possible_frames {
            if frames.len() > 0 {
                trace.game_history.push(GameHistoryElement {
                    query: query.clone(),
                    answer_count: answer_count,
                    possible_frames_split: resulting_possible_frames_cloned.clone(),
                });
                let substrategies = come_up_with_strategy_for(remaining_moves - 1, frames, trace);
                trace.game_history.pop();

                cont.insert(answer_count, Box::new(substrategies));
            }
        }

        StrategyAgainstFixedWorldCount::AskQueryAndThen {
            query: query.clone(),
            cont,
        }
    }
}

pub fn come_up_with_strategy() -> KripkeGameStrategy {
    let mut strategies = HashMap::new();

    let mut frames_grouped_by_relation_count: HashMap<u8, Vec<&'static FiniteKripkeFrame<4>>> =
        FiniteKripkeFrame::<4>::canonical_frames().into_iter().fold(
            HashMap::new(),
            |mut acc, frame| {
                let rel_count = frame.accessibility_relation_count() as u8;
                acc.entry(rel_count).or_insert_with(Vec::new).push(frame);
                acc
            },
        );

    for relation_count in 0u8..=16 {
        println!(
            "Computing strategy for relation count = {}...",
            relation_count
        );
        strategies.insert(
            relation_count,
            come_up_with_strategy_for(
                10,
                frames_grouped_by_relation_count
                    .remove(&relation_count)
                    .unwrap_or(vec![]),
                &mut DiagnosticTrace {
                    game_history: vec![],
                    relation_count,
                },
            ),
        );
        println!("...done.");
    }

    KripkeGameStrategy(strategies)
}
