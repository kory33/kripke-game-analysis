use std::{collections::BTreeMap, fmt::Display, sync::LazyLock, u8};

use itertools::{Itertools, chain};

use crate::{finite_kripke_frame::FiniteKripkeFrame, formula::Formula};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[allow(dead_code)]
pub enum OfficialGamePropVar {
    P,
    Q,
    R,
    S,
}

impl OfficialGamePropVar {
    pub fn from_ordinal_clamped(ordinal: u8) -> OfficialGamePropVar {
        match ordinal {
            0 => OfficialGamePropVar::P,
            1 => OfficialGamePropVar::Q,
            2 => OfficialGamePropVar::R,
            _ => OfficialGamePropVar::S,
        }
    }
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

pub mod parsing {
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
        cont: BTreeMap</* answer world count */ u8, Box<StrategyAgainstFixedWorldCount>>,
    },
}

#[derive(Debug)]
#[allow(dead_code)]
pub struct KripkeGameStrategy(
    BTreeMap</* accessibility relation size */ u8, StrategyAgainstFixedWorldCount>,
);

// When searching for a strategy, instead of considering the explicit pair (relation count, query-answer history)
// as a game state, we actually only need to consider the set of all equivalence classes of worlds that
// conform to the pair (relation count, query-answer history).
type PossibleFramesForState = Vec<&'static FiniteKripkeFrame<4>>;

struct GameHistoryElement {
    query: Formula<OfficialGamePropVar>,
    answer_count: u8,
    possible_frames_split: BTreeMap<u8, Vec<&'static FiniteKripkeFrame<4>>>,
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

pub fn answer_distribution_for_query(
    possible_frames: &[&'static FiniteKripkeFrame<4>],
    query: &Formula<OfficialGamePropVar>,
) -> BTreeMap<u8, Vec<&'static FiniteKripkeFrame<4>>> {
    let mut frames_grouped_by_answer_count: BTreeMap<u8, Vec<&'static FiniteKripkeFrame<4>>> =
        BTreeMap::new();
    for frame in possible_frames {
        frames_grouped_by_answer_count
            .entry(frame.number_of_worlds_validating(query))
            .or_insert_with(Vec::new)
            .push(frame);
    }
    frames_grouped_by_answer_count
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
            // 15. nodes with outdegree <= 1 (separates [4469, 4473, 4581, 4711, 5033])
            "◇p → □p",
            // 16. all nodes reachable in exactly 2 steps are reachable in exactly 1 step (separates [5625, 5869, 6061, 6073, 6121])
            "◇◇p → ◇p",
            // 17. nodes where all next nodes are mutually reachable (separates [5594, 6042, 6588, 6636, 7084])
            "□p → □◇p",
            // 18. query separating [6046, 6590, 7100]
            "◇(p → □□p)",
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
                (
                    formula,
                    answer_distribution_for_query(&possible_frames, formula),
                )
            })
            .min_by_key(|(_, grouping)| grouping.values().map(|v| v.len()).max().unwrap_or(0))
            .unwrap();

        let mut cont = BTreeMap::new();
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
    let mut strategies = BTreeMap::new();

    for relation_count in 0u8..=16 {
        let possible_frames =
            FiniteKripkeFrame::<4>::canonical_frames_grouped_by_accessibility_count()
                .get(&relation_count)
                .cloned()
                .unwrap_or(vec![]);
        println!(
            "Computing strategy for relation count = {} (total frames to classify = {})...",
            relation_count,
            possible_frames.len()
        );
        strategies.insert(
            relation_count,
            come_up_with_strategy_for(
                10,
                possible_frames,
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

fn enumerate_formulae_of_exact_size(
    size: u8,
    already_used_vars_count: u8,
) -> Box<
    dyn Iterator<
        Item = (
            Formula<OfficialGamePropVar>,
            u8, /* used variables count */
        ),
    >,
> {
    if size <= 1 {
        Box::new(chain!(
            vec![Formula::True, Formula::False]
                .into_iter()
                .map(move |f| (f, already_used_vars_count)),
            // always use variables in increasing order (Do not use Q before using P etc.)
            (0..already_used_vars_count).map(move |i| {
                (
                    Formula::Var(OfficialGamePropVar::from_ordinal_clamped(i)),
                    already_used_vars_count,
                )
            }),
            if already_used_vars_count < 4 {
                vec![(
                    Formula::Var(OfficialGamePropVar::from_ordinal_clamped(
                        already_used_vars_count,
                    )),
                    already_used_vars_count + 1,
                )]
                .into_iter()
            } else {
                vec![].into_iter()
            }
        ))
    } else {
        Box::new(chain!(
            enumerate_formulae_of_exact_size(size - 1, already_used_vars_count)
                .map(|(f, uvc)| (Formula::Not(Box::new(f)), uvc)),
            enumerate_formulae_of_exact_size(size - 1, already_used_vars_count)
                .map(|(f, uvc)| (Formula::MBox(Box::new(f)), uvc)),
            enumerate_formulae_of_exact_size(size - 1, already_used_vars_count)
                .map(|(f, uvc)| (Formula::MDia(Box::new(f)), uvc)),
            (1..(size - 1))
                .flat_map(|left_size| {
                    let right_size = size - 1 - left_size;
                    enumerate_formulae_of_exact_size(left_size, already_used_vars_count)
                        .flat_map(move |(f1, uvc1)| {
                            enumerate_formulae_of_exact_size(right_size, uvc1)
                                .map(move |(f2, uvc2)| (f1.clone(), f2, uvc2))
                        })
                        .flat_map(|(f1, f2, uvc2)| {
                            vec![
                                Formula::And(Box::new(f1.clone()), Box::new(f2.clone())),
                                Formula::Or(Box::new(f1.clone()), Box::new(f2.clone())),
                                Formula::Imp(Box::new(f1.clone()), Box::new(f2.clone())),
                                Formula::Iff(Box::new(f1.clone()), Box::new(f2)),
                            ]
                            .into_iter()
                            .map(move |f| (f, uvc2))
                        })
                })
                .collect::<Vec<_>>()
                .into_iter()
        ))
    }
}

pub fn enumerate_formulae_up_to_size(
    size: u8,
) -> impl Iterator<Item = Formula<OfficialGamePropVar>> {
    Box::new((1..=size).flat_map(|s| enumerate_formulae_of_exact_size(s, 0))).map(|(f, _)| f)
}

pub fn indefinitely_enumelate_formulae() -> impl Iterator<Item = Formula<OfficialGamePropVar>> {
    (1..)
        .flat_map(|s| enumerate_formulae_of_exact_size(s, 0))
        .map(|(f, _)| f)
}

pub fn search_for_formula_to_split_frames(
    frames: &[&'static FiniteKripkeFrame<4>],
    mut printing_condition: impl FnMut(&BTreeMap<u8, Vec<&'static FiniteKripkeFrame<4>>>) -> bool,
    formula_size_bound: u8,
) {
    for formula in enumerate_formulae_up_to_size(formula_size_bound) {
        let grouping = answer_distribution_for_query(frames, &formula);
        if printing_condition(&grouping) {
            println!(
                "Formula {} splits {} frames into groups of sizes: {{{}}}",
                formula,
                frames.len(),
                grouping
                    .iter()
                    .sorted_by_key(|e| e.0)
                    .map(|(k, v)| format!("{}: {}", k, v.len()))
                    .join(", "),
            );
        }
    }
}
