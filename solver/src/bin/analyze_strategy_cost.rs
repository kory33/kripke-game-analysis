extern crate kripke_game_solver;

use kripke_game_solver::finite_kripke_frame::FiniteKripkeFrame;
use kripke_game_solver::offical_game_solver::{
    StrategyAgainstFixedWorldCount, answer_distribution_for_query, come_up_with_strategy,
};

fn walk(
    strategy: &StrategyAgainstFixedWorldCount,
    possible_frames: Vec<&'static FiniteKripkeFrame<4>>,
    total_nodes: &mut usize,
    total_frame_query_checks: &mut usize,
) {
    match strategy {
        StrategyAgainstFixedWorldCount::ProceedWithExhaustiveSearch => {}
        StrategyAgainstFixedWorldCount::AskQueryAndThen { query, cont } => {
            *total_nodes += 1;
            *total_frame_query_checks += possible_frames.len();
            let buckets = answer_distribution_for_query(&possible_frames, query);
            for answer in 0..=4u8 {
                let child = cont
                    .get(&answer)
                    .map(|child| child.as_ref())
                    .unwrap_or(&StrategyAgainstFixedWorldCount::ProceedWithExhaustiveSearch);
                walk(
                    child,
                    buckets.get(&answer).cloned().unwrap_or_default(),
                    total_nodes,
                    total_frame_query_checks,
                );
            }
        }
    }
}

fn main() {
    let strategy = come_up_with_strategy();
    let grouped = FiniteKripkeFrame::<4>::canonical_frames_grouped_by_accessibility_count();

    let mut total_nodes = 0usize;
    let mut total_frame_query_checks = 0usize;

    for relation_count in 0u8..=16 {
        let frames = grouped.get(&relation_count).cloned().unwrap_or_default();
        let strategy_for_count = strategy.0.get(&relation_count).unwrap();
        let mut nodes = 0usize;
        let mut checks = 0usize;
        walk(strategy_for_count, frames, &mut nodes, &mut checks);
        total_nodes += nodes;
        total_frame_query_checks += checks;
        println!(
            "relation_count={} nodes={} frame_query_checks={}",
            relation_count, nodes, checks
        );
    }

    println!("total_nodes={}", total_nodes);
    println!("total_frame_query_checks={}", total_frame_query_checks);
}
