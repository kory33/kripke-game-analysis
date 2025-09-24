extern crate kripke_game_solver;

use kripke_game_solver::*;
use std::collections::{BTreeMap, HashSet};

fn main() {
    let mut minmax_frame_counts =
        finite_kripke_frame::FiniteKripkeFrame::<4>::canonical_frames().len();
    let mut printed_distribution = HashSet::new();
    offical_game_solver::search_for_formula_to_split_frames(
        finite_kripke_frame::FiniteKripkeFrame::<4>::canonical_frames_grouped_by_accessibility_count().get(&4).unwrap(),
        |grouping| {
            let frame_counts = grouping
                .iter()
                .map(|(k, v)| (k.clone(), v.len()))
                .collect::<BTreeMap<u8, usize>>();
            let max_frame_count = frame_counts.iter().map(|(_, v)| *v).max().unwrap_or(5000);

            let do_print = max_frame_count as f32 <= minmax_frame_counts as f32 * 1.5
                && !(
                    // if these conditions are true, the current formula is
                    // probably equivalent/dual to a previously printed one, so skip
                    printed_distribution.contains(&frame_counts)
                        || printed_distribution
                            .contains(&frame_counts.iter().map(|(k, v)| (4 - *k, *v)).collect())
                );

            if max_frame_count < minmax_frame_counts {
                minmax_frame_counts = max_frame_count;
            }
            if do_print {
                printed_distribution.insert(frame_counts.clone());
            }
            do_print
        },
        7,
    );
}
