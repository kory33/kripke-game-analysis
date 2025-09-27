extern crate kripke_game_solver;

use itertools::Itertools;
use kripke_game_solver::{finite_kripke_frame::FiniteKripkeFrame, offical_game_solver::*};
use rand::Rng;
use rayon::prelude::*;

fn main() {
    let frames = vec![38777, 38889]
        .into_iter()
        .map(|id| FiniteKripkeFrame::<4>::from_u16_id(id))
        .collect::<Vec<_>>();

    enumerate_formulae_of_exact_size(10, 0)
        .par_bridge()
        .for_each_init(
            || rand::rng(),
            |rng, (formula, _)| {
                let grouping = answer_distribution_for_query(&frames, &formula);
                if grouping.len() > 1 {
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
                } else if rng.random_ratio(1, 100000) {
                    println!("Checked formula {}, but no luck", formula);
                }
            },
        );
}
