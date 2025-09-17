use strum::EnumIter;

mod finite_kripke_frame;
mod formula;
mod valuation;

use finite_kripke_frame::FiniteKripkeFrame;

#[derive(Debug, EnumIter, Clone, Copy)]
enum OfficialGamePropVar {
    P,
    Q,
    R,
    S,
}

fn main() {
    println!(
        "{}",
        FiniteKripkeFrame::<4>::CANONICALIZED_FRAME_ID
            .as_slice()
            .iter()
            .enumerate()
            .filter(|a| a.0 == *a.1 as usize)
            .count()
    );
}
