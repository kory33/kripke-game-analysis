mod finite_kripke_frame;
mod formula;
mod offical_game_solver;
mod parser;
mod valuation;

fn main() {
    println!("{:?}", offical_game_solver::come_up_with_strategy());

    // offical_game_solver::search_for_formula_to_split_frames(
    //     &vec![6046, 6590, 7100]
    //         .iter()
    //         .map(|id| finite_kripke_frame::FiniteKripkeFrame::from_u16_id(*id))
    //         .collect::<Vec<_>>(),
    //     6,
    // );
}
