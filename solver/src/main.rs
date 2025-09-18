mod finite_kripke_frame;
mod formula;
mod offical_game_solver;
mod parser;
mod valuation;

fn main() {
    println!("{:?}", offical_game_solver::come_up_with_strategy())
}
