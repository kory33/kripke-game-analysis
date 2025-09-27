extern crate kripke_game_solver;

use clap::*;
use itertools::Itertools;
use kripke_game_solver::finite_kripke_frame::*;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    #[arg(short, long)]
    frames: Option<String>,
}

// example usage: cargo run --bin visualize_frames -- --frames "38265, 38373"
fn main() {
    let cli = Cli::parse();
    let frames_input = if let Some(frames_str) = cli.frames {
        frames_str
    } else {
        println!(
            "Input comma-separated u16 IDs of frames to visualize, e.g. `36015,36027,36077`: "
        );
        let mut input = String::new();
        std::io::stdin().read_line(&mut input).unwrap();
        input
    };
    let frames = frames_input
        .split(',')
        .map(str::trim)
        .map(|s| s.parse::<u16>().unwrap())
        .map(|id| FiniteKripkeFrame::<4>::from_u16_id(id))
        .collect::<Vec<_>>();

    println!(
        // works in GNU bash (version 5.0.17(1)-release) + graphviz (version 13.1.2) + Chromium (version 140.0.7339.127)
        r#"####
graph_data=$(cat <<EOF
{}
EOF
); svg_html='<!DOCTYPE html>'; while IFS= read -r line; do svg_html+="<div style=\"margin-right: 100px; display: inline\">$(echo "$line" | dot -Tsvg)</div>"; done <<< "$graph_data"; chromium $(echo -n "data:text/html;base64,"; echo "$svg_html" | base64 -w 0)
####
"#,
        frames
            .iter()
            .map(|f| f.into_graphviz_dot_string())
            .join("\n"),
    )
}
