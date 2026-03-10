extern crate kripke_game_solver;

use kripke_game_solver::finite_kripke_frame::FiniteKripkeFrame;
use kripke_game_solver::formula::Formula;
use kripke_game_solver::offical_game_solver::{
    OfficialGamePropVar, StrategyAgainstFixedWorldCount, come_up_with_strategy,
    official_game_queries_to_try,
};
use std::collections::BTreeSet;
use std::io::{self, Write};

/// Convert a Rust formula to Lean ModalFormula syntax.
fn formula_to_lean(f: &Formula<OfficialGamePropVar>) -> String {
    match f {
        Formula::Var(v) => match v {
            OfficialGamePropVar::P => "ModalFormula.p".to_string(),
            OfficialGamePropVar::Q => "ModalFormula.q".to_string(),
            OfficialGamePropVar::R => "ModalFormula.r".to_string(),
            OfficialGamePropVar::S => "ModalFormula.s".to_string(),
        },
        Formula::True => "ModalFormula.var (KripkeGameVars.p) |> ModalFormula.or (ModalFormula.not (ModalFormula.var (KripkeGameVars.p)))".to_string(),
        Formula::False => "ModalFormula.var (KripkeGameVars.p) |> ModalFormula.and (ModalFormula.not (ModalFormula.var (KripkeGameVars.p)))".to_string(),
        Formula::Not(inner) => format!("ModalFormula.not ({})", formula_to_lean(inner)),
        Formula::MBox(inner) => format!("ModalFormula.box ({})", formula_to_lean(inner)),
        Formula::MDia(inner) => format!("ModalFormula.dia ({})", formula_to_lean(inner)),
        Formula::And(left, right) => {
            format!("ModalFormula.and ({}) ({})", formula_to_lean(left), formula_to_lean(right))
        }
        Formula::Or(left, right) => {
            format!("ModalFormula.or ({}) ({})", formula_to_lean(left), formula_to_lean(right))
        }
        Formula::Imp(left, right) => {
            format!(
                "ModalFormula.implies ({}) ({})",
                formula_to_lean(left),
                formula_to_lean(right)
            )
        }
        Formula::Iff(left, right) => {
            format!(
                "ModalFormula.and (ModalFormula.implies ({}) ({})) (ModalFormula.implies ({}) ({}))",
                formula_to_lean(left),
                formula_to_lean(right),
                formula_to_lean(right),
                formula_to_lean(left)
            )
        }
    }
}

fn emit_array_chunks<T: std::fmt::Display>(
    output: &mut dyn Write,
    base_name: &str,
    values: &[T],
    chunk_size: usize,
    line_wrap: usize,
) -> io::Result<usize> {
    let chunk_count = values.len().div_ceil(chunk_size);
    for chunk_idx in 0..chunk_count {
        let start = chunk_idx * chunk_size;
        let end = ((chunk_idx + 1) * chunk_size).min(values.len());
        writeln!(
            output,
            "private def {}_chunk_{} : Array Nat :=",
            base_name, chunk_idx
        )?;
        write!(output, "  #[")?;
        for (i, value) in values[start..end].iter().enumerate() {
            if i > 0 {
                write!(output, ", ")?;
            }
            if i % line_wrap == 0 {
                writeln!(output)?;
                write!(output, "    ")?;
            }
            write!(output, "{}", value)?;
        }
        writeln!(output)?;
        writeln!(output, "  ]")?;
        writeln!(output)?;
    }
    Ok(chunk_count)
}

fn collect_used_queries(
    strategy: &StrategyAgainstFixedWorldCount,
    used_queries: &mut BTreeSet<Formula<OfficialGamePropVar>>,
) {
    match strategy {
        StrategyAgainstFixedWorldCount::ProceedWithExhaustiveSearch => {}
        StrategyAgainstFixedWorldCount::AskQueryAndThen { query, cont } => {
            used_queries.insert(query.clone());
            for child in cont.values() {
                collect_used_queries(child, used_queries);
            }
        }
    }
}

fn main() -> io::Result<()> {
    const RAW_FRAME_COUNT: usize = 65536;
    const FRAME_ID_CHUNK_SIZE: usize = 256;
    const RAW_INDEX_CHUNK_SIZE: usize = 1024;
    const QUERY_TABLE_CHUNK_SIZE: usize = 512;

    let strategy = come_up_with_strategy();
    let mut used_queries_set = BTreeSet::new();
    for strategy_for_count in strategy.0.values() {
        collect_used_queries(strategy_for_count, &mut used_queries_set);
    }
    let used_queries = official_game_queries_to_try()
        .iter()
        .filter(|query| used_queries_set.contains(*query))
        .cloned()
        .collect::<Vec<_>>();

    let canonical_frame_ids = FiniteKripkeFrame::<4>::canonical_frames()
        .iter()
        .map(|frame| frame.to_u16_id())
        .collect::<Vec<_>>();
    let canonical_frame_count = canonical_frame_ids.len();

    let mut canonical_frame_index_table = vec![canonical_frame_count; RAW_FRAME_COUNT];
    for (idx, frame_id) in canonical_frame_ids.iter().enumerate() {
        canonical_frame_index_table[*frame_id as usize] = idx;
    }

    let stdout = io::stdout();
    let mut output = stdout.lock();

    eprintln!(
        "Generating precomputed query counts for {} used queries over {} canonical frames...",
        used_queries.len(),
        canonical_frame_count
    );

    writeln!(
        output,
        "-- DO NOT EDIT MANUALLY: Autogenerated by the Kripke Game solver in `/solver`"
    )?;
    writeln!(output)?;
    writeln!(output, "import KripkeGameAnalysis.Game.Basic")?;
    writeln!(output)?;
    writeln!(output, "namespace KripkeGameAnalysis.Precomputed")?;
    writeln!(output)?;
    writeln!(output, "set_option maxRecDepth 10000")?;
    writeln!(output, "set_option maxHeartbeats 1000000")?;
    writeln!(output)?;

    writeln!(
        output,
        "def canonicalFrameCount : Nat := {}",
        canonical_frame_count
    )?;
    writeln!(output)?;

    let frame_id_chunk_count = emit_array_chunks(
        &mut output,
        "canonicalFrameIdsArrayNat",
        &canonical_frame_ids,
        FRAME_ID_CHUNK_SIZE,
        16,
    )?;

    writeln!(
        output,
        "private def canonicalFrameIdsArrayNat : Array Nat :="
    )?;
    for chunk_idx in 0..frame_id_chunk_count {
        if chunk_idx == 0 {
            writeln!(output, "  canonicalFrameIdsArrayNat_chunk_{}", chunk_idx)?;
        } else {
            writeln!(output, "  ++ canonicalFrameIdsArrayNat_chunk_{}", chunk_idx)?;
        }
    }
    writeln!(output)?;

    writeln!(
        output,
        "def canonicalFrameIds : {{ ids : Array (Fin 65536) // ids.size = canonicalFrameCount }} :="
    )?;
    writeln!(output, "  ⟨")?;
    writeln!(
        output,
        "    canonicalFrameIdsArrayNat.map (fun frameId => ⟨frameId, by native_decide⟩)"
    )?;
    writeln!(output, "  , by native_decide")?;
    writeln!(output, "  ⟩")?;
    writeln!(output)?;

    writeln!(
        output,
        "def canonicalFrameId (idx : Fin canonicalFrameCount) : Fin 65536 :="
    )?;
    writeln!(
        output,
        "  canonicalFrameIds.val[idx]'(by simpa [canonicalFrameIds.property] using idx.isLt)"
    )?;
    writeln!(output)?;

    let raw_index_chunk_count = emit_array_chunks(
        &mut output,
        "canonicalFrameIndexTable",
        &canonical_frame_index_table,
        RAW_INDEX_CHUNK_SIZE,
        32,
    )?;

    writeln!(
        output,
        "def canonicalFrameIndexTable : {{ table : Array Nat // table.size = 65536 }} :="
    )?;
    writeln!(output, "  ⟨")?;
    for chunk_idx in 0..raw_index_chunk_count {
        if chunk_idx == 0 {
            writeln!(output, "    canonicalFrameIndexTable_chunk_{}", chunk_idx)?;
        } else {
            writeln!(
                output,
                "    ++ canonicalFrameIndexTable_chunk_{}",
                chunk_idx
            )?;
        }
    }
    writeln!(output, "  , by native_decide")?;
    writeln!(output, "  ⟩")?;
    writeln!(output)?;

    writeln!(
        output,
        "def canonicalFrameIndex (frameId : Fin 65536) : Nat :="
    )?;
    writeln!(
        output,
        "  canonicalFrameIndexTable.val[frameId]'(by simpa [canonicalFrameIndexTable.property] using frameId.isLt)"
    )?;
    writeln!(output)?;

    writeln!(
        output,
        "theorem canonicalFrameId_of_canonicalFrameIndex (frameId : Fin 65536)"
    )?;
    writeln!(
        output,
        "    (h : canonicalFrameIndex frameId < canonicalFrameCount) :"
    )?;
    writeln!(
        output,
        "    canonicalFrameId ⟨canonicalFrameIndex frameId, h⟩ = frameId := by"
    )?;
    writeln!(output, "  native_decide")?;
    writeln!(output)?;

    for (query_idx, query) in used_queries.iter().enumerate() {
        eprintln!(
            "  Computing table for used query {} / {}...",
            query_idx + 1,
            used_queries.len()
        );

        let counts = canonical_frame_ids
            .iter()
            .map(|frame_id| {
                FiniteKripkeFrame::<4>::from_u16_id(*frame_id).number_of_worlds_validating(query)
            })
            .collect::<Vec<_>>();

        let query_name = format!("query_{}", query_idx);
        let table_name = format!("queryCountTable_{}", query_idx);
        let computed_name = format!("computedQueryCountTable_{}", query_idx);
        let count_fn_name = format!("queryCount_{}", query_idx);

        writeln!(
            output,
            "/-- Solver query {} actually used by the generated strategy. -/",
            query_idx
        )?;
        writeln!(
            output,
            "def {} : ModalFormula KripkeGameVars :=",
            query_name
        )?;
        writeln!(output, "  {}", formula_to_lean(query))?;
        writeln!(output)?;

        let query_chunk_count = emit_array_chunks(
            &mut output,
            &table_name,
            &counts,
            QUERY_TABLE_CHUNK_SIZE,
            32,
        )?;

        writeln!(
            output,
            "def {} : {{ table : Array Nat // table.size = canonicalFrameCount }} :=",
            table_name
        )?;
        writeln!(output, "  ⟨")?;
        for chunk_idx in 0..query_chunk_count {
            if chunk_idx == 0 {
                writeln!(output, "    {}_chunk_{}", table_name, chunk_idx)?;
            } else {
                writeln!(output, "    ++ {}_chunk_{}", table_name, chunk_idx)?;
            }
        }
        writeln!(output, "  , by native_decide")?;
        writeln!(output, "  ⟩")?;
        writeln!(output)?;

        writeln!(output, "private def {} : Array Nat :=", computed_name)?;
        writeln!(
            output,
            "  Array.ofFn (fun idx : Fin canonicalFrameCount => (FiniteKripkeFrame.ofFin (n := 4) (canonicalFrameId idx)).countSatisfyingNodes {})",
            query_name
        )?;
        writeln!(output)?;

        writeln!(
            output,
            "theorem {}_spec : {}.val = {} := by",
            table_name, table_name, computed_name
        )?;
        writeln!(output, "  native_decide")?;
        writeln!(output)?;

        writeln!(
            output,
            "theorem {}_eq_actual_at_index (idx : Fin canonicalFrameCount) :",
            table_name
        )?;
        writeln!(
            output,
            "    {}.val[idx]'(by simpa [{}.property] using idx.isLt) = (FiniteKripkeFrame.ofFin (n := 4) (canonicalFrameId idx)).countSatisfyingNodes {} := by",
            table_name, table_name, query_name
        )?;
        writeln!(
            output,
            "  have h := congrArg (fun arr => arr[idx]'(by simpa [Array.size_ofFn, {}] using idx.isLt)) {}_spec",
            computed_name, table_name
        )?;
        writeln!(output, "  simpa [{}] using h", computed_name)?;
        writeln!(output)?;

        writeln!(
            output,
            "def {} (frameId : Fin 65536) : Nat :=",
            count_fn_name
        )?;
        writeln!(output, "  let idx := canonicalFrameIndex frameId")?;
        writeln!(output, "  if h : idx < canonicalFrameCount then")?;
        writeln!(
            output,
            "    {}.val[⟨idx, h⟩]'(by simpa [{}.property] using h)",
            table_name, table_name
        )?;
        writeln!(output, "  else")?;
        writeln!(
            output,
            "    (FiniteKripkeFrame.ofFin (n := 4) frameId).countSatisfyingNodes {}",
            query_name
        )?;
        writeln!(output)?;

        writeln!(
            output,
            "theorem {}_eq_actual (frameId : Fin 65536) :",
            count_fn_name
        )?;
        writeln!(
            output,
            "    {} frameId = (FiniteKripkeFrame.ofFin (n := 4) frameId).countSatisfyingNodes {} := by",
            count_fn_name, query_name
        )?;
        writeln!(output, "  unfold {}", count_fn_name)?;
        writeln!(output, "  dsimp")?;
        writeln!(output, "  split <;> rename_i h")?;
        writeln!(
            output,
            "  · have hidx := {}_eq_actual_at_index ⟨canonicalFrameIndex frameId, h⟩",
            table_name
        )?;
        writeln!(
            output,
            "    rw [canonicalFrameId_of_canonicalFrameIndex frameId h] at hidx"
        )?;
        writeln!(output, "    simpa [canonicalFrameIndex, h] using hidx")?;
        writeln!(output, "  · simp [h, canonicalFrameIndex]")?;
        writeln!(output)?;
    }

    writeln!(
        output,
        "/-- Count satisfying nodes using precomputed tables for the queries used in the generated strategy. -/"
    )?;
    writeln!(
        output,
        "def precomputedCountSatisfyingNodes (frameId : Fin 65536) (query : ModalFormula KripkeGameVars) : Nat :="
    )?;
    for query_idx in 0..used_queries.len() {
        let prefix = if query_idx == 0 { "  if" } else { "  else if" };
        writeln!(
            output,
            "{} h_{} : query = query_{} then queryCount_{} frameId",
            prefix, query_idx, query_idx, query_idx
        )?;
    }
    writeln!(
        output,
        "  else (FiniteKripkeFrame.ofFin (n := 4) frameId).countSatisfyingNodes query"
    )?;
    writeln!(output)?;

    writeln!(
        output,
        "theorem precomputedCountSatisfyingNodes_eq_actual (frameId : Fin 65536) (query : ModalFormula KripkeGameVars) :"
    )?;
    writeln!(
        output,
        "    precomputedCountSatisfyingNodes frameId query = (FiniteKripkeFrame.ofFin (n := 4) frameId).countSatisfyingNodes query := by"
    )?;
    writeln!(output, "  unfold precomputedCountSatisfyingNodes")?;
    for query_idx in 0..used_queries.len() {
        writeln!(
            output,
            "  by_cases h_{} : query = query_{}",
            query_idx, query_idx
        )?;
        writeln!(
            output,
            "  · simp [h_{}, queryCount_{}_eq_actual]",
            query_idx, query_idx
        )?;
    }
    let all_hypotheses = (0..used_queries.len())
        .map(|query_idx| format!("h_{}", query_idx))
        .collect::<Vec<_>>()
        .join(", ");
    writeln!(output, "  · simp [{}]", all_hypotheses)?;
    writeln!(output)?;

    writeln!(output, "end KripkeGameAnalysis.Precomputed")?;

    eprintln!("Done.");
    Ok(())
}
