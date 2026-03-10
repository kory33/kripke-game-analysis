#!/usr/bin/env bash
set -euo pipefail

# Script to regenerate generated Lean strategy artifacts from the Rust solver

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Define paths relative to the script directory
SOLVER_DIR="${SCRIPT_DIR}/solver"
GEN_DIR="${SCRIPT_DIR}/main-proofs/KripkeGameAnalysis/Game/Strategy/gen"
STRATEGY_OUTPUT_PATH="${GEN_DIR}/Strategy.lean"
FRAME_SETS_OUTPUT_PATH="${GEN_DIR}/PrecomputedFrameSets.lean"
VALUATION_TABLES_OUTPUT_PATH="${GEN_DIR}/ValuationTruthTables.lean"
CERTIFICATES_OUTPUT_DIR="${GEN_DIR}/StrategyCertificates"

echo "Regenerating generated Lean strategy artifacts..." >&2
echo "  Solver directory: ${SOLVER_DIR}" >&2
echo "  Strategy output path: ${STRATEGY_OUTPUT_PATH}" >&2
echo "  Frame sets output path: ${FRAME_SETS_OUTPUT_PATH}" >&2
echo "  Valuation tables output path: ${VALUATION_TABLES_OUTPUT_PATH}" >&2
echo "  Certificates output dir: ${CERTIFICATES_OUTPUT_DIR}" >&2
echo "" >&2

# Build and run the Rust binaries, capturing stdout to the output files
cd "${SOLVER_DIR}"
cargo run --bin emit_lean_strategy --release > "${STRATEGY_OUTPUT_PATH}"
cargo run --bin emit_precomputed_frame_sets --release > "${FRAME_SETS_OUTPUT_PATH}"
cargo run --bin emit_valuation_truth_tables --release > "${VALUATION_TABLES_OUTPUT_PATH}"
cargo run --bin emit_strategy_certificates --release -- "${CERTIFICATES_OUTPUT_DIR}"

echo "" >&2
echo "Successfully regenerated generated Lean artifacts at:" >&2
echo "  ${STRATEGY_OUTPUT_PATH}" >&2
echo "  ${FRAME_SETS_OUTPUT_PATH}" >&2
echo "  ${VALUATION_TABLES_OUTPUT_PATH}" >&2
echo "  ${CERTIFICATES_OUTPUT_DIR}" >&2
