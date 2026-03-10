#!/usr/bin/env bash
set -euo pipefail

# Script to regenerate the Lean strategy certificate from the Rust solver

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Define paths relative to the script directory
SOLVER_DIR="${SCRIPT_DIR}/solver"
OUTPUT_PATH="${SCRIPT_DIR}/main-proofs/KripkeGameAnalysis/Game/Strategy/gen/Strategy.lean"
QUERY_COUNTS_OUTPUT_PATH="${SCRIPT_DIR}/main-proofs/KripkeGameAnalysis/Game/Strategy/gen/PrecomputedQueryCounts.lean"

echo "Regenerating Lean strategy certificate..." >&2
echo "  Solver directory: ${SOLVER_DIR}" >&2
echo "  Output path: ${OUTPUT_PATH}" >&2
echo "  Query counts output path: ${QUERY_COUNTS_OUTPUT_PATH}" >&2
echo "" >&2

# Build and run the Rust binaries, capturing stdout to the output files
cd "${SOLVER_DIR}"
cargo run --bin emit_lean_strategy --release > "${OUTPUT_PATH}"
cargo run --bin emit_precomputed_query_counts --release > "${QUERY_COUNTS_OUTPUT_PATH}"

echo "" >&2
echo "Successfully regenerated generated Lean artifacts at:" >&2
echo "  ${OUTPUT_PATH}" >&2
echo "  ${QUERY_COUNTS_OUTPUT_PATH}" >&2
