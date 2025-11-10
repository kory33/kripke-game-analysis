#!/usr/bin/env bash
set -euo pipefail

# Script to regenerate the Lean strategy certificate from the Rust solver

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Define paths relative to the script directory
SOLVER_DIR="${SCRIPT_DIR}/solver"
OUTPUT_PATH="${SCRIPT_DIR}/main-proofs/KripkeGameAnalysis/Game/Strategy/gen/Strategy.lean"

echo "Regenerating Lean strategy certificate..." >&2
echo "  Solver directory: ${SOLVER_DIR}" >&2
echo "  Output path: ${OUTPUT_PATH}" >&2
echo "" >&2

# Build and run the Rust binary, capturing stdout to the output file
cd "${SOLVER_DIR}"
cargo run --bin emit_lean_strategy --release > "${OUTPUT_PATH}"

echo "" >&2
echo "Successfully regenerated strategy certificate at:" >&2
echo "  ${OUTPUT_PATH}" >&2
