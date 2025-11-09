#!/bin/bash
set -eux

# Install rustup + Rust toolchain
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain none
. "${HOME}/.cargo/env"
echo 'source "${HOME}/.cargo/env"' >> "${HOME}/.bashrc"
cd /workspace/solver && rustup show

# Install elan + Lean toolchain
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
source "${HOME}/.elan/env"
echo 'source "${HOME}/.elan/env"' >> "${HOME}/.bashrc"
cd /workspace/main-proofs && elan show

cat <<EOF
=========================

Setup complete! You can now use Rust and Lean.

We recommend downloading pre-built binaries for mathlib. To do so, run:

cd /workspace/main-proofs && lake update mathlib && lake exe cache get

=========================
EOF
