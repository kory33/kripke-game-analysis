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

echo "=========================
Setting up Lean project...
========================="

# Update and fetch mathlib cache
cd /workspace/main-proofs && lake exe cache get

cat <<EOF

=========================
Setup complete!

You can now build the project with:
  cd /workspace/main-proofs && lake build

=========================
EOF
