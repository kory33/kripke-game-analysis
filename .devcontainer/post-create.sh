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

echo "=========================
Installing uv (Python package manager)...
========================="

# Install uv for MCP server
curl -LsSf https://astral.sh/uv/install.sh | sh
export PATH="${HOME}/.local/bin:${PATH}"
echo 'export PATH="${HOME}/.local/bin:${PATH}"' >> "${HOME}/.bashrc"

echo "=========================
Pre-caching lean-lsp-mcp server...
========================="

# Pre-download lean-lsp-mcp from PyPI (uvx will cache it)
# This makes the first MCP run faster
"${HOME}/.local/bin/uvx" --version > /dev/null 2>&1 || true
"${HOME}/.local/bin/uvx" lean-lsp-mcp --help > /dev/null 2>&1 || true

cat <<EOF

=========================
Setup complete!

You can now build the project with:
  cd /workspace/main-proofs && lake build

lean-lsp-mcp server is configured and ready to use!
Configuration: /workspace/.mcp.json
To test it: uvx lean-lsp-mcp --help

=========================
EOF
