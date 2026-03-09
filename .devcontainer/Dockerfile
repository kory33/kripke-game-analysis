FROM mcr.microsoft.com/devcontainers/base:2-bookworm@sha256:23fa69fed758b7927c60061317d73baf7d66b9fca5c344e80bce3a940b229af0

ARG USERNAME=vscode

RUN apt-get update && apt-get install -y --no-install-recommends \
    dos2unix \
    ripgrep \
    && rm -rf /var/lib/apt/lists/*

# Used to persist bash history as per https://code.visualstudio.com/remote/advancedcontainers/persist-bash-history
RUN SNIPPET="export PROMPT_COMMAND='history -a' && export HISTFILE=/commandhistory/.bash_history" \
    && mkdir /commandhistory \
    && touch /commandhistory/.bash_history \
    && chown -R $USERNAME /commandhistory \
    && echo "$SNIPPET" >> "/home/$USERNAME/.bashrc"

# Install Codex
RUN wget https://github.com/openai/codex/releases/download/rust-v0.112.0/codex-x86_64-unknown-linux-musl.tar.gz -O /tmp/codex.tar.gz && \
  tar -xvf /tmp/codex.tar.gz -C /usr/local/bin/ && \
  rm /tmp/codex.tar.gz && \
  mv /usr/local/bin/codex-x86_64-unknown-linux-musl /usr/local/bin/codex && \
  chmod +x /usr/local/bin/codex

# Codex configuration files
RUN mkdir /home/$USERNAME/.codex && chown -R $USERNAME /home/$USERNAME/.codex

# Claude configuration files
RUN mkdir /home/$USERNAME/.claude && chown -R $USERNAME /home/$USERNAME/.claude
# Rust toolchain
RUN mkdir /home/$USERNAME/.rustup && chown -R $USERNAME /home/$USERNAME/.rustup
# Lean toolchain
RUN mkdir /home/$USERNAME/.elan && chown -R $USERNAME /home/$USERNAME/.elan
# uv (Python package manager) cache and local bin
RUN mkdir -p /home/$USERNAME/.cache/uv /home/$USERNAME/.local && chown -R $USERNAME /home/$USERNAME/.cache /home/$USERNAME/.local

# Use with caution.
# The devcontainer may contain Claude credentials so this is not entirely safe.
RUN echo "alias claude-yolo='claude --dangerously-skip-permissions'" >> /etc/bash.bashrc
RUN echo "alias codex-yolo='codex --dangerously-bypass-approvals-and-sandbox'" >> /etc/bash.bashrc
