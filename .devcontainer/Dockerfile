FROM mcr.microsoft.com/devcontainers/base:2-bookworm@sha256:15143a8c806afb8db57ae2c92876c112d7a6a1ced31cd7aa8b414201782757a4

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
