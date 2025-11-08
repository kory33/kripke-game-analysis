FROM mcr.microsoft.com/devcontainers/base:bookworm

ARG USERNAME=vscode

RUN apt-get update && apt-get install -y --no-install-recommends \
    dos2unix \
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

# Use with caution.
# The devcontainer may contain Claude credentials so this is not entirely safe.
RUN echo "alias claude-yolo='claude --dangerously-skip-permissions'" >> /etc/bash.bashrc
