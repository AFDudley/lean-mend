# lean-mend commit-boundary gate image (exophial D49:
# exophial/docs/decisions/2026-10-14-gate-runs-in-a-container-built-from-the-judged-commit.md).
#
# exophial's gate_container.build_gate_image builds this file from a tar of
# the judged commit's tree (no .git, no .scratch). gate_container.run_in_container
# then runs `.exophial/config.yaml` gate.command (`scripts/gate.sh`) as the one
# process, with no bind mount and no -e. So every tool the gate calls is image
# content:
#   elan and the toolchains lean-mend supports  -> lake build, lake test, the probe matrix
#   jq                                         -> the probe matrix checks
#   git, bash                                  -> scripts/gate.sh
#
# The toolchain list must equal the default list in tests/probe-matrix.sh and
# lean-mend's own lean-toolchain. The layers before COPY do not depend on the
# judged tree, so docker reuses them between gate runs.
FROM debian:bookworm-slim

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates curl git jq bash zstd binutils \
    && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/root/.elan HOME=/root
ENV PATH="/root/.elan/bin:${PATH}"
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --no-modify-path --default-toolchain none \
    && elan toolchain install leanprover/lean4:v4.29.0 \
    && elan toolchain install leanprover/lean4:v4.33.1 \
    && elan toolchain install leanprover/lean4:v4.35.0

WORKDIR /gate
COPY . .

# No ENTRYPOINT: run_in_container passes gate.command, which runs in
# WORKDIR /gate with this image's PATH.
