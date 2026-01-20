# Multi-stage Dockerfile for CerbLean
# Builds Cerberus (C frontend) and Lean interpreter into a single image
#
# Layer caching strategy:
# - Dependencies are installed before source code is copied
# - Source changes don't invalidate dependency layers

# =============================================================================
# Stage 1: Build Cerberus
# =============================================================================
FROM ubuntu:24.04 AS cerberus-builder

ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN apt-get update && apt-get install -y \
    build-essential \
    libgmp-dev \
    pkg-config \
    opam \
    git \
    && rm -rf /var/lib/apt/lists/*

# Initialize opam without sandboxing (required in Docker)
RUN opam init --disable-sandboxing --yes

WORKDIR /opt/cerberus

# Copy only opam files first to cache dependency installation
COPY cerberus/*.opam cerberus/dune-project ./

# Install dependencies (cached unless opam files change)
RUN opam pin add -n --yes cerberus-lib . && \
    opam pin add -n --yes cerberus . && \
    opam install --yes --deps-only cerberus-lib cerberus

# Now copy full source and build
COPY cerberus /opt/cerberus
RUN opam install --yes cerberus && \
    opam clean --yes --download-cache --logs --repo-cache

# =============================================================================
# Stage 2: Build Lean
# =============================================================================
FROM ubuntu:24.04 AS lean-builder

ENV DEBIAN_FRONTEND=noninteractive

# Install dependencies for elan/lean
RUN apt-get update && apt-get install -y \
    curl \
    git \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | \
    sh -s -- -y --default-toolchain none

ENV PATH="/root/.elan/bin:${PATH}"

WORKDIR /opt/lean

# Copy toolchain file first to cache toolchain download
COPY lean/lean-toolchain ./

# Download toolchain (cached unless lean-toolchain changes)
RUN elan toolchain install $(cat lean-toolchain)

# Copy build config (cached layer for project structure)
COPY lean/lakefile.toml lean/lake-manifest.json ./

# Copy source and build
COPY lean /opt/lean
RUN lake build cerblean_interp

# =============================================================================
# Stage 3: Runtime image
# =============================================================================
FROM ubuntu:24.04 AS runtime

ENV DEBIAN_FRONTEND=noninteractive

# Install runtime dependencies
# - libgmp10: required by OCaml
# - gcc: required by Cerberus for C preprocessing
RUN apt-get update && apt-get install -y \
    libgmp10 \
    gcc \
    && rm -rf /var/lib/apt/lists/*

# Copy entire opam environment from cerberus-builder
# (includes cerberus binary, runtime, and all OCaml deps)
COPY --from=cerberus-builder /root/.opam /root/.opam

# Copy Lean interpreter binary
COPY --from=lean-builder /opt/lean/.lake/build/bin/cerblean_interp /opt/cerblean/cerblean_interp

# Copy entrypoint script
COPY scripts/docker_entrypoint.sh /opt/cerblean/entrypoint.sh
RUN chmod +x /opt/cerblean/entrypoint.sh

# Set up opam environment (required for Cerberus to find runtime)
ENV OPAM_SWITCH_PREFIX="/root/.opam/default"
ENV CAML_LD_LIBRARY_PATH="/root/.opam/default/lib/stublibs:/root/.opam/default/lib/ocaml/stublibs:/root/.opam/default/lib/ocaml"
ENV PATH="/root/.opam/default/bin:/opt/cerblean:${PATH}"

# Set working directory for user files
WORKDIR /work

ENTRYPOINT ["/opt/cerblean/entrypoint.sh"]
CMD ["--help"]
