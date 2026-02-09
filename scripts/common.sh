#!/bin/bash
# common.sh — shared helpers for all project scripts
#
# Usage: source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
#
# Provides:
#   PROJECT_ROOT, CERBERUS_DIR, LEAN_DIR, CERBERUS  — standard paths
#   RED, GREEN, YELLOW, NC                           — color codes (auto-detect TTY)
#   TMP_DIR                                          — project-local tmp directory
#   make_temp_dir PREFIX                             — create a temp directory under TMP_DIR
#   register_cleanup DIR                             — schedule DIR for removal on EXIT
#   build_lean TARGET                                — build a Lean target (idempotent)
#   require_cerberus                                 — check Cerberus prerequisites exist
#   portable_hash STRING                             — 8-char hash (works macOS + Linux)

# NOTE: This file does NOT set shell options (set -euo pipefail).
# Each script that sources this file should set its own shell options
# after the source line, since some scripts (e.g., creduce) need
# different error-handling behavior.

# ---------------------------------------------------------------------------
# Path resolution (works under symlinks)
# ---------------------------------------------------------------------------
# BASH_SOURCE[0] is common.sh itself; BASH_SOURCE[1] is the script that sourced us.
# But if common.sh is sourced at top level (not nested), BASH_SOURCE[1] may not exist.
# Use the caller's directory if available, otherwise fall back to our own.
if [[ ${#BASH_SOURCE[@]} -ge 2 ]]; then
    _CALLER_DIR="$(cd "$(dirname "${BASH_SOURCE[1]}")" && pwd)"
else
    _CALLER_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
fi
SCRIPT_DIR="$_CALLER_DIR"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CERBERUS_DIR="$PROJECT_ROOT/cerberus"
LEAN_DIR="$PROJECT_ROOT/lean"
CERBERUS="$PROJECT_ROOT/scripts/cerberus"
unset _CALLER_DIR

# ---------------------------------------------------------------------------
# Colors (auto-detect terminal)
# ---------------------------------------------------------------------------
if [[ -t 1 ]]; then
    RED='\033[0;31m'
    GREEN='\033[0;32m'
    YELLOW='\033[1;33m'
    NC='\033[0m'
else
    RED=''
    GREEN=''
    YELLOW=''
    NC=''
fi

# ---------------------------------------------------------------------------
# Temp directory management
# ---------------------------------------------------------------------------
TMP_DIR="$PROJECT_ROOT/tmp"
mkdir -p "$TMP_DIR"

# Create a temp directory under TMP_DIR.
# Usage: dir=$(make_temp_dir "my-prefix")
make_temp_dir() {
    local prefix="${1:-script}"
    mktemp -d "$TMP_DIR/${prefix}.XXXXXXXXXX"
}

# ---------------------------------------------------------------------------
# Cleanup on EXIT
# ---------------------------------------------------------------------------
_CLEANUP_PATHS=()

# Register a file or directory for automatic removal on script exit.
register_cleanup() {
    _CLEANUP_PATHS+=("$1")
}

_do_cleanup() {
    for p in ${_CLEANUP_PATHS[@]+"${_CLEANUP_PATHS[@]}"}; do
        rm -rf "$p"
    done
}
trap _do_cleanup EXIT

# ---------------------------------------------------------------------------
# Build helpers
# ---------------------------------------------------------------------------

# Build a Lean target (idempotent — lake build is incremental).
# Usage: build_lean cerblean_interp
build_lean() {
    local target="$1"
    echo "Building $target..."
    (cd "$LEAN_DIR" && lake build "$target" 2>&1 | tail -5)
}

# Check that the Cerberus opam switch exists.
require_cerberus() {
    if [[ ! -d "$CERBERUS_DIR/_opam" ]]; then
        echo "Error: Local opam switch not found at $CERBERUS_DIR/_opam" >&2
        echo "Run 'make cerberus-setup' first" >&2
        exit 1
    fi
}

# ---------------------------------------------------------------------------
# Portability helpers
# ---------------------------------------------------------------------------

# Produce an 8-character hash of a string (works on both macOS and Linux).
portable_hash() {
    if command -v md5sum &>/dev/null; then
        printf '%s' "$1" | md5sum | cut -c1-8
    else
        printf '%s' "$1" | md5 | cut -c1-8
    fi
}
