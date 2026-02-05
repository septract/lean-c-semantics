#!/bin/bash
# Docker entrypoint for CerbLean
# Executes a C program through Cerberus → Lean pipeline
#
# Usage:
#   cerblean [options] <file.c>
#   cerblean --help
#
# Options:
#   --batch       Output machine-readable result format
#   --nolibc      Skip libc linking (faster, but fewer programs work)
#   --cerberus    Run Cerberus only (skip Lean interpreter)
#   --json        Output Core IR as JSON (for debugging)
#   --help        Show this help message

set -e

# Cerberus is installed via opam, available in PATH
CERBERUS="cerberus"
LEAN_INTERP="/opt/cerblean/cerblean_interp"

# Default options
BATCH_MODE=false
NO_LIBC=false
CERBERUS_ONLY=false
JSON_OUTPUT=false
INPUT_FILE=""

show_help() {
    cat << 'EOF'
CerbLean - C semantics via Cerberus and Lean

Usage:
  cerblean [options] <file.c>

Options:
  --batch       Output machine-readable result format
  --nolibc      Skip libc linking (faster, but fewer programs work)
  --cerberus    Run Cerberus execution only (skip Lean interpreter)
  --json        Output Core IR as JSON instead of executing
  --help        Show this help message

Examples:
  # Execute a C program with the Lean interpreter
  cerblean program.c

  # Execute with batch output (for scripting)
  cerblean --batch program.c

  # Just run Cerberus (compare results)
  cerblean --cerberus program.c

  # Get Core IR as JSON
  cerblean --json program.c > core.json

EOF
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --batch)
            BATCH_MODE=true
            shift
            ;;
        --nolibc)
            NO_LIBC=true
            shift
            ;;
        --cerberus)
            CERBERUS_ONLY=true
            shift
            ;;
        --json)
            JSON_OUTPUT=true
            shift
            ;;
        --help|-h)
            show_help
            exit 0
            ;;
        -*)
            echo "Unknown option: $1" >&2
            echo "Use --help for usage information" >&2
            exit 1
            ;;
        *)
            if [[ -n "$INPUT_FILE" ]]; then
                echo "Error: Multiple input files not supported" >&2
                exit 1
            fi
            INPUT_FILE="$1"
            shift
            ;;
    esac
done

# Validate input
if [[ -z "$INPUT_FILE" ]]; then
    echo "Error: No input file specified" >&2
    echo "Use --help for usage information" >&2
    exit 1
fi

if [[ ! -f "$INPUT_FILE" ]]; then
    echo "Error: File not found: $INPUT_FILE" >&2
    exit 1
fi

# Build Cerberus flags
CERBERUS_FLAGS="--sequentialise"
if $NO_LIBC; then
    CERBERUS_FLAGS="$CERBERUS_FLAGS --nolibc"
fi

# Mode: JSON output
if $JSON_OUTPUT; then
    exec $CERBERUS $CERBERUS_FLAGS --json_core_out=/dev/stdout "$INPUT_FILE"
fi

# Mode: Cerberus only
if $CERBERUS_ONLY; then
    if $BATCH_MODE; then
        exec $CERBERUS $CERBERUS_FLAGS --exec --batch "$INPUT_FILE"
    else
        exec $CERBERUS $CERBERUS_FLAGS --exec "$INPUT_FILE"
    fi
fi

# Mode: Full pipeline (Cerberus → Lean)
# Create temporary file for JSON
JSON_FILE=$(mktemp "${TMPDIR:-/tmp}/cerblean.XXXXXX.json")
trap "rm -f $JSON_FILE" EXIT

# Generate Core IR JSON
if ! $CERBERUS $CERBERUS_FLAGS --json_core_out="$JSON_FILE" "$INPUT_FILE" 2>&1; then
    echo "Error: Cerberus failed to process $INPUT_FILE" >&2
    exit 1
fi

# Run Lean interpreter
if $BATCH_MODE; then
    exec $LEAN_INTERP --batch "$JSON_FILE"
else
    exec $LEAN_INTERP "$JSON_FILE"
fi
