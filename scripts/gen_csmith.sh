#!/bin/bash
# Generate a csmith test suitable for our interpreter
#
# Usage: ./scripts/gen_csmith.sh [--help] [seed] [output_file]
#
# The generated test:
# - Uses --no-argc (we don't support argc/argv yet)
# - Includes our csmith_cerberus.h header which exits with checksum
# - Can be run with ./scripts/test_interp.sh

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
set -euo pipefail

usage() {
    cat <<'EOF'
Generate a csmith test suitable for our interpreter.

Usage: ./scripts/gen_csmith.sh [options] [seed] [output_file]

Arguments:
  seed          Random seed for reproducibility (default: random)
  output_file   Output path (default: tests/csmith/generated_<seed>.c)

Options:
  -h, --help    Show this help message

The generated test uses --no-argc and --no-bitfields, and replaces
csmith.h with our csmith_cerberus.h header.

Examples:
  ./scripts/gen_csmith.sh
  ./scripts/gen_csmith.sh 12345
  ./scripts/gen_csmith.sh 12345 tests/csmith/debug.c
EOF
    exit 0
}

# Parse arguments
SEED=""
OUTPUT=""
while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help) usage ;;
        -*)
            echo "Unknown option: $1" >&2
            echo "Use --help for usage information" >&2
            exit 1
            ;;
        *)
            if [[ -z "$SEED" ]]; then
                SEED="$1"
            elif [[ -z "$OUTPUT" ]]; then
                OUTPUT="$1"
            else
                echo "Error: Too many arguments" >&2
                usage
            fi
            shift
            ;;
    esac
done

SEED="${SEED:-$RANDOM}"
OUTPUT="${OUTPUT:-tests/csmith/generated_${SEED}.c}"

# Check if csmith is available
if ! command -v csmith &>/dev/null; then
    echo "Error: csmith not found. Install with: brew install csmith" >&2
    exit 1
fi

# Generate the test with our preferred options
TMP_FILE=$(mktemp "$TMP_DIR/gen_csmith.XXXXXXXXXX")
register_cleanup "$TMP_FILE"

csmith \
    --no-argc \
    --no-bitfields \
    --seed "$SEED" \
    --max-funcs 3 \
    --max-block-depth 3 \
    --max-block-size 4 \
    --max-expr-complexity 3 \
    > "$TMP_FILE"

# Replace the csmith.h include with our header
sed 's|#include "csmith.h"|#define CSMITH_MINIMAL\
#include "csmith_cerberus.h"|' "$TMP_FILE" > "$OUTPUT"

echo "Generated: $OUTPUT (seed: $SEED)"
echo "Run with: ./scripts/test_interp.sh $OUTPUT"
