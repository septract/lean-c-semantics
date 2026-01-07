#!/bin/bash
# Generate a csmith test suitable for our interpreter
#
# Usage: ./scripts/gen_csmith_test.sh [seed] [output_file]
#
# The generated test:
# - Uses --no-argc (we don't support argc/argv yet)
# - Includes our csmith_cerberus.h header which exits with checksum
# - Can be run with ./scripts/test_interp.sh

set -e

SEED="${1:-$RANDOM}"
OUTPUT="${2:-tests/csmith/generated_${SEED}.c}"

# Check if csmith is available
if ! command -v csmith &> /dev/null; then
    echo "Error: csmith not found. Install with: brew install csmith" >&2
    exit 1
fi

# Generate the test with our preferred options
# Key options:
#   --no-argc: We don't support argc/argv yet
#   --no-bitfields: Cerberus doesn't support bit-fields
#   --no-float: Avoid floating point edge cases (optional)
#   --max-funcs 3: Keep tests reasonably small
#   --max-block-depth 3: Limit nesting
#   --seed: For reproducibility
csmith \
    --no-argc \
    --no-bitfields \
    --seed "$SEED" \
    --max-funcs 3 \
    --max-block-depth 3 \
    --max-block-size 4 \
    --max-expr-complexity 3 \
    > "$OUTPUT.tmp"

# Replace the csmith.h include with our header
sed 's|#include "csmith.h"|#define CSMITH_MINIMAL\n#include "csmith_cerberus.h"|' "$OUTPUT.tmp" > "$OUTPUT"
rm "$OUTPUT.tmp"

echo "Generated: $OUTPUT (seed: $SEED)"
echo "Run with: ./scripts/test_interp.sh $OUTPUT"
