#!/bin/bash
# Fuzz testing with csmith - generates random tests and finds mismatches
#
# Usage: ./scripts/fuzz_csmith.sh [num_tests] [output_dir]
#
# Generates random csmith tests, runs them through test_interp.sh,
# and saves any mismatches for investigation.

set -e

NUM_TESTS="${1:-100}"
OUTPUT_DIR="${2:-tests/csmith/fuzz_results}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Ensure output directory exists
mkdir -p "$OUTPUT_DIR"
TEMP_DIR=$(mktemp -d)
trap "rm -rf $TEMP_DIR" EXIT

# Check dependencies
if ! command -v csmith &> /dev/null; then
    echo "Error: csmith not found. Install with: brew install csmith" >&2
    exit 1
fi

echo "Generating $NUM_TESTS random csmith tests in $TEMP_DIR..."

# Generate all tests first
for i in $(seq 1 $NUM_TESTS); do
    seed=$RANDOM$RANDOM
    outfile="$TEMP_DIR/csmith_${seed}.c"

    csmith \
        --no-argc \
        --no-bitfields \
        --seed "$seed" \
        --max-funcs 3 \
        --max-block-depth 3 \
        --max-block-size 4 \
        --max-expr-complexity 3 \
        2>/dev/null | sed 's|#include "csmith.h"|#define CSMITH_MINIMAL\
#include "csmith_cerberus.h"|' > "$outfile"

    printf "\rGenerated %d/%d tests" "$i" "$NUM_TESTS"
done
echo ""

# Copy our csmith header to temp dir so includes work
cp "$PROJECT_DIR/tests/csmith/csmith_cerberus.h" "$TEMP_DIR/"
cp "$PROJECT_DIR/tests/csmith/safe_math.h" "$TEMP_DIR/"

# Run test_interp.sh on all generated tests
echo ""
echo "Running interpreter comparison..."
"$SCRIPT_DIR/test_interp.sh" "$TEMP_DIR" 2>&1 | tee "$OUTPUT_DIR/fuzz_log.txt"

# Extract and save any failures or interesting differences
echo ""
echo "Checking for failures and mismatches..."
# FAIL = interpreter error, MISMATCH = different concrete values, DIFF = semantic difference (e.g., Unspecified)
grep -E "^(FAIL|MISMATCH|DIFF)" "$OUTPUT_DIR/fuzz_log.txt" 2>/dev/null | while read line; do
    # Extract filename from the failure line
    testname=$(echo "$line" | awk '{print $2}' | sed 's/://')
    if [ -f "$TEMP_DIR/${testname}.c" ]; then
        cp "$TEMP_DIR/${testname}.c" "$OUTPUT_DIR/"
        echo "Saved: $OUTPUT_DIR/${testname}.c"
    fi
done

echo ""
echo "Results saved to: $OUTPUT_DIR/"
echo "Log file: $OUTPUT_DIR/fuzz_log.txt"
