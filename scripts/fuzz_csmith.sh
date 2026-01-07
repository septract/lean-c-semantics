#!/bin/bash
# Fuzz testing with csmith - generates random tests and finds bugs
#
# Usage: ./scripts/fuzz_csmith.sh [num_tests] [output_dir]
#
# Generates random csmith tests, runs them through test_interp.sh,
# and saves any bugs for investigation.
#
# Output categories (all differences are BUGS):
#   FAIL     = Lean interpreter error (BUG)
#   MISMATCH = Different concrete values (BUG)
#   DIFF     = One returned UB, other didn't (BUG)
#   TIMEOUT  = Lean took too long (may need more fuel)

set -e

NUM_TESTS="${1:-100}"
OUTPUT_DIR="${2:-tests/csmith/fuzz_results}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Ensure output directories exist
mkdir -p "$OUTPUT_DIR"
mkdir -p "$OUTPUT_DIR/bugs"      # FAIL, MISMATCH, DIFF - any difference is a BUG
mkdir -p "$OUTPUT_DIR/timeouts"  # TIMEOUT cases (may need more fuel)

TEMP_DIR=$(mktemp -d)
# Don't auto-cleanup - we need to save interesting cases
cleanup() {
    # Only cleanup temp dir after we've saved interesting cases
    rm -rf "$TEMP_DIR"
}

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

# Extract and save interesting cases
echo ""
echo "Checking for failures and mismatches..."

# Count saved cases
BUGS_SAVED=0
TIMEOUTS_SAVED=0

# Process each line from the log
# Format: [N/M] STATUS filename: details
while IFS= read -r line; do
    # Extract testname from format: [N/M] STATUS testname: details
    if [[ "$line" =~ \[.*\]\ (FAIL|MISMATCH|DIFF)\ ([^:]+) ]]; then
        # FAIL, MISMATCH, or DIFF = BUG (any difference from Cerberus is a bug)
        testname="${BASH_REMATCH[2]}"
        if [ -f "$TEMP_DIR/${testname}.c" ]; then
            cp "$TEMP_DIR/${testname}.c" "$OUTPUT_DIR/bugs/"
            echo "BUG FOUND: $OUTPUT_DIR/bugs/${testname}.c"
            echo "  $line"
            ((BUGS_SAVED++))
        fi
    elif [[ "$line" =~ \[.*\]\ TIMEOUT\ ([^\ ]+) ]]; then
        # TIMEOUT
        testname="${BASH_REMATCH[1]}"
        if [ -f "$TEMP_DIR/${testname}.c" ]; then
            cp "$TEMP_DIR/${testname}.c" "$OUTPUT_DIR/timeouts/"
            echo "Timeout: $OUTPUT_DIR/timeouts/${testname}.c"
            ((TIMEOUTS_SAVED++))
        fi
    fi
done < "$OUTPUT_DIR/fuzz_log.txt"

# Cleanup temp directory now that we've saved everything
cleanup

echo ""
echo "================================="
echo "Saved Cases Summary"
echo "================================="
echo "  Bugs (FAIL/MISMATCH/DIFF): $BUGS_SAVED  -> $OUTPUT_DIR/bugs/"
echo "  Timeouts:                  $TIMEOUTS_SAVED  -> $OUTPUT_DIR/timeouts/"
echo ""
echo "Log file: $OUTPUT_DIR/fuzz_log.txt"

if [ $BUGS_SAVED -gt 0 ]; then
    echo ""
    echo "*** BUGS FOUND! Check $OUTPUT_DIR/bugs/ ***"
    exit 1
fi
