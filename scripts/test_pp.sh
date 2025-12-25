#!/bin/bash
# Test the Lean pretty-printer against Cerberus pretty-printer output
# Usage: ./scripts/test_pp.sh [--quick] [--verbose] [--max N] [test_dir]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
CERBERUS_DIR="$PROJECT_DIR/cerberus"
LEAN_DIR="$PROJECT_DIR/lean"
CERBERUS="$CERBERUS_DIR/_build/install/default/bin/cerberus"

# Configuration
QUICK_MODE=false
VERBOSE=false
TEST_DIR=""
MAX_TESTS=0  # 0 = unlimited
OUTPUT_DIR=$(mktemp -d "${TMPDIR:-/tmp}/c-to-lean-pp-test.XXXXXXXXXX")
ERROR_LOG="$OUTPUT_DIR/errors.log"
DIFF_LOG="$OUTPUT_DIR/diffs.log"

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --quick)
            QUICK_MODE=true
            MAX_TESTS=10
            shift
            ;;
        --verbose|-v)
            VERBOSE=true
            shift
            ;;
        --max)
            MAX_TESTS=$2
            shift 2
            ;;
        *)
            TEST_DIR="$1"
            shift
            ;;
    esac
done

# Default test directory - use CI tests for pretty-printer comparison
if [[ -z "$TEST_DIR" ]]; then
    TEST_DIR="$CERBERUS_DIR/tests/ci"
fi

# Check prerequisites
if [[ ! -x "$CERBERUS" ]]; then
    echo "Error: Cerberus not found at $CERBERUS"
    echo "Build it with: cd cerberus && make cerberus"
    exit 1
fi

# Build Lean pretty-printer
echo "Building Lean pretty-printer..."
cd "$LEAN_DIR"
lake build ctolean_pp 2>&1 | tail -5

# Create output directory
mkdir -p "$OUTPUT_DIR"
> "$ERROR_LOG"
> "$DIFF_LOG"

# Counters
total=0
cerberus_success=0
cerberus_fail=0
pp_match=0
pp_mismatch=0

# Find all .c files (excluding syntax-only tests)
echo ""
echo "Finding test files in $TEST_DIR..."
test_files=$(find "$TEST_DIR" -name "*.c" ! -name "*.syntax-only.c" | sort)
total_available=$(echo "$test_files" | wc -l | tr -d ' ')
echo "Found $total_available test files"

if [[ "$QUICK_MODE" == "true" ]]; then
    echo "Quick mode: testing first $MAX_TESTS files"
fi

echo ""
echo "Running pretty-printer comparison..."
echo "===================================="

start_time=$(date +%s)

# Process each file
while IFS= read -r cfile; do
    # Check max tests
    if [[ $MAX_TESTS -gt 0 && $total -ge $MAX_TESTS ]]; then
        break
    fi

    ((total++)) || true

    # Generate unique name for output
    basename=$(basename "$cfile" .c)
    hash=$(echo "$cfile" | md5 | cut -c1-8)
    json_file="$OUTPUT_DIR/${basename}_${hash}.json"
    cerberus_pp="$OUTPUT_DIR/${basename}_${hash}.cerberus.core"
    lean_pp="$OUTPUT_DIR/${basename}_${hash}.lean.core"

    if [[ "$VERBOSE" == "true" ]]; then
        echo -n "[$total] $basename ... "
    fi

    # Run Cerberus to generate JSON
    cerberus_err_file=$(mktemp)
    if ! "$CERBERUS" --json_core_out="$json_file" "$cfile" 2>"$cerberus_err_file"; then
        ((cerberus_fail++)) || true
        rm -f "$cerberus_err_file"
        if [[ "$VERBOSE" == "true" ]]; then
            echo "CERBERUS_FAIL"
        fi
        continue
    fi
    rm -f "$cerberus_err_file"

    # Run Cerberus to generate pretty-printed output (compact mode for easy comparison)
    if ! "$CERBERUS" --pp=core --pp_core_compact "$cfile" > "$cerberus_pp" 2>/dev/null; then
        ((cerberus_fail++)) || true
        if [[ "$VERBOSE" == "true" ]]; then
            echo "CERBERUS_PP_FAIL"
        fi
        continue
    fi

    ((cerberus_success++)) || true

    # Run Lean pretty-printer
    if ! "$LEAN_DIR/.lake/build/bin/ctolean_pp" "$json_file" > "$lean_pp" 2>/dev/null; then
        echo "$cfile: Lean pretty-printer failed" >> "$ERROR_LOG"
        if [[ "$VERBOSE" == "true" ]]; then
            echo "LEAN_PP_FAIL"
        fi
        continue
    fi

    # Compare outputs using the Lean comparison tool
    result=$("$LEAN_DIR/.lake/build/bin/ctolean_pp" "$json_file" --compare "$cerberus_pp" 2>&1) || true

    if echo "$result" | grep -q "^✓"; then
        ((pp_match++)) || true
        if [[ "$VERBOSE" == "true" ]]; then
            echo "✓ MATCH"
        fi
    else
        ((pp_mismatch++)) || true
        # Log the first difference
        diff_info=$(echo "$result" | grep "First difference" | head -1)
        echo "$basename: $diff_info" >> "$DIFF_LOG"
        if [[ "$VERBOSE" == "true" ]]; then
            echo "✗ MISMATCH"
            echo "$result" | grep -A2 "First difference" | head -3
        fi
    fi

done <<< "$test_files"

end_time=$(date +%s)
total_elapsed=$((end_time - start_time))

echo ""
echo ""
echo "===================================="
echo "Results Summary"
echo "===================================="
echo ""
echo "Total time:             ${total_elapsed}s"
echo ""
echo "Total files tested:     $total"
echo ""
echo "Cerberus stage:"
echo "  Success:              $cerberus_success"
echo "  Failed:               $cerberus_fail"
echo ""
echo "Pretty-printer comparison (of Cerberus successes):"
echo "  Match:                $pp_match"
echo "  Mismatch:             $pp_mismatch"
echo ""

if [[ $cerberus_success -gt 0 ]]; then
    match_rate=$((pp_match * 100 / cerberus_success))
    echo "Match rate:             ${match_rate}%"
fi

echo ""

# Show first few mismatches
if [[ -s "$DIFF_LOG" ]]; then
    echo "First differences found:"
    echo "------------------------"
    head -10 "$DIFF_LOG"
    echo ""
fi

echo "Output files saved to: $OUTPUT_DIR"
echo "  - JSON files: *.json"
echo "  - Cerberus output: *.cerberus.core"
echo "  - Lean output: *.lean.core"
echo "Diff log: $DIFF_LOG"

# Show how to investigate a mismatch
if [[ $pp_mismatch -gt 0 ]]; then
    first_mismatch=$(head -1 "$DIFF_LOG" | cut -d: -f1)
    echo ""
    echo "To investigate a mismatch, e.g. '$first_mismatch':"
    echo "  diff $OUTPUT_DIR/${first_mismatch}_*.cerberus.core $OUTPUT_DIR/${first_mismatch}_*.lean.core"
fi
