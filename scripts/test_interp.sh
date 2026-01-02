#!/bin/bash
# Test the Lean interpreter against Cerberus execution
# Usage: ./scripts/test_interp.sh [--verbose] [--max N] [test_dir]
#
# If test_dir is the Cerberus CI directory, uses their tests.sh for the file list.
# Otherwise, tests all *.c files in the directory.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
CERBERUS_DIR="$PROJECT_DIR/cerberus"
LEAN_DIR="$PROJECT_DIR/lean"

# Cerberus requires OCaml 4.14.1
OPAM_SWITCH="cerberus-414"
CERBERUS="$PROJECT_DIR/scripts/cerberus"

# Configuration
VERBOSE=false
TEST_DIR=""
MAX_TESTS=0  # 0 = unlimited
OUTPUT_DIR=$(mktemp -d "${TMPDIR:-/tmp}/c-to-lean-interp-test.XXXXXXXXXX")

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
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

# Default test directory
if [[ -z "$TEST_DIR" ]]; then
    TEST_DIR="$CERBERUS_DIR/tests/ci"
fi

# Resolve to absolute path
TEST_DIR="$(cd "$TEST_DIR" && pwd)"

# Build Lean interpreter
echo "Building Lean interpreter..."
cd "$LEAN_DIR"
lake build ctolean_interp 2>&1 | tail -3
LEAN_INTERP="$LEAN_DIR/.lake/build/bin/ctolean_interp"

# Get test files
echo ""
if [[ "$TEST_DIR" == "$CERBERUS_DIR/tests/ci" ]]; then
    # Use Cerberus's tests.sh for the official CI test list
    echo "Loading test list from Cerberus tests.sh..."
    source "$CERBERUS_DIR/tests/tests.sh"
    TEST_FILES=""
    for f in "${citests[@]}"; do
        # Skip syntax-only tests (not semantically well-formed for execution)
        # Skip exhaust tests (require exhaustive exploration of interleavings)
        if [[ $f == *.syntax-only.c ]] || [[ $f == *.exhaust.c ]]; then
            continue
        fi
        TEST_FILES="$TEST_FILES $TEST_DIR/$f"
    done
else
    # Test all .c files in the directory
    echo "Testing all .c files in $TEST_DIR..."
    TEST_FILES=$(find "$TEST_DIR" -maxdepth 1 -name "*.c" | sort)
fi

TOTAL_FILES=$(echo $TEST_FILES | wc -w | tr -d ' ')
echo "Found $TOTAL_FILES test files"

if [[ $MAX_TESTS -gt 0 ]]; then
    echo "Testing first $MAX_TESTS files"
    TEST_FILES=$(echo $TEST_FILES | tr ' ' '\n' | head -n $MAX_TESTS | tr '\n' ' ')
fi

# Timeout for Lean interpreter (seconds)
LEAN_TIMEOUT=5

# Counters
CERBERUS_OK=0
CERBERUS_FAIL=0
LEAN_OK=0
LEAN_FAIL=0
LEAN_TIMEOUT_COUNT=0
MATCH=0
MISMATCH=0

echo ""
echo "Running interpreter comparison..."
echo "================================="

file_num=0
total_to_test=$(echo $TEST_FILES | wc -w | tr -d ' ')

for c_file in $TEST_FILES; do
    filename=$(basename "$c_file" .c)
    file_num=$((file_num + 1))

    # Show progress
    if ! $VERBOSE; then
        printf "\r[%d/%d] %s...                    " "$file_num" "$total_to_test" "$filename"
    fi

    # Run Cerberus to get exit code
    cerberus_exit=0
    eval $CERBERUS --exec "$c_file" >/dev/null 2>&1 || cerberus_exit=$?

    if [[ $cerberus_exit -eq 139 ]] || [[ $cerberus_exit -eq 134 ]] || [[ $cerberus_exit -eq 137 ]]; then
        # Cerberus crashed (SIGSEGV, SIGABRT, etc.) - skip
        ((CERBERUS_FAIL++))
        if $VERBOSE; then
            echo "SKIP $filename (Cerberus crashed with $cerberus_exit)"
        fi
        continue
    fi
    ((CERBERUS_OK++))

    # Generate JSON for Lean
    json_file="$OUTPUT_DIR/$filename.json"
    if ! eval $CERBERUS --json_core_out="$json_file" "$c_file" >/dev/null 2>&1; then
        if $VERBOSE; then
            echo "SKIP $filename (JSON generation failed)"
        fi
        continue
    fi

    # Run Lean interpreter with timeout
    lean_exit=0
    lean_output=$(timeout ${LEAN_TIMEOUT}s "$LEAN_INTERP" "$json_file" 2>&1) || lean_exit=$?

    # Check for timeout (exit code 124)
    if [[ $lean_exit -eq 124 ]]; then
        ((LEAN_TIMEOUT_COUNT++))
        if $VERBOSE; then
            echo "TIMEOUT $filename (>${LEAN_TIMEOUT}s)"
        else
            echo ""
            echo "TIMEOUT $filename (>${LEAN_TIMEOUT}s)"
        fi
        continue
    fi

    # Extract Lean return value
    lean_ret=""
    if echo "$lean_output" | grep -q "Return value:"; then
        lean_ret=$(echo "$lean_output" | grep "Return value:" | sed 's/Return value: //')
    elif echo "$lean_output" | grep -q "Error:"; then
        lean_ret="ERROR"
        ((LEAN_FAIL++))
        error_msg=$(echo "$lean_output" | grep "Error:" | head -1)
        if ! $VERBOSE; then
            echo ""
        fi
        echo "FAIL $filename: $error_msg"
        continue
    fi
    ((LEAN_OK++))

    # Compare results
    if [[ "$lean_ret" == "$cerberus_exit" ]]; then
        ((MATCH++))
        if $VERBOSE; then
            echo "OK   $filename: $lean_ret"
        fi
    else
        ((MISMATCH++))
        if ! $VERBOSE; then
            echo ""
        fi
        echo "DIFF $filename: Lean=$lean_ret Cerberus=$cerberus_exit"
    fi
done

# Clear progress line
if ! $VERBOSE; then
    printf "\r                                                            \r"
fi

echo ""
echo "================================="
echo "Results Summary"
echo "================================="
echo ""
echo "Cerberus execution:"
echo "  Success:    $CERBERUS_OK"
echo "  Failed:     $CERBERUS_FAIL"
echo ""
echo "Lean interpreter (of Cerberus successes):"
echo "  Success:    $LEAN_OK"
echo "  Failed:     $LEAN_FAIL"
echo "  Timeout:    $LEAN_TIMEOUT_COUNT"
echo ""
echo "Comparison (of both successes):"
echo "  Match:      $MATCH"
echo "  Mismatch:   $MISMATCH"
echo ""

if [[ $((MATCH + MISMATCH)) -gt 0 ]]; then
    MATCH_RATE=$((MATCH * 100 / (MATCH + MISMATCH)))
    echo "Match rate:   ${MATCH_RATE}%"
fi

echo ""
echo "Output files saved to: $OUTPUT_DIR"
