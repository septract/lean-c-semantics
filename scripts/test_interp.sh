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
    # Test all .c files in the directory (recursively)
    # Skip directories that require special modes or memory models:
    #   bmc/        - Bounded model checking (requires --bmc mode)
    #   cheri-ci/   - CHERI memory model tests
    #   pnvi_testsuite/ - PNVI provenance tests
    echo "Testing all .c files in $TEST_DIR..."
    TEST_FILES=$(find "$TEST_DIR" -name "*.c" \
        ! -name "*.syntax-only.c" \
        ! -name "*.exhaust.c" \
        ! -path "*/bmc/*" \
        ! -path "*/cheri-ci/*" \
        ! -path "*/pnvi_testsuite/*" \
        | sort)
fi

TOTAL_FILES=$(echo $TEST_FILES | wc -w | tr -d ' ')
echo "Found $TOTAL_FILES test files"

if [[ $MAX_TESTS -gt 0 ]]; then
    echo "Testing first $MAX_TESTS files"
    TEST_FILES=$(echo $TEST_FILES | tr ' ' '\n' | head -n $MAX_TESTS | tr '\n' ' ')
fi

# Timeout for interpreters (seconds)
TIMEOUT_SECS=10

# Counters
CERBERUS_OK=0
CERBERUS_FAIL=0
LEAN_OK=0
LEAN_FAIL=0
LEAN_TIMEOUT_COUNT=0
MATCH=0
MISMATCH=0
UB_MATCH=0      # Both detected UB with same code
UB_CODE_DIFF=0  # Both detected UB but different codes (not a failure)

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

    # Run Cerberus in batch mode to get return value (not shell exit code)
    cerberus_shell_exit=0
    cerberus_output=$(timeout ${TIMEOUT_SECS}s $CERBERUS --exec --batch "$c_file" 2>&1) || cerberus_shell_exit=$?

    # Check for timeout
    if [[ $cerberus_shell_exit -eq 124 ]]; then
        ((CERBERUS_FAIL++))
        if $VERBOSE; then
            echo "SKIP $filename (Cerberus timeout)"
        fi
        continue
    fi
    cerberus_has_ub=false
    cerberus_ret=""

    if echo "$cerberus_output" | grep -q "undefined behaviour"; then
        cerberus_has_ub=true
    fi

    if [[ $cerberus_shell_exit -eq 139 ]] || [[ $cerberus_shell_exit -eq 134 ]] || [[ $cerberus_shell_exit -eq 137 ]]; then
        # Cerberus crashed (SIGSEGV, SIGABRT, etc.) - skip
        ((CERBERUS_FAIL++))
        if $VERBOSE; then
            echo "SKIP $filename (Cerberus crashed with $cerberus_shell_exit)"
        fi
        continue
    fi

    # Extract return value from batch output: Defined {value: "Specified(N)", ...}
    # or detect UB: Undefined {ub: "CODE", ...}
    # or error: Error {msg: "..."}
    cerberus_ub_code=""
    if echo "$cerberus_output" | grep -q '^Undefined {'; then
        cerberus_has_ub=true
        cerberus_ub_code=$(echo "$cerberus_output" | grep -o 'ub: "[^"]*"' | sed 's/ub: "\([^"]*\)"/\1/')
        cerberus_ret="UB"
    elif echo "$cerberus_output" | grep -q 'value: "Specified'; then
        cerberus_ret=$(echo "$cerberus_output" | grep -o 'value: "Specified([^)]*)"' | sed 's/value: "Specified(\([^)]*\))"/\1/')
    elif echo "$cerberus_output" | grep -q 'value: "Unspecified'; then
        cerberus_ret="UNSPECIFIED"
    elif echo "$cerberus_output" | grep -q '^Error {'; then
        # Cerberus reported an error (ill-formed program, unsupported feature, etc.)
        ((CERBERUS_FAIL++))
        if $VERBOSE; then
            error_msg=$(echo "$cerberus_output" | grep -o 'msg: "[^"]*"' | head -1 | sed 's/msg: "\([^"]*\)"/\1/')
            echo "SKIP $filename (Cerberus error: $error_msg)"
        fi
        continue
    elif [[ $cerberus_shell_exit -ne 0 ]]; then
        # Cerberus exited with error (constraint violation, etc.)
        ((CERBERUS_FAIL++))
        if $VERBOSE; then
            echo "SKIP $filename (Cerberus exit $cerberus_shell_exit)"
        fi
        continue
    else
        # Could not extract return value - skip
        ((CERBERUS_FAIL++))
        if $VERBOSE; then
            echo "SKIP $filename (could not extract Cerberus return value)"
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

    # Run Lean interpreter in batch mode with timeout
    lean_exit=0
    lean_output=$(timeout ${TIMEOUT_SECS}s "$LEAN_INTERP" --batch "$json_file" 2>&1) || lean_exit=$?

    # Check for timeout (exit code 124)
    if [[ $lean_exit -eq 124 ]]; then
        ((LEAN_TIMEOUT_COUNT++))
        if $VERBOSE; then
            echo "TIMEOUT $filename (Lean >${TIMEOUT_SECS}s)"
        else
            echo ""
            echo "TIMEOUT $filename (Lean >${TIMEOUT_SECS}s)"
        fi
        continue
    fi

    # Extract Lean result from batch output
    # Format: Defined {value: "N"} or Undefined {ub: "CODE"} or Error {msg: "..."}
    lean_ret=""
    lean_has_ub=false
    lean_ub_code=""
    if echo "$lean_output" | grep -q '^Undefined {'; then
        lean_has_ub=true
        lean_ub_code=$(echo "$lean_output" | grep -o 'ub: "[^"]*"' | sed 's/ub: "\([^"]*\)"/\1/')
        lean_ret="UB"
    elif echo "$lean_output" | grep -q '^Defined {'; then
        lean_ret=$(echo "$lean_output" | grep -o 'value: "[^"]*"' | sed 's/value: "\([^"]*\)"/\1/')
    elif echo "$lean_output" | grep -q '^Error {'; then
        error_msg=$(echo "$lean_output" | grep -o 'msg: "[^"]*"' | sed 's/msg: "\([^"]*\)"/\1/')
        lean_ret="ERROR"
        ((LEAN_FAIL++))
        if ! $VERBOSE; then
            echo ""
        fi
        echo "FAIL $filename: $error_msg"
        continue
    else
        # Unexpected output format
        ((LEAN_FAIL++))
        if ! $VERBOSE; then
            echo ""
        fi
        echo "FAIL $filename: unexpected output: $lean_output"
        continue
    fi

    # If both detected UB, compare UB codes
    if $lean_has_ub && $cerberus_has_ub; then
        ((LEAN_OK++))
        if [[ "$lean_ub_code" == "$cerberus_ub_code" ]]; then
            ((UB_MATCH++))
            if $VERBOSE; then
                echo "UB   $filename: $lean_ub_code"
            fi
        else
            # Both detected UB but with different codes - note but count as success
            ((UB_CODE_DIFF++))
            if $VERBOSE; then
                echo "UB~  $filename: Lean=$lean_ub_code Cerberus=$cerberus_ub_code"
            fi
        fi
        continue
    fi

    # One detected UB but not the other - mismatch
    if $lean_has_ub || $cerberus_has_ub; then
        ((LEAN_OK++))
        ((MISMATCH++))
        if ! $VERBOSE; then
            echo ""
        fi
        if $lean_has_ub; then
            echo "DIFF $filename: Lean=UB($lean_ub_code) Cerberus=$cerberus_ret"
        else
            echo "DIFF $filename: Lean=$lean_ret Cerberus=UB($cerberus_ub_code)"
        fi
        continue
    fi

    ((LEAN_OK++))

    # Compare results
    if [[ "$lean_ret" == "$cerberus_ret" ]]; then
        ((MATCH++))
        if $VERBOSE; then
            echo "OK   $filename: $lean_ret"
        fi
    else
        ((MISMATCH++))
        if ! $VERBOSE; then
            echo ""
        fi
        echo "DIFF $filename: Lean=$lean_ret Cerberus=$cerberus_ret"
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
echo "  UB Match:   $UB_MATCH (both detected same UB)"
if [[ $UB_CODE_DIFF -gt 0 ]]; then
    echo "  UB Diff:    $UB_CODE_DIFF (both detected UB, different codes)"
fi
echo "  Mismatch:   $MISMATCH"
echo ""

TOTAL_MATCH=$((MATCH + UB_MATCH + UB_CODE_DIFF))
TOTAL_COMPARE=$((TOTAL_MATCH + MISMATCH))
if [[ $TOTAL_COMPARE -gt 0 ]]; then
    MATCH_RATE=$((TOTAL_MATCH * 100 / TOTAL_COMPARE))
    echo "Match rate:   ${MATCH_RATE}%"
fi

echo ""
echo "Output files saved to: $OUTPUT_DIR"
