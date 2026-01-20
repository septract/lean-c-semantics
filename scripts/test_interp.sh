#!/bin/bash
# Test the Lean interpreter against Cerberus execution
# Usage: ./scripts/test_interp.sh [--verbose] [--max N] [--list FILE] [--nolibc] [test_dir_or_file]
#
# Supports:
#   - Single .c file: ./scripts/test_interp.sh path/to/test.c
#   - Directory: tests all *.c files recursively
#   - Cerberus CI directory: uses their tests.sh for the file list
#   - List file: ./scripts/test_interp.sh --list paths.txt (one path per line)
#
# Options:
#   --nolibc: Skip libc linking for faster testing (2MB vs 200MB JSON).
#             Tests named *.libc.c are automatically skipped in this mode.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
CERBERUS_DIR="$PROJECT_DIR/cerberus"
LEAN_DIR="$PROJECT_DIR/lean"

# Check for required dependencies
command -v timeout &> /dev/null || { echo "Error: 'timeout' command not found"; exit 1; }

# Cerberus wrapper script (handles local opam switch)
CERBERUS="$PROJECT_DIR/scripts/cerberus"

# Configuration
VERBOSE=false
TEST_PATH=""  # Can be a file or directory
LIST_FILE=""  # File containing list of test paths
MAX_TESTS=0  # 0 = unlimited
NO_LIBC=false  # Skip libc linking for faster JSON (2MB vs 200MB)
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
        --list)
            LIST_FILE="$2"
            shift 2
            ;;
        --nolibc)
            NO_LIBC=true
            shift
            ;;
        *)
            TEST_PATH="$1"
            shift
            ;;
    esac
done

# Handle --list mode vs path mode
LIST_MODE=false
if [[ -n "$LIST_FILE" ]]; then
    LIST_MODE=true
    if [[ ! -f "$LIST_FILE" ]]; then
        echo "Error: List file not found: $LIST_FILE"
        exit 1
    fi
    # Resolve to absolute path before we change directories
    LIST_FILE="$(cd "$(dirname "$LIST_FILE")" && pwd)/$(basename "$LIST_FILE")"
fi

# Default test directory (only used if not in list mode)
if [[ -z "$TEST_PATH" ]] && ! $LIST_MODE; then
    TEST_PATH="$CERBERUS_DIR/tests/ci"
fi

# Check if it's a single file or a directory (only relevant if not list mode)
SINGLE_FILE=false
TEST_DIR=""
if ! $LIST_MODE; then
    if [[ -f "$TEST_PATH" ]]; then
        SINGLE_FILE=true
        # For single file, resolve to absolute path
        TEST_PATH="$(cd "$(dirname "$TEST_PATH")" && pwd)/$(basename "$TEST_PATH")"
        TEST_DIR="$(dirname "$TEST_PATH")"
    else
        # Resolve directory to absolute path
        TEST_DIR="$(cd "$TEST_PATH" && pwd)"
    fi
fi

# Build Lean interpreter
echo "Building Lean interpreter..."
cd "$LEAN_DIR"
lake build cerblean_interp 2>&1 | tail -3
LEAN_INTERP="$LEAN_DIR/.lake/build/bin/cerblean_interp"

# Get test files
echo ""
if $LIST_MODE; then
    # List file mode - read paths from file (one per line)
    echo "Testing files from list: $LIST_FILE"
    # Read non-empty, non-comment lines
    TEST_FILES=$(grep -v '^#' "$LIST_FILE" | grep -v '^$' | tr '\n' ' ')
elif $SINGLE_FILE; then
    # Single file mode
    echo "Testing single file: $TEST_PATH"
    TEST_FILES="$TEST_PATH"
elif [[ "$TEST_DIR" == "$CERBERUS_DIR/tests/ci" ]]; then
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
    #   csmith/     - Csmith tests (require special header setup, use fuzz_csmith.sh)
    #   pnvi_testsuite/ - PNVI provenance tests
    echo "Testing all .c files in $TEST_DIR..."
    TEST_FILES=$(find "$TEST_DIR" -name "*.c" \
        ! -name "*.syntax-only.c" \
        ! -name "*.exhaust.c" \
        ! -path "*/bmc/*" \
        ! -path "*/cheri-ci/*" \
        ! -path "*/csmith/*" \
        ! -path "*/pnvi_testsuite/*" \
        | sort)
fi

# Filter out .libc.c files when --nolibc is set
if $NO_LIBC; then
    TEST_FILES=$(echo $TEST_FILES | tr ' ' '\n' | grep -v '\.libc\.c$' | tr '\n' ' ')
fi

TOTAL_FILES=$(echo $TEST_FILES | wc -w | tr -d ' ')
if ! $SINGLE_FILE || $LIST_MODE; then
    echo "Found $TOTAL_FILES test files"
fi

if [[ $MAX_TESTS -gt 0 ]] && ! $SINGLE_FILE; then
    echo "Testing first $MAX_TESTS files"
    TEST_FILES=$(echo $TEST_FILES | tr ' ' '\n' | head -n $MAX_TESTS | tr '\n' ' ')
fi

# Timeout for interpreters (seconds)
TIMEOUT_SECS=10

# Build Cerberus flags
# Always use --sequentialise since our interpreter evaluates unseq left-to-right
# (matches Cerberus's sequentialised behavior, not its non-deterministic exploration)
CERBERUS_FLAGS="--sequentialise"
if $NO_LIBC; then
    CERBERUS_FLAGS="$CERBERUS_FLAGS --nolibc"
fi

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

    # Run Cerberus in batch mode to get return value (not shell exit code)
    cerberus_shell_exit=0
    cerberus_output=$(timeout ${TIMEOUT_SECS}s $CERBERUS $CERBERUS_FLAGS --exec --batch "$c_file" 2>&1) || cerberus_shell_exit=$?

    # Check for timeout
    if [[ $cerberus_shell_exit -eq 124 ]]; then
        (( CERBERUS_FAIL++ )) || true
        echo "[$file_num/$total_to_test] CERB_SKIP $filename (Cerberus timeout)"
        continue
    fi
    cerberus_has_ub=false
    cerberus_ret=""

    if echo "$cerberus_output" | grep -q "undefined behaviour"; then
        cerberus_has_ub=true
    fi

    if [[ $cerberus_shell_exit -eq 139 ]] || [[ $cerberus_shell_exit -eq 134 ]] || [[ $cerberus_shell_exit -eq 137 ]]; then
        # Cerberus crashed (SIGSEGV, SIGABRT, etc.) - skip
        (( CERBERUS_FAIL++ )) || true
        echo "[$file_num/$total_to_test] CERB_SKIP $filename (Cerberus crashed: $cerberus_shell_exit)"
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
        cerberus_ret=$(echo "$cerberus_output" | grep -o 'value: "[^"]*"' | sed 's/value: "\([^"]*\)"/\1/')
    elif echo "$cerberus_output" | grep -q '^Error {'; then
        # Cerberus reported an error (ill-formed program, unsupported feature, etc.)
        (( CERBERUS_FAIL++ )) || true
        error_msg=$(echo "$cerberus_output" | grep -o 'msg: "[^"]*"' | head -1 | sed 's/msg: "\([^"]*\)"/\1/')
        echo "[$file_num/$total_to_test] CERB_SKIP $filename (error: $error_msg)"
        continue
    elif [[ $cerberus_shell_exit -ne 0 ]]; then
        # Cerberus exited with error (constraint violation, etc.)
        (( CERBERUS_FAIL++ )) || true
        echo "[$file_num/$total_to_test] CERB_SKIP $filename (exit $cerberus_shell_exit)"
        continue
    else
        # Could not extract return value - skip
        (( CERBERUS_FAIL++ )) || true
        echo "[$file_num/$total_to_test] CERB_SKIP $filename (could not extract return value)"
        continue
    fi
    (( CERBERUS_OK++ )) || true

    # Generate JSON for Lean
    json_file="$OUTPUT_DIR/$filename.json"
    if ! eval $CERBERUS $CERBERUS_FLAGS --json_core_out="$json_file" "$c_file" >/dev/null 2>&1; then
        # JSON generation failed after Cerberus execution succeeded
        # This is a Cerberus inconsistency (--exec is more lenient than --json_core_out)
        (( CERBERUS_FAIL++ )) || true
        echo "[$file_num/$total_to_test] CERB_INCONSISTENT $filename: exec succeeded but JSON failed"
        continue
    fi

    # Run Lean interpreter in batch mode with timeout
    lean_exit=0
    lean_output=$(timeout ${TIMEOUT_SECS}s "$LEAN_INTERP" --batch "$json_file" 2>&1) || lean_exit=$?

    # Check for timeout (exit code 124)
    if [[ $lean_exit -eq 124 ]]; then
        (( LEAN_TIMEOUT_COUNT++ )) || true
        echo "[$file_num/$total_to_test] TIMEOUT $filename (Lean >${TIMEOUT_SECS}s)"
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
        if echo "$lean_output" | grep -q 'value: "Specified'; then
            lean_ret=$(echo "$lean_output" | grep -o 'value: "Specified([^)]*)"' | sed 's/value: "Specified(\([^)]*\))"/\1/')
        elif echo "$lean_output" | grep -q 'value: "Unspecified'; then
            lean_ret=$(echo "$lean_output" | grep -o 'value: "[^"]*"' | sed 's/value: "\([^"]*\)"/\1/')
        else
            lean_ret=$(echo "$lean_output" | grep -o 'value: "[^"]*"' | sed 's/value: "\([^"]*\)"/\1/')
        fi
    elif echo "$lean_output" | grep -q '^Error {'; then
        error_msg=$(echo "$lean_output" | grep -o 'msg: "[^"]*"' | sed 's/msg: "\([^"]*\)"/\1/')
        lean_ret="ERROR"
        (( LEAN_FAIL++ )) || true
        echo "[$file_num/$total_to_test] FAIL $filename: $error_msg"
        continue
    else
        # Unexpected output format
        (( LEAN_FAIL++ )) || true
        echo "[$file_num/$total_to_test] FAIL $filename: unexpected output: $lean_output"
        continue
    fi

    # If both detected UB, compare UB codes
    if $lean_has_ub && $cerberus_has_ub; then
        (( LEAN_OK++ )) || true
        if [[ "$lean_ub_code" == "$cerberus_ub_code" ]]; then
            (( UB_MATCH++ )) || true
            echo "[$file_num/$total_to_test] UB_MATCH $filename: $lean_ub_code"
        else
            # Both detected UB but with different codes - note but count as success
            (( UB_CODE_DIFF++ )) || true
            echo "[$file_num/$total_to_test] UB_DIFF $filename: Lean=$lean_ub_code Cerberus=$cerberus_ub_code"
        fi
        continue
    fi

    # One detected UB but not the other - mismatch
    if $lean_has_ub || $cerberus_has_ub; then
        (( LEAN_OK++ )) || true
        (( MISMATCH++ )) || true
        if $lean_has_ub; then
            echo "[$file_num/$total_to_test] DIFF $filename: Lean=UB($lean_ub_code) Cerberus=$cerberus_ret"
        else
            echo "[$file_num/$total_to_test] DIFF $filename: Lean=$lean_ret Cerberus=UB($cerberus_ub_code)"
        fi
        continue
    fi

    (( LEAN_OK++ )) || true

    # Compare results
    if [[ "$lean_ret" == "$cerberus_ret" ]]; then
        (( MATCH++ )) || true
        echo "[$file_num/$total_to_test] MATCH $filename: $lean_ret"
    else
        (( MISMATCH++ )) || true
        echo "[$file_num/$total_to_test] MISMATCH $filename: Lean=$lean_ret Cerberus=$cerberus_ret"
    fi
done

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
