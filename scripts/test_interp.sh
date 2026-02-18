#!/bin/bash
# Test the Lean interpreter against Cerberus execution
#
# Usage: ./scripts/test_interp.sh [options] [test_dir_or_file]
#
# Supports:
#   - Single .c file: ./scripts/test_interp.sh path/to/test.c
#   - Directory: tests all *.c files recursively
#   - Cerberus CI directory: uses their tests.sh for the file list
#   - List file: ./scripts/test_interp.sh --list paths.txt (one path per line)
#
# NOTE: This script intentionally does NOT use set -e because it captures
# non-zero exit codes from Cerberus and the Lean interpreter for comparison.

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
set -uo pipefail
# NOTE: -e is intentionally omitted — we capture exit codes for comparison

usage() {
    cat <<'EOF'
Test the Lean interpreter against Cerberus execution.

Usage: ./scripts/test_interp.sh [options] [test_dir_or_file]

Arguments:
  test_dir_or_file   A .c file or directory (default: cerberus/tests/ci)

Options:
  -v, --verbose      Show detailed per-file output
  --max N            Test first N files only
  --list FILE        Read test paths from FILE (one per line)
  --nolibc           Skip libc linking (2MB vs 200MB JSON, faster)
  --mode=MODE        Execution mode: exhaustive (default) or deterministic
  --sequentialise    Use Cerberus sequentialise pass (eliminates Eunseq)
  --exclude=PATTERN  Exclude files whose basename matches PATTERN
  -h, --help         Show this help message

Examples:
  ./scripts/test_interp.sh tests/minimal/001-return-literal.c
  ./scripts/test_interp.sh --nolibc tests/minimal
  ./scripts/test_interp.sh --nolibc --sequentialise --exclude=unseq tests/minimal
  ./scripts/test_interp.sh --max 100 cerberus/tests/ci
EOF
    exit 0
}

# Check for required dependencies
if ! command -v timeout &>/dev/null; then
    echo "Error: 'timeout' command not found" >&2
    echo "On macOS, install with: brew install coreutils" >&2
    exit 1
fi

# Configuration
VERBOSE=false
TEST_PATH=""
LIST_FILE=""
MAX_TESTS=0  # 0 = unlimited
NO_LIBC=false
MODE="exhaustive"
SEQUENTIALISE=false
EXCLUDE_PATTERN=""
OUTPUT_DIR=$(make_temp_dir "interp-test")
register_cleanup "$OUTPUT_DIR"

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help) usage ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        --max)
            MAX_TESTS="$2"
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
        --mode=*)
            MODE="${1#--mode=}"
            shift
            ;;
        --sequentialise|--sequentialize)
            SEQUENTIALISE=true
            shift
            ;;
        --exclude=*)
            EXCLUDE_PATTERN="${1#--exclude=}"
            shift
            ;;
        -*)
            echo "Unknown option: $1" >&2
            echo "Use --help for usage information" >&2
            exit 1
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
        echo "Error: List file not found: $LIST_FILE" >&2
        exit 1
    fi
    # Resolve to absolute path
    LIST_FILE="$(cd "$(dirname "$LIST_FILE")" && pwd)/$(basename "$LIST_FILE")"
fi

# Default test directory
if [[ -z "$TEST_PATH" ]] && ! $LIST_MODE; then
    TEST_PATH="$CERBERUS_DIR/tests/ci"
fi

# Determine if single file or directory
SINGLE_FILE=false
TEST_DIR=""
if ! $LIST_MODE; then
    if [[ -f "$TEST_PATH" ]]; then
        SINGLE_FILE=true
        TEST_PATH="$(cd "$(dirname "$TEST_PATH")" && pwd)/$(basename "$TEST_PATH")"
        TEST_DIR="$(dirname "$TEST_PATH")"
    else
        TEST_DIR="$(cd "$TEST_PATH" && pwd)"
    fi
fi

# Build Lean interpreter
build_lean cerblean_interp
LEAN_INTERP="$LEAN_DIR/.lake/build/bin/cerblean_interp"

# Get test files into array
echo ""
declare -a TEST_FILES=()

if $LIST_MODE; then
    echo "Testing files from list: $LIST_FILE"
    while IFS= read -r line; do
        [[ -z "$line" || "$line" == \#* ]] && continue
        TEST_FILES+=("$line")
    done < "$LIST_FILE"
elif $SINGLE_FILE; then
    echo "Testing single file: $TEST_PATH"
    TEST_FILES=("$TEST_PATH")
elif [[ "$TEST_DIR" == "$CERBERUS_DIR/tests/ci" ]]; then
    echo "Loading test list from Cerberus tests.sh..."
    source "$CERBERUS_DIR/tests/tests.sh"
    for f in "${citests[@]}"; do
        # Skip syntax-only and exhaust tests
        if [[ $f == *.syntax-only.c ]] || [[ $f == *.exhaust.c ]]; then
            continue
        fi
        TEST_FILES+=("$TEST_DIR/$f")
    done
else
    echo "Testing all .c files in $TEST_DIR..."
    while IFS= read -r f; do
        TEST_FILES+=("$f")
    done < <(find "$TEST_DIR" -name "*.c" \
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
    filtered=()
    for f in "${TEST_FILES[@]}"; do
        if [[ "$f" != *.libc.c ]]; then
            filtered+=("$f")
        fi
    done
    TEST_FILES=(${filtered[@]+"${filtered[@]}"})
fi

# Filter out files whose basename matches exclude pattern
if [[ -n "$EXCLUDE_PATTERN" ]]; then
    filtered=()
    for f in "${TEST_FILES[@]}"; do
        bname=$(basename "$f")
        if ! echo "$bname" | grep -q "$EXCLUDE_PATTERN"; then
            filtered+=("$f")
        fi
    done
    TEST_FILES=(${filtered[@]+"${filtered[@]}"})
fi

TOTAL_FILES=${#TEST_FILES[@]}
if ! $SINGLE_FILE || $LIST_MODE; then
    echo "Found $TOTAL_FILES test files"
fi

if [[ $MAX_TESTS -gt 0 ]] && ! $SINGLE_FILE; then
    echo "Testing first $MAX_TESTS files"
    TEST_FILES=("${TEST_FILES[@]:0:$MAX_TESTS}")
fi

# Timeout for interpreters (seconds)
TIMEOUT_SECS=10

# Build Cerberus flags
CERBERUS_FLAGS=()
if $NO_LIBC; then
    CERBERUS_FLAGS+=("--nolibc")
fi
if $SEQUENTIALISE; then
    CERBERUS_FLAGS+=("--sequentialise")
    MODE="deterministic"
elif [[ -n "$MODE" ]]; then
    CERBERUS_FLAGS+=("--mode=$MODE")
fi

# Build Lean interpreter flags
LEAN_FLAGS=()
if [[ -n "$MODE" ]]; then
    LEAN_FLAGS+=("--mode=$MODE")
fi

# Counters
CERBERUS_OK=0
CERBERUS_FAIL=0
LEAN_OK=0
LEAN_FAIL=0
LEAN_TIMEOUT_COUNT=0
MATCH=0
MISMATCH=0
UB_MATCH=0
UB_CODE_DIFF=0
UNSUPPORTED_EXPECTED=0
UNSUPPORTED_UNEXPECTED=0

echo ""
echo "Running interpreter comparison..."
echo "================================="

file_num=0
total_to_test=${#TEST_FILES[@]}

for c_file in "${TEST_FILES[@]}"; do
    filename=$(basename "$c_file" .c)
    file_num=$((file_num + 1))

    # Check if this is an unsupported test (expected to fail)
    expect_unsupported=false
    if [[ "$c_file" == *.unsupported.c ]]; then
        expect_unsupported=true
    fi

    # Run Cerberus in batch mode to get return value (not shell exit code)
    cerberus_shell_exit=0
    cerberus_output=$(timeout "${TIMEOUT_SECS}s" "$CERBERUS" ${CERBERUS_FLAGS[@]+"${CERBERUS_FLAGS[@]}"} --exec --batch "$c_file" 2>&1) || cerberus_shell_exit=$?

    # Check for timeout
    if [[ $cerberus_shell_exit -eq 124 ]]; then
        CERBERUS_FAIL=$((CERBERUS_FAIL + 1))
        echo "[$file_num/$total_to_test] CERB_SKIP $filename (Cerberus timeout)"
        continue
    fi
    cerberus_has_ub=false
    cerberus_ret=""

    if [[ "$cerberus_output" == *"undefined behaviour"* ]]; then
        cerberus_has_ub=true
    fi

    if [[ $cerberus_shell_exit -eq 139 ]] || [[ $cerberus_shell_exit -eq 134 ]] || [[ $cerberus_shell_exit -eq 137 ]]; then
        CERBERUS_FAIL=$((CERBERUS_FAIL + 1))
        echo "[$file_num/$total_to_test] CERB_SKIP $filename (Cerberus crashed: $cerberus_shell_exit)"
        continue
    fi

    # Extract return value from batch output
    # NOTE: Use [[ == *pattern* ]] for boolean checks instead of echo | grep -q,
    # because large outputs (e.g. exhaustive mode with many executions) cause
    # SIGPIPE/broken-pipe when grep -q exits early, and with pipefail this makes
    # the check return non-zero even when the pattern IS present.
    cerberus_ub_code=""
    if [[ "$cerberus_output" == *'Undefined {'* ]]; then
        cerberus_has_ub=true
        cerberus_ub_code=$(echo "$cerberus_output" | grep -o 'ub: "[^"]*"' | head -1 | sed 's/ub: "\([^"]*\)"/\1/')
        cerberus_ret="UB"
    elif [[ "$cerberus_output" == *'value: "Specified'* ]]; then
        cerberus_ret=$(echo "$cerberus_output" | grep -o 'value: "Specified([^)]*)"' | head -1 | sed 's/value: "Specified(\([^)]*\))"/\1/')
    elif [[ "$cerberus_output" == *'value: "Unspecified'* ]]; then
        cerberus_ret=$(echo "$cerberus_output" | grep -o 'value: "[^"]*"' | head -1 | sed 's/value: "\([^"]*\)"/\1/')
    elif [[ "$cerberus_output" == *'Error {'* ]]; then
        CERBERUS_FAIL=$((CERBERUS_FAIL + 1))
        error_msg=$(echo "$cerberus_output" | grep -o 'msg: "[^"]*"' | head -1 | sed 's/msg: "\([^"]*\)"/\1/')
        echo "[$file_num/$total_to_test] CERB_SKIP $filename (error: $error_msg)"
        continue
    elif [[ $cerberus_shell_exit -ne 0 ]]; then
        CERBERUS_FAIL=$((CERBERUS_FAIL + 1))
        echo "[$file_num/$total_to_test] CERB_SKIP $filename (exit $cerberus_shell_exit)"
        continue
    else
        CERBERUS_FAIL=$((CERBERUS_FAIL + 1))
        echo "[$file_num/$total_to_test] CERB_SKIP $filename (could not extract return value)"
        continue
    fi
    CERBERUS_OK=$((CERBERUS_OK + 1))

    # Generate JSON for Lean
    json_file="$OUTPUT_DIR/$filename.json"
    if ! "$CERBERUS" ${CERBERUS_FLAGS[@]+"${CERBERUS_FLAGS[@]}"} --json_core_out="$json_file" "$c_file" >/dev/null 2>&1; then
        CERBERUS_FAIL=$((CERBERUS_FAIL + 1))
        echo "[$file_num/$total_to_test] CERB_INCONSISTENT $filename: exec succeeded but JSON failed"
        continue
    fi

    # Run Lean interpreter in batch mode with timeout
    lean_exit=0
    lean_output=$(timeout "${TIMEOUT_SECS}s" "$LEAN_INTERP" --batch ${LEAN_FLAGS[@]+"${LEAN_FLAGS[@]}"} "$json_file" 2>&1) || lean_exit=$?

    # Check for timeout (exit code 124)
    if [[ $lean_exit -eq 124 ]]; then
        if $expect_unsupported; then
            UNSUPPORTED_EXPECTED=$((UNSUPPORTED_EXPECTED + 1))
            echo "[$file_num/$total_to_test] UNSUPPORTED $filename (timeout, expected)"
        else
            LEAN_TIMEOUT_COUNT=$((LEAN_TIMEOUT_COUNT + 1))
            echo "[$file_num/$total_to_test] TIMEOUT $filename (Lean >${TIMEOUT_SECS}s)"
        fi
        continue
    fi

    # Extract Lean result from batch output
    lean_ret=""
    lean_has_ub=false
    lean_ub_code=""
    if [[ "$lean_output" == *'Undefined {'* ]]; then
        lean_has_ub=true
        lean_ub_code=$(echo "$lean_output" | grep -o 'ub: "[^"]*"' | sed 's/ub: "\([^"]*\)"/\1/')
        lean_ret="UB"
    elif [[ "$lean_output" == *'Defined {'* ]]; then
        if [[ "$lean_output" == *'value: "Specified'* ]]; then
            lean_ret=$(echo "$lean_output" | grep -o 'value: "Specified([^)]*)"' | sed 's/value: "Specified(\([^)]*\))"/\1/')
        elif [[ "$lean_output" == *'value: "Unspecified'* ]]; then
            lean_ret=$(echo "$lean_output" | grep -o 'value: "[^"]*"' | sed 's/value: "\([^"]*\)"/\1/')
        else
            lean_ret=$(echo "$lean_output" | grep -o 'value: "[^"]*"' | sed 's/value: "\([^"]*\)"/\1/')
        fi
    elif [[ "$lean_output" == *'Error {'* ]]; then
        error_msg=$(echo "$lean_output" | grep -o 'msg: "[^"]*"' | sed 's/msg: "\([^"]*\)"/\1/')
        lean_ret="ERROR"
        if $expect_unsupported; then
            UNSUPPORTED_EXPECTED=$((UNSUPPORTED_EXPECTED + 1))
            echo "[$file_num/$total_to_test] UNSUPPORTED $filename: $error_msg"
        else
            LEAN_FAIL=$((LEAN_FAIL + 1))
            echo "[$file_num/$total_to_test] FAIL $filename: $error_msg"
        fi
        continue
    else
        if $expect_unsupported; then
            UNSUPPORTED_EXPECTED=$((UNSUPPORTED_EXPECTED + 1))
            echo "[$file_num/$total_to_test] UNSUPPORTED $filename: unexpected output"
        else
            LEAN_FAIL=$((LEAN_FAIL + 1))
            echo "[$file_num/$total_to_test] FAIL $filename: unexpected output: $lean_output"
        fi
        continue
    fi

    # If both detected UB, compare UB codes
    if $lean_has_ub && $cerberus_has_ub; then
        LEAN_OK=$((LEAN_OK + 1))
        if [[ "$lean_ub_code" == "$cerberus_ub_code" ]]; then
            UB_MATCH=$((UB_MATCH + 1))
            echo "[$file_num/$total_to_test] UB_MATCH $filename: $lean_ub_code"
        else
            UB_CODE_DIFF=$((UB_CODE_DIFF + 1))
            echo "[$file_num/$total_to_test] UB_DIFF $filename: Lean=$lean_ub_code Cerberus=$cerberus_ub_code"
        fi
        continue
    fi

    # One detected UB but not the other — mismatch
    if $lean_has_ub || $cerberus_has_ub; then
        if $expect_unsupported; then
            UNSUPPORTED_EXPECTED=$((UNSUPPORTED_EXPECTED + 1))
            if $lean_has_ub; then
                echo "[$file_num/$total_to_test] UNSUPPORTED $filename: Lean=UB($lean_ub_code) Cerberus=$cerberus_ret"
            else
                echo "[$file_num/$total_to_test] UNSUPPORTED $filename: Lean=$lean_ret Cerberus=UB($cerberus_ub_code)"
            fi
        else
            LEAN_OK=$((LEAN_OK + 1))
            MISMATCH=$((MISMATCH + 1))
            if $lean_has_ub; then
                echo "[$file_num/$total_to_test] DIFF $filename: Lean=UB($lean_ub_code) Cerberus=$cerberus_ret"
            else
                echo "[$file_num/$total_to_test] DIFF $filename: Lean=$lean_ret Cerberus=UB($cerberus_ub_code)"
            fi
        fi
        continue
    fi

    LEAN_OK=$((LEAN_OK + 1))

    # Compare results
    if [[ "$lean_ret" == "$cerberus_ret" ]]; then
        if $expect_unsupported; then
            UNSUPPORTED_UNEXPECTED=$((UNSUPPORTED_UNEXPECTED + 1))
            echo "[$file_num/$total_to_test] UNSUPPORTED_PASS $filename: $lean_ret (expected failure but passed!)"
        else
            MATCH=$((MATCH + 1))
            echo "[$file_num/$total_to_test] MATCH $filename: $lean_ret"
        fi
    else
        if $expect_unsupported; then
            UNSUPPORTED_EXPECTED=$((UNSUPPORTED_EXPECTED + 1))
            echo "[$file_num/$total_to_test] UNSUPPORTED $filename: Lean=$lean_ret Cerberus=$cerberus_ret"
        else
            MISMATCH=$((MISMATCH + 1))
            echo "[$file_num/$total_to_test] MISMATCH $filename: Lean=$lean_ret Cerberus=$cerberus_ret"
        fi
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

if [[ $UNSUPPORTED_EXPECTED -gt 0 ]] || [[ $UNSUPPORTED_UNEXPECTED -gt 0 ]]; then
    echo "Unsupported (*.unsupported.c):"
    echo "  Expected:   $UNSUPPORTED_EXPECTED (failed as expected)"
    if [[ $UNSUPPORTED_UNEXPECTED -gt 0 ]]; then
        echo "  Unexpected: $UNSUPPORTED_UNEXPECTED (passed — consider removing .unsupported suffix)"
    fi
    echo ""
fi

TOTAL_MATCH=$((MATCH + UB_MATCH + UB_CODE_DIFF))
TOTAL_COMPARE=$((TOTAL_MATCH + MISMATCH))
if [[ $TOTAL_COMPARE -gt 0 ]]; then
    MATCH_RATE=$((TOTAL_MATCH * 100 / TOTAL_COMPARE))
    echo "Match rate:   ${MATCH_RATE}%"
fi

echo ""
echo "Output files saved to: $OUTPUT_DIR"

# Exit with failure if there were interpreter errors or mismatches
if [[ $LEAN_FAIL -gt 0 ]]; then
    echo ""
    echo -e "${RED}FAILED: $LEAN_FAIL interpreter error(s)${NC}"
    exit 1
fi

if [[ $MISMATCH -gt 0 ]]; then
    echo ""
    echo -e "${RED}FAILED: $MISMATCH mismatch(es) with Cerberus${NC}"
    exit 1
fi
