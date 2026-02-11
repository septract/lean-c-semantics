#!/bin/bash
# Test CN type checking
#
# Usage: ./scripts/test_cn.sh [options] [file.c ...]
#
# Options:
#   --unit         Run unit tests only (no Cerberus required)
#   --nolibc       Skip libc (faster, skips *.libc.* tests)
#   --libc-only    Run only *.libc.* tests (with libc)
#   -v, --verbose  Show detailed output per test
#   -h, --help     Show this help message

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
set -uo pipefail
# NOTE: -e is intentionally omitted — we capture exit codes for comparison

usage() {
    cat <<'EOF'
Test CN type checking.

Usage: ./scripts/test_cn.sh [options] [file.c ...]

With no arguments, runs all integration tests in tests/cn/.
With file arguments, tests only those specific C files.

Options:
  --unit         Run unit tests only (no Cerberus required)
  --nolibc       Skip libc (faster, skips *.libc.* tests)
  --libc-only    Run only *.libc.* tests (with libc)
  -v, --verbose  Show detailed output per test
  -h, --help     Show this help message

Examples:
  ./scripts/test_cn.sh                      # All integration tests
  ./scripts/test_cn.sh --nolibc             # Skip libc tests (faster)
  ./scripts/test_cn.sh --libc-only          # Only libc tests
  ./scripts/test_cn.sh tests/cn/001-*.c     # Specific test
  ./scripts/test_cn.sh --unit               # Unit tests only
EOF
    exit 0
}

# Parse arguments
UNIT_MODE=false
NO_LIBC=false
LIBC_ONLY=false
VERBOSE=false
TEST_ARGS=()

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help) usage ;;
        --unit)
            UNIT_MODE=true
            shift
            ;;
        --nolibc)
            NO_LIBC=true
            shift
            ;;
        --libc-only)
            LIBC_ONLY=true
            shift
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -*)
            echo "Unknown option: $1" >&2
            echo "Use --help for usage information" >&2
            exit 1
            ;;
        *)
            TEST_ARGS+=("$1")
            shift
            ;;
    esac
done

TEST_CN="$LEAN_DIR/.lake/build/bin/test_cn"

# Validate flag combinations
if $NO_LIBC && $LIBC_ONLY; then
    echo "Error: --nolibc and --libc-only are mutually exclusive" >&2
    exit 1
fi

# Handle --unit flag: run unit tests only
if $UNIT_MODE; then
    build_lean test_cn
    echo ""
    echo "=== CN Unit Tests ==="
    exec "$TEST_CN"
fi

# Determine test files (resolve paths before any cd)
TEST_FILES=()
if [[ ${#TEST_ARGS[@]} -eq 0 ]]; then
    # No args: run all integration tests in tests/cn/
    for f in "$PROJECT_ROOT"/tests/cn/*.c; do
        TEST_FILES+=("$f")
    done
else
    # Specific files provided — resolve to absolute paths
    for arg in "${TEST_ARGS[@]}"; do
        if [[ "$arg" = /* ]]; then
            TEST_FILES+=("$arg")
        else
            TEST_FILES+=("$PROJECT_ROOT/$arg")
        fi
    done
fi

# Filter test files based on libc flags
if $NO_LIBC; then
    FILTERED=()
    for f in "${TEST_FILES[@]}"; do
        [[ "$(basename "$f")" == *.libc.* ]] && continue
        FILTERED+=("$f")
    done
    TEST_FILES=("${FILTERED[@]}")
elif $LIBC_ONLY; then
    FILTERED=()
    for f in "${TEST_FILES[@]}"; do
        [[ "$(basename "$f")" == *.libc.* ]] || continue
        FILTERED+=("$f")
    done
    TEST_FILES=("${FILTERED[@]}")
fi

# Check prerequisites
require_cerberus

# Build Lean project
build_lean test_cn
echo ""

# Set up temp file for JSON
TMP_JSON=$(mktemp "$TMP_DIR/cn-test-XXXXXXXXXX")
register_cleanup "$TMP_JSON"

# Counters
TOTAL_PASS=0
TOTAL_FAIL=0
TOTAL_CERB_SKIP=0
FAILED_FILES=()

total_to_test=${#TEST_FILES[@]}
echo "Running CN type checking..."
echo "================================="
echo "Testing $total_to_test file(s)"
echo ""

file_num=0
for TEST_FILE in "${TEST_FILES[@]}"; do
    BASENAME=$(basename "$TEST_FILE" .c)
    file_num=$((file_num + 1))
    prefix="[$file_num/$total_to_test]"

    # Determine if this is an expected-failure test
    EXPECT_FAIL=false
    if [[ "$BASENAME" == *.fail ]] || [[ "$BASENAME" == *.smt-fail ]]; then
        EXPECT_FAIL=true
    fi

    # Check test file exists
    if [[ ! -f "$TEST_FILE" ]]; then
        echo "$prefix FAIL $BASENAME: file not found"
        TOTAL_FAIL=$((TOTAL_FAIL + 1))
        FAILED_FILES+=("$TEST_FILE")
        continue
    fi

    # Generate JSON with Cerberus
    CERBERUS_FLAGS=("--switches=at_magic_comments")
    if $NO_LIBC; then
        CERBERUS_FLAGS+=("--nolibc")
    fi
    cerb_exit=0
    cerb_output=$("$CERBERUS" "${CERBERUS_FLAGS[@]}" --json_core_out="$TMP_JSON" "$TEST_FILE" 2>&1) || cerb_exit=$?
    if [[ $cerb_exit -ne 0 ]]; then
        TOTAL_CERB_SKIP=$((TOTAL_CERB_SKIP + 1))
        cerb_reason=$(echo "$cerb_output" | head -1 | cut -c1-80)
        echo "$prefix CERB_SKIP $BASENAME: $cerb_reason"
        continue
    fi

    # Run Lean CN type checker (no --expect-fail; we handle expectations here)
    cn_exit=0
    cn_output=$("$TEST_CN" "$TMP_JSON" 2>&1) || cn_exit=$?

    if $VERBOSE; then
        # Show full test_cn output indented
        if [[ -n "$cn_output" ]]; then
            echo "$cn_output" | sed 's/^/  /'
        fi
    fi

    if $EXPECT_FAIL; then
        if [[ $cn_exit -ne 0 ]]; then
            # Expected fail, got fail — correct
            TOTAL_PASS=$((TOTAL_PASS + 1))
            echo "$prefix PASS $BASENAME (failed as expected)"
        else
            # Expected fail, got pass — wrong
            TOTAL_FAIL=$((TOTAL_FAIL + 1))
            FAILED_FILES+=("$TEST_FILE")
            echo "$prefix FAIL $BASENAME: expected failure but passed"
        fi
    else
        if [[ $cn_exit -eq 0 ]]; then
            # Expected pass, got pass — correct
            TOTAL_PASS=$((TOTAL_PASS + 1))
            echo "$prefix PASS $BASENAME"
        else
            # Expected pass, got fail — wrong
            TOTAL_FAIL=$((TOTAL_FAIL + 1))
            FAILED_FILES+=("$TEST_FILE")
            # Extract a one-line reason from test_cn output (prefer "error:" lines)
            reason=$(echo "$cn_output" | grep -m1 'error:' | sed 's/^[[:space:]]*//' | cut -c1-80)
            reason=${reason:-$(echo "$cn_output" | grep -i -m1 'fail\|not yet\|not impl\|unsupported\|unhandled' | sed 's/^[[:space:]]*//' | cut -c1-80)}
            reason=${reason:-"(no details)"}
            echo "$prefix FAIL $BASENAME: $reason"
        fi
    fi
done

echo ""
echo "================================="
echo "Results Summary"
echo "================================="
echo ""
echo "  Pass:      $TOTAL_PASS"
echo "  Fail:      $TOTAL_FAIL"
echo "  Cerb Skip: $TOTAL_CERB_SKIP"
echo ""

if [[ ${#FAILED_FILES[@]} -gt 0 ]]; then
    echo "Failed files:"
    for f in "${FAILED_FILES[@]}"; do
        echo "  - $(basename "$f")"
    done
    echo ""
fi

TOTAL_RAN=$((TOTAL_PASS + TOTAL_FAIL))
if [[ $TOTAL_RAN -gt 0 ]]; then
    PASS_RATE=$((TOTAL_PASS * 100 / TOTAL_RAN))
    echo "Pass rate: ${PASS_RATE}% ($TOTAL_PASS/$TOTAL_RAN)"
fi

# Exit with failure if any tests failed
if [[ $TOTAL_FAIL -gt 0 ]]; then
    echo ""
    echo -e "${RED}FAILED: $TOTAL_FAIL test failure(s)${NC}"
    exit 1
fi
