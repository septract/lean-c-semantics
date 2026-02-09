#!/bin/bash
# Test CN type checking
#
# Usage: ./scripts/test_cn.sh [options] [file.c ...]
#
# Options:
#   --unit         Run unit tests only (no Cerberus required)
#   -v, --verbose  Show detailed output per test
#   -h, --help     Show this help message

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
set -euo pipefail

usage() {
    cat <<'EOF'
Test CN type checking.

Usage: ./scripts/test_cn.sh [options] [file.c ...]

With no arguments, runs all integration tests in tests/cn/.
With file arguments, tests only those specific C files.

Options:
  --unit         Run unit tests only (no Cerberus required)
  -v, --verbose  Show detailed output per test
  -h, --help     Show this help message

Examples:
  ./scripts/test_cn.sh                      # All integration tests
  ./scripts/test_cn.sh tests/cn/001-*.c     # Specific test
  ./scripts/test_cn.sh --unit               # Unit tests only
EOF
    exit 0
}

# Parse arguments
UNIT_MODE=false
VERBOSE=false
TEST_ARGS=()

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help) usage ;;
        --unit)
            UNIT_MODE=true
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

# Build Lean project
build_lean test_cn
echo ""

# Set up temp file for JSON
TMP_JSON=$(mktemp "$TMP_DIR/cn-test-XXXXXXXXXX")
register_cleanup "$TMP_JSON"

# Track results
TOTAL_PASS=0
TOTAL_FAIL=0
FAILED_FILES=()

echo "=== CN Integration Tests ==="
echo "Testing ${#TEST_FILES[@]} file(s)"
echo ""

for TEST_FILE in "${TEST_FILES[@]}"; do
    BASENAME=$(basename "$TEST_FILE")

    if $VERBOSE; then
        echo "=== Testing: $BASENAME ==="
    fi

    # Determine if this is an expected-failure test
    EXPECT_FAIL=""
    if [[ "$BASENAME" == *.fail.c ]] || [[ "$BASENAME" == *.smt-fail.c ]]; then
        EXPECT_FAIL="--expect-fail"
        if $VERBOSE; then
            echo "  (expecting failure)"
        fi
    fi

    # Check test file exists
    if [[ ! -f "$TEST_FILE" ]]; then
        echo -e "${RED}ERROR: Test file not found: $TEST_FILE${NC}"
        TOTAL_FAIL=$((TOTAL_FAIL + 1))
        FAILED_FILES+=("$TEST_FILE")
        continue
    fi

    # Generate JSON with Cerberus
    if ! "$CERBERUS" --switches=at_magic_comments --json_core_out="$TMP_JSON" "$TEST_FILE" 2>/dev/null; then
        echo -e "${RED}  ERROR: Cerberus failed on $BASENAME${NC}"
        TOTAL_FAIL=$((TOTAL_FAIL + 1))
        FAILED_FILES+=("$TEST_FILE")
        continue
    fi

    # Run Lean test on JSON (with --expect-fail for .fail.c files)
    if "$TEST_CN" $EXPECT_FAIL "$TMP_JSON" 2>&1; then
        TOTAL_PASS=$((TOTAL_PASS + 1))
    else
        echo -e "${RED}  ERROR: Lean test failed on $BASENAME${NC}"
        TOTAL_FAIL=$((TOTAL_FAIL + 1))
        FAILED_FILES+=("$TEST_FILE")
    fi

    if $VERBOSE; then
        echo ""
    fi
done

echo "=== Summary ==="
echo -e "Passed: ${GREEN}$TOTAL_PASS${NC}"
echo -e "Failed: ${RED}$TOTAL_FAIL${NC}"

if [[ ${#FAILED_FILES[@]} -gt 0 ]]; then
    echo ""
    echo "Failed files:"
    for f in "${FAILED_FILES[@]}"; do
        echo "  - $f"
    done
    exit 1
fi

echo "=== All Tests Complete ==="
