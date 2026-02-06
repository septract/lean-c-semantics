#!/bin/bash
# Test CN type checking
#
# Usage: ./scripts/test_cn.sh              Run integration tests on tests/cn/
#        ./scripts/test_cn.sh [file.c ...] Test specific C files
#        ./scripts/test_cn.sh --unit       Run unit tests only (no Cerberus)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
LEAN_DIR="$PROJECT_ROOT/lean"
TEST_CN="$LEAN_DIR/.lake/build/bin/test_cn"

# Build Lean project first
echo "=== Building Lean project ==="
cd "$LEAN_DIR"
if ! lake build test_cn 2>&1 | tail -5; then
    echo "ERROR: Lean build failed"
    exit 1
fi
echo ""

# Handle --unit flag: run unit tests only
if [ "$1" == "--unit" ]; then
    echo "=== CN Unit Tests ==="
    exec "$TEST_CN"
fi

# Determine test files
if [ $# -eq 0 ]; then
    # No args: run all integration tests in tests/cn/
    TEST_FILES=("$PROJECT_ROOT"/tests/cn/*.c)
else
    # Specific files provided
    TEST_FILES=("$@")
fi

TMP_DIR="$PROJECT_ROOT/tmp"
mkdir -p "$TMP_DIR"
TMP_JSON="$TMP_DIR/cn-test-$$.json"

cleanup() {
    rm -f "$TMP_JSON"
}
trap cleanup EXIT

# Track results
TOTAL_PASS=0
TOTAL_FAIL=0
FAILED_FILES=()

echo "=== CN Integration Tests ==="
echo "Testing ${#TEST_FILES[@]} file(s)"
echo ""

for TEST_FILE in "${TEST_FILES[@]}"; do
    BASENAME=$(basename "$TEST_FILE")
    echo "=== Testing: $BASENAME ==="

    # Determine if this is an expected-failure test
    EXPECT_FAIL=""
    if [[ "$BASENAME" == *.fail.c ]] || [[ "$BASENAME" == *.smt-fail.c ]]; then
        EXPECT_FAIL="--expect-fail"
        echo "  (expecting failure)"
    fi

    # Check test file exists
    if [ ! -f "$TEST_FILE" ]; then
        echo "ERROR: Test file not found: $TEST_FILE"
        TOTAL_FAIL=$((TOTAL_FAIL + 1))
        FAILED_FILES+=("$TEST_FILE")
        continue
    fi

    # Generate JSON with Cerberus
    if ! "$SCRIPT_DIR/cerberus" --switches=at_magic_comments --json_core_out="$TMP_JSON" "$TEST_FILE" 2>/dev/null; then
        echo "  ERROR: Cerberus failed"
        TOTAL_FAIL=$((TOTAL_FAIL + 1))
        FAILED_FILES+=("$TEST_FILE")
        continue
    fi

    # Run Lean test on JSON (with --expect-fail for .fail.c files)
    if "$TEST_CN" $EXPECT_FAIL "$TMP_JSON" 2>&1; then
        TOTAL_PASS=$((TOTAL_PASS + 1))
    else
        echo "  ERROR: Lean test failed"
        TOTAL_FAIL=$((TOTAL_FAIL + 1))
        FAILED_FILES+=("$TEST_FILE")
    fi
    echo ""
done

echo "=== Summary ==="
echo "Passed: $TOTAL_PASS"
echo "Failed: $TOTAL_FAIL"

if [ ${#FAILED_FILES[@]} -gt 0 ]; then
    echo ""
    echo "Failed files:"
    for f in "${FAILED_FILES[@]}"; do
        echo "  - $f"
    done
    exit 1
fi

echo "=== All Tests Complete ==="
