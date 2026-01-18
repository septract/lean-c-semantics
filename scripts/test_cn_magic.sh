#!/bin/bash
# Test that CN magic comments are correctly extracted from C files and parsed by Lean
#
# Usage: ./scripts/test_cn_magic.sh [test_file.c]
#
# If no test file is provided, uses the default test file.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
LEAN_DIR="$PROJECT_ROOT/lean"

# Default test file
TEST_FILE="${1:-$PROJECT_ROOT/tests/cn/001-simple-owned.c}"
TMP_JSON="/tmp/cn-magic-test-$$.json"

cleanup() {
    rm -f "$TMP_JSON"
}
trap cleanup EXIT

echo "=== CN Magic Comment Pipeline Test ==="
echo ""

# Step 1: Check test file exists
if [ ! -f "$TEST_FILE" ]; then
    echo "ERROR: Test file not found: $TEST_FILE"
    exit 1
fi

echo "Test file: $TEST_FILE"
echo ""
echo "--- C source ---"
cat "$TEST_FILE"
echo ""
echo "--- End C source ---"
echo ""

# Step 2: Generate JSON with Cerberus
echo "Step 1: Running Cerberus with --switches=at_magic_comments..."
if ! "$SCRIPT_DIR/cerberus" --switches=at_magic_comments --json_core_out="$TMP_JSON" "$TEST_FILE" 2>&1; then
    echo "ERROR: Cerberus failed"
    exit 1
fi
echo "  JSON written to: $TMP_JSON"
echo ""

# Step 3: Check JSON for cn_magic content using Python
echo "Step 2: Checking JSON for cn_magic content..."
CN_MAGIC_INFO=$(python3 -c "
import json, sys
with open('$TMP_JSON') as f:
    data = json.load(f)
count = 0
for entry in data.get('funinfo', []):
    cn_magic = entry.get('cn_magic', [])
    if cn_magic:
        count += 1
        name = entry.get('symbol', {}).get('name', '<unknown>')
        print(f'  Function: {name}')
        for ann in cn_magic:
            text = ann.get('text', '')
            print(f'    Text: {repr(text[:60])}...' if len(text) > 60 else f'    Text: {repr(text)}')
print(f'TOTAL:{count}')
")
echo "$CN_MAGIC_INFO"
CN_MAGIC_COUNT=$(echo "$CN_MAGIC_INFO" | grep "^TOTAL:" | cut -d: -f2)

if [ "$CN_MAGIC_COUNT" -eq 0 ]; then
    echo ""
    echo "WARNING: No non-empty cn_magic arrays in JSON!"
    echo "This suggests Cerberus is not extracting the magic comments."
    exit 1
fi
echo ""

# Step 4: Build Lean project if needed
echo "Step 3: Building Lean project..."
cd "$LEAN_DIR"
if ! lake build 2>&1 | tail -5; then
    echo "ERROR: Lean build failed"
    exit 1
fi
echo ""

# Step 5: Run Lean test
echo "Step 4: Running Lean CN magic test..."
echo ""
lake env lean --run TestCnMagic.lean "$TMP_JSON"
LEAN_EXIT=$?
echo ""

if [ $LEAN_EXIT -ne 0 ]; then
    echo "ERROR: Lean test failed with exit code $LEAN_EXIT"
    exit 1
fi

echo "=== Test Complete ==="
