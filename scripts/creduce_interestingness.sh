#!/bin/bash
# Interestingness test for creduce
# Returns 0 if Lean reports UB but Cerberus succeeds (the bug we want to isolate)
#
# Usage: creduce ./scripts/creduce_interestingness.sh test.c

PROJECT=/Users/miked/Projects/c-to-lean
CERBERUS="$PROJECT/scripts/cerberus"
INTERP="$PROJECT/lean/.lake/build/bin/ctolean_interp"

# Timeout in seconds (creduce can create infinite loops)
TIMEOUT=10

# The file being reduced (creduce passes it as working directory file)
TEST_FILE="${1:-stdarg-1.c}"

# Run Cerberus with timeout
CERB_OUT=$(timeout $TIMEOUT $CERBERUS --exec --batch "$TEST_FILE" 2>&1)
CERB_EXIT=$?

# Skip if Cerberus fails or times out
if [ $CERB_EXIT -ne 0 ]; then
    exit 1
fi

# Check if Cerberus returned 0
if ! echo "$CERB_OUT" | grep -q 'value: "Specified(0)"'; then
    exit 1
fi

# Generate JSON with timeout
timeout $TIMEOUT $CERBERUS --json_core_out=test.json "$TEST_FILE" 2>&1 >/dev/null
if [ $? -ne 0 ]; then
    exit 1
fi

# Run our interpreter with timeout
LEAN_OUT=$(timeout $TIMEOUT $INTERP test.json 2>&1)

# Check if Lean reports UB (out of bounds)
if echo "$LEAN_OUT" | grep -q "out of bounds"; then
    exit 0  # Interesting - bug reproduced
fi

exit 1  # Not interesting
