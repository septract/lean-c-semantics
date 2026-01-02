#!/bin/bash
# Test PP against a specific category of problem files
# Usage: ./scripts/test_pp_category.sh <category>
#   Categories: float_format, impl_brackets, long_double, fvfromint, null_type, flexible_array, other, all

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
PROBLEM_DIR="$PROJECT_DIR/tests/problem_tests"
LEAN_PP="$PROJECT_DIR/lean/.lake/build/bin/ctolean_pp"
CERBERUS="$PROJECT_DIR/scripts/cerberus"

CATEGORY="${1:-all}"
VERBOSE="${2:---verbose}"

if [ "$CATEGORY" = "all" ]; then
    files=$(cat "$PROBLEM_DIR"/*.txt 2>/dev/null | grep -v "^$")
else
    file_list="$PROBLEM_DIR/$CATEGORY.txt"
    if [ ! -f "$file_list" ]; then
        echo "Unknown category: $CATEGORY"
        echo "Available: float_format, impl_brackets, long_double, fvfromint, null_type, flexible_array, other, all"
        exit 1
    fi
    files=$(cat "$file_list")
fi

if [ -z "$files" ]; then
    echo "No files in category: $CATEGORY"
    exit 0
fi

echo "Testing category: $CATEGORY"
echo "=========================="
echo ""

total=0
match=0
mismatch=0

while IFS= read -r f; do
    [ -z "$f" ] && continue
    ((total++)) || true

    basename=$(basename "$f" .c)
    json_file=$(mktemp)
    cerb_pp=$(mktemp)

    if ! "$CERBERUS" --json_core_out="$json_file" "$f" 2>/dev/null; then
        echo "[$total] $basename: CERBERUS_FAIL"
        rm -f "$json_file" "$cerb_pp"
        continue
    fi

    if ! "$CERBERUS" --pp=core --pp_core_compact "$f" > "$cerb_pp" 2>/dev/null; then
        echo "[$total] $basename: CERBERUS_PP_FAIL"
        rm -f "$json_file" "$cerb_pp"
        continue
    fi

    result=$("$LEAN_PP" "$json_file" --compare "$cerb_pp" 2>&1) || true

    if echo "$result" | grep -q "^✓"; then
        ((match++)) || true
        echo "[$total] $basename: ✓ MATCH"
    else
        ((mismatch++)) || true
        echo "[$total] $basename: ✗ MISMATCH"
        if [ "$VERBOSE" = "--verbose" ] || [ "$VERBOSE" = "-v" ]; then
            echo "$result" | grep -A3 "First difference" | head -4
            echo ""
        fi
    fi

    rm -f "$json_file" "$cerb_pp"
done <<< "$files"

echo ""
echo "=========================="
echo "Total: $total, Match: $match, Mismatch: $mismatch"
if [ $total -gt 0 ]; then
    rate=$((match * 100 / total))
    echo "Match rate: ${rate}%"
fi
