#!/bin/bash
# Find representative test files for each PP mismatch category
# Creates a problem_tests/ directory with categorized test files

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
CERBERUS_DIR="$PROJECT_DIR/cerberus"
LEAN_PP="$PROJECT_DIR/lean/.lake/build/bin/ctolean_pp"
CERBERUS="$CERBERUS_DIR/_build/install/default/bin/cerberus"
OUTPUT_DIR="$PROJECT_DIR/tests/problem_tests"

mkdir -p "$OUTPUT_DIR"

# Test directories to search (gcc-torture has more variety)
TEST_DIRS="$CERBERUS_DIR/tests/gcc-torture/execute"

echo "Finding problem tests..."
echo "========================"

# Initialize counters and category files
> "$OUTPUT_DIR/float_format.txt"
> "$OUTPUT_DIR/impl_brackets.txt"
> "$OUTPUT_DIR/long_double.txt"
> "$OUTPUT_DIR/fvfromint.txt"
> "$OUTPUT_DIR/null_type.txt"
> "$OUTPUT_DIR/flexible_array.txt"
> "$OUTPUT_DIR/other.txt"

count=0
max=500  # Check up to 500 files to find examples

for f in $(find "$TEST_DIRS" -name "*.c" ! -name "*.syntax-only.c" | sort | head -$max); do
    ((count++)) || true

    # Try to generate JSON and compare
    json_file=$(mktemp)
    cerb_pp=$(mktemp)

    if ! "$CERBERUS" --json_core_out="$json_file" "$f" 2>/dev/null; then
        rm -f "$json_file" "$cerb_pp"
        continue
    fi

    if ! "$CERBERUS" --pp=core --pp_core_compact "$f" > "$cerb_pp" 2>/dev/null; then
        rm -f "$json_file" "$cerb_pp"
        continue
    fi

    result=$("$LEAN_PP" "$json_file" --compare "$cerb_pp" 2>&1) || true

    if echo "$result" | grep -q "^✓"; then
        rm -f "$json_file" "$cerb_pp"
        continue
    fi

    # Categorize the mismatch
    basename=$(basename "$f" .c)

    if echo "$result" | grep -q "000000\|\.0\+[^0-9]"; then
        echo "$f" >> "$OUTPUT_DIR/float_format.txt"
    elif echo "$result" | grep -q "<[A-Z]"; then
        echo "$f" >> "$OUTPUT_DIR/impl_brackets.txt"
    elif echo "$result" | grep -q "long.double\|long_double"; then
        echo "$f" >> "$OUTPUT_DIR/long_double.txt"
    elif echo "$result" | grep -q "[CF]vfromint"; then
        echo "$f" >> "$OUTPUT_DIR/fvfromint.txt"
    elif echo "$result" | grep -q "NULL"; then
        echo "$f" >> "$OUTPUT_DIR/null_type.txt"
    elif echo "$result" | grep -q "char\[\]"; then
        echo "$f" >> "$OUTPUT_DIR/flexible_array.txt"
    else
        echo "$f" >> "$OUTPUT_DIR/other.txt"
        # Save the comparison output for "other" category
        echo "=== $basename ===" >> "$OUTPUT_DIR/other_details.txt"
        echo "$result" | head -10 >> "$OUTPUT_DIR/other_details.txt"
        echo "" >> "$OUTPUT_DIR/other_details.txt"
    fi

    rm -f "$json_file" "$cerb_pp"

    # Show progress
    if [ $((count % 100)) -eq 0 ]; then
        echo "Checked $count files..."
    fi
done

echo ""
echo "Results saved to $OUTPUT_DIR"
echo ""
echo "=== Category counts ==="
echo "Float formatting:        $(wc -l < "$OUTPUT_DIR/float_format.txt" | tr -d ' ')"
echo "Impl brackets:           $(wc -l < "$OUTPUT_DIR/impl_brackets.txt" | tr -d ' ')"
echo "long_double:             $(wc -l < "$OUTPUT_DIR/long_double.txt" | tr -d ' ')"
echo "Fvfromint:               $(wc -l < "$OUTPUT_DIR/fvfromint.txt" | tr -d ' ')"
echo "NULL type:               $(wc -l < "$OUTPUT_DIR/null_type.txt" | tr -d ' ')"
echo "Flexible array:          $(wc -l < "$OUTPUT_DIR/flexible_array.txt" | tr -d ' ')"
echo "Other:                   $(wc -l < "$OUTPUT_DIR/other.txt" | tr -d ' ')"
echo ""
echo "First file in each category:"
for cat in float_format impl_brackets long_double fvfromint null_type flexible_array other; do
    first=$(head -1 "$OUTPUT_DIR/$cat.txt" 2>/dev/null || echo "(none)")
    echo "  $cat: $(basename "$first" 2>/dev/null || echo "(none)")"
done
