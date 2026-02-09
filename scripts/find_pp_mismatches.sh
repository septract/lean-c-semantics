#!/bin/bash
# Find representative test files for each PP mismatch category
# Creates a problem_tests/ directory with categorized test files
#
# Usage: ./scripts/find_pp_mismatches.sh [options]

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
set -euo pipefail

usage() {
    cat <<'EOF'
Find representative test files for each PP mismatch category.

Usage: ./scripts/find_pp_mismatches.sh [options]

Options:
  --max N        Check up to N files (default: 500)
  -v, --verbose  Show each file as it's checked
  -h, --help     Show this help message

Output is saved to tests/problem_tests/ with one file per category.
EOF
    exit 0
}

LEAN_PP="$LEAN_DIR/.lake/build/bin/cerblean_pp"
OUTPUT_DIR="$PROJECT_ROOT/tests/problem_tests"

# Parse arguments
MAX_FILES=500
VERBOSE=false

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help) usage ;;
        --max)
            MAX_FILES="$2"
            shift 2
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
            echo "Unexpected argument: $1" >&2
            exit 1
            ;;
    esac
done

mkdir -p "$OUTPUT_DIR"

# Test directories to search (gcc-torture has more variety)
TEST_DIRS="$CERBERUS_DIR/tests/gcc-torture/execute"

echo "Finding problem tests..."
echo "========================"

# Initialize category files
> "$OUTPUT_DIR/float_format.txt"
> "$OUTPUT_DIR/impl_brackets.txt"
> "$OUTPUT_DIR/long_double.txt"
> "$OUTPUT_DIR/fvfromint.txt"
> "$OUTPUT_DIR/null_type.txt"
> "$OUTPUT_DIR/flexible_array.txt"
> "$OUTPUT_DIR/other.txt"

# Collect test files into array
test_files=()
while IFS= read -r f; do
    test_files+=("$f")
done < <(find "$TEST_DIRS" -name "*.c" ! -name "*.syntax-only.c" | sort | head -n "$MAX_FILES")

count=0
for f in "${test_files[@]}"; do
    count=$((count + 1))

    # Try to generate JSON and compare
    json_file=$(mktemp "$TMP_DIR/find-prob-json.XXXXXXXXXX")
    cerb_pp=$(mktemp "$TMP_DIR/find-prob-cerb.XXXXXXXXXX")
    register_cleanup "$json_file"
    register_cleanup "$cerb_pp"

    if ! "$CERBERUS" --json_core_out="$json_file" "$f" 2>/dev/null; then
        continue
    fi

    if ! "$CERBERUS" --pp=core --pp_core_compact "$f" > "$cerb_pp" 2>/dev/null; then
        continue
    fi

    result=$("$LEAN_PP" "$json_file" --compare "$cerb_pp" 2>&1) || true

    if echo "$result" | grep -q "^✓"; then
        if $VERBOSE; then
            echo "[$count] $(basename "$f"): MATCH"
        fi
        continue
    fi

    # Categorize the mismatch
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
        echo "=== $(basename "$f" .c) ===" >> "$OUTPUT_DIR/other_details.txt"
        echo "$result" | head -10 >> "$OUTPUT_DIR/other_details.txt"
        echo "" >> "$OUTPUT_DIR/other_details.txt"
    fi

    if $VERBOSE; then
        echo "[$count] $(basename "$f"): MISMATCH"
    fi

    # Show progress
    if [[ $((count % 100)) -eq 0 ]]; then
        echo "Checked $count files..."
    fi
done

echo ""
echo "Results saved to $OUTPUT_DIR"
echo ""
echo "=== Category counts ==="
for cat in float_format impl_brackets long_double fvfromint null_type flexible_array other; do
    count=$(wc -l < "$OUTPUT_DIR/$cat.txt" | tr -d ' ')
    printf "  %-20s %s\n" "$cat:" "$count"
done
echo ""
echo "First file in each category:"
for cat in float_format impl_brackets long_double fvfromint null_type flexible_array other; do
    first=$(head -1 "$OUTPUT_DIR/$cat.txt" 2>/dev/null || echo "(none)")
    echo "  $cat: $(basename "$first" 2>/dev/null || echo "(none)")"
done
