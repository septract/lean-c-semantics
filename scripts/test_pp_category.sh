#!/bin/bash
# Test PP against a specific category of problem files
#
# Usage: ./scripts/test_pp_category.sh [options] [category]
#
# Categories: float_format, impl_brackets, long_double, fvfromint,
#             null_type, flexible_array, other, all

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
set -euo pipefail

usage() {
    cat <<'EOF'
Test pretty-printer against a specific category of problem files.

Usage: ./scripts/test_pp_category.sh [options] [category]

Categories:
  float_format     Floating-point formatting mismatches
  impl_brackets    Implementation bracket differences
  long_double      Long double type issues
  fvfromint        Fvfromint conversion issues
  null_type        NULL type parsing issues
  flexible_array   Flexible array member issues
  other            Uncategorized mismatches
  all              All categories (default)

Options:
  -v, --verbose    Show detailed mismatch info
  -h, --help       Show this help message

Examples:
  ./scripts/test_pp_category.sh null_type
  ./scripts/test_pp_category.sh --verbose float_format
  ./scripts/test_pp_category.sh all
EOF
    exit 0
}

PROBLEM_DIR="$PROJECT_ROOT/tests/problem_tests"
LEAN_PP="$LEAN_DIR/.lake/build/bin/cerblean_pp"

# Parse arguments
CATEGORY="all"
VERBOSE=false

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help) usage ;;
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
            CATEGORY="$1"
            shift
            ;;
    esac
done

# Collect files from category
files=""
if [[ "$CATEGORY" == "all" ]]; then
    files=$(cat "$PROBLEM_DIR"/*.txt 2>/dev/null | grep -v "^$" || true)
else
    file_list="$PROBLEM_DIR/$CATEGORY.txt"
    if [[ ! -f "$file_list" ]]; then
        echo "Unknown category: $CATEGORY" >&2
        echo "Available: float_format, impl_brackets, long_double, fvfromint, null_type, flexible_array, other, all" >&2
        exit 1
    fi
    files=$(cat "$file_list")
fi

if [[ -z "$files" ]]; then
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
    [[ -z "$f" ]] && continue
    total=$((total + 1))

    basename=$(basename "$f" .c)
    json_file=$(mktemp "$TMP_DIR/pp-cat-json.XXXXXXXXXX")
    cerb_pp=$(mktemp "$TMP_DIR/pp-cat-cerb.XXXXXXXXXX")
    register_cleanup "$json_file"
    register_cleanup "$cerb_pp"

    if ! "$CERBERUS" --json_core_out="$json_file" "$f" 2>/dev/null; then
        echo "[$total] $basename: CERBERUS_FAIL"
        continue
    fi

    if ! "$CERBERUS" --pp=core --pp_core_compact "$f" > "$cerb_pp" 2>/dev/null; then
        echo "[$total] $basename: CERBERUS_PP_FAIL"
        continue
    fi

    result=$("$LEAN_PP" "$json_file" --compare "$cerb_pp" 2>&1) || true

    if echo "$result" | grep -q "^✓"; then
        match=$((match + 1))
        echo -e "[$total] $basename: ${GREEN}MATCH${NC}"
    else
        mismatch=$((mismatch + 1))
        echo -e "[$total] $basename: ${RED}MISMATCH${NC}"
        if $VERBOSE; then
            echo "$result" | grep -A3 "First difference" | head -4
            echo ""
        fi
    fi
done <<< "$files"

echo ""
echo "=========================="
echo "Total: $total, Match: $match, Mismatch: $mismatch"
if [[ $total -gt 0 ]]; then
    rate=$((match * 100 / total))
    echo "Match rate: ${rate}%"
fi
