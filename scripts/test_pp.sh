#!/bin/bash
# Test the Lean pretty-printer against Cerberus pretty-printer output
#
# Usage: ./scripts/test_pp.sh [options] [test_dir]

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
set -euo pipefail

usage() {
    cat <<'EOF'
Test the Lean pretty-printer against Cerberus pretty-printer output.

Usage: ./scripts/test_pp.sh [options] [test_dir]

Arguments:
  test_dir      Directory containing .c files (default: cerberus/tests)

Options:
  --quick        Test first 50 files only
  --max N        Test first N files
  -v, --verbose  Show per-file results
  -h, --help     Show this help message

Examples:
  ./scripts/test_pp.sh --quick
  ./scripts/test_pp.sh --max 100 -v
  ./scripts/test_pp.sh cerberus/tests/ci
EOF
    exit 0
}

# Configuration
QUICK_MODE=false
VERBOSE=false
TEST_DIR=""
MAX_TESTS=0  # 0 = unlimited

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help) usage ;;
        --quick)
            QUICK_MODE=true
            MAX_TESTS=50
            shift
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        --max)
            MAX_TESTS="$2"
            shift 2
            ;;
        -*)
            echo "Unknown option: $1" >&2
            echo "Use --help for usage information" >&2
            exit 1
            ;;
        *)
            TEST_DIR="$1"
            shift
            ;;
    esac
done

# Default test directory
if [[ -z "$TEST_DIR" ]]; then
    TEST_DIR="$CERBERUS_DIR/tests"
fi

# Check prerequisites
require_cerberus

# Build Lean pretty-printer
build_lean cerblean_pp

# Create output directory
OUTPUT_DIR=$(make_temp_dir "pp-test")
register_cleanup "$OUTPUT_DIR"
ERROR_LOG="$OUTPUT_DIR/errors.log"
DIFF_LOG="$OUTPUT_DIR/diffs.log"
> "$ERROR_LOG"
> "$DIFF_LOG"

# Counters
total=0
cerberus_success=0
cerberus_fail=0
pp_match=0
pp_mismatch=0

# Find all .c files (excluding syntax-only tests) into an array
echo ""
echo "Finding test files in $TEST_DIR..."
test_files=()
while IFS= read -r f; do
    test_files+=("$f")
done < <(find "$TEST_DIR" -name "*.c" ! -name "*.syntax-only.c" | sort)
total_available=${#test_files[@]}
echo "Found $total_available test files"

if $QUICK_MODE; then
    echo "Quick mode: testing first $MAX_TESTS files"
fi

echo ""
echo "Running pretty-printer comparison..."
echo "===================================="

start_time=$(date +%s)

# Process each file
for cfile in "${test_files[@]}"; do
    # Check max tests
    if [[ $MAX_TESTS -gt 0 && $total -ge $MAX_TESTS ]]; then
        break
    fi

    total=$((total + 1))

    # Generate unique name for output
    basename_c=$(basename "$cfile" .c)
    hash=$(portable_hash "$cfile")
    json_file="$OUTPUT_DIR/${basename_c}_${hash}.json"
    cerberus_pp="$OUTPUT_DIR/${basename_c}_${hash}.cerberus.core"
    lean_pp="$OUTPUT_DIR/${basename_c}_${hash}.lean.core"

    if $VERBOSE; then
        echo -n "[$total] $basename_c ... "
    fi

    # Run Cerberus to generate JSON
    cerberus_err_file=$(mktemp "$TMP_DIR/cerb-err.XXXXXXXXXX")
    register_cleanup "$cerberus_err_file"
    if ! "$CERBERUS" --json_core_out="$json_file" "$cfile" 2>"$cerberus_err_file"; then
        cerberus_fail=$((cerberus_fail + 1))
        if $VERBOSE; then
            echo "CERBERUS_FAIL"
        fi
        continue
    fi

    # Run Cerberus to generate pretty-printed output (compact mode for easy comparison)
    if ! "$CERBERUS" --pp=core --pp_core_compact "$cfile" > "$cerberus_pp" 2>/dev/null; then
        cerberus_fail=$((cerberus_fail + 1))
        if $VERBOSE; then
            echo "CERBERUS_PP_FAIL"
        fi
        continue
    fi

    cerberus_success=$((cerberus_success + 1))

    # Run Lean pretty-printer
    if ! "$LEAN_DIR/.lake/build/bin/cerblean_pp" "$json_file" > "$lean_pp" 2>/dev/null; then
        echo "$cfile: Lean pretty-printer failed" >> "$ERROR_LOG"
        if $VERBOSE; then
            echo "LEAN_PP_FAIL"
        fi
        continue
    fi

    # Compare outputs using the Lean comparison tool
    result=$("$LEAN_DIR/.lake/build/bin/cerblean_pp" "$json_file" --compare "$cerberus_pp" 2>&1) || true

    if echo "$result" | grep -q "^✓"; then
        pp_match=$((pp_match + 1))
        if $VERBOSE; then
            echo -e "${GREEN}MATCH${NC}"
        fi
    else
        pp_mismatch=$((pp_mismatch + 1))
        # Log the first difference
        diff_info=$(echo "$result" | grep "First difference" | head -1)
        echo "$basename_c: $diff_info" >> "$DIFF_LOG"
        if $VERBOSE; then
            echo -e "${RED}MISMATCH${NC}"
            echo "$result" | grep -A2 "First difference" | head -3
        fi
    fi

    # Progress indicator (every 100 files)
    if ! $VERBOSE && [[ $((total % 100)) -eq 0 ]]; then
        now=$(date +%s)
        elapsed=$((now - start_time))
        elapsed_safe=$((elapsed > 0 ? elapsed : 1))
        target=$((MAX_TESTS > 0 ? MAX_TESTS : total_available))
        pct=$((total * 100 / target))
        echo "  [$total/$target] ${pct}% | match: $pp_match mismatch: $pp_mismatch | ${elapsed}s elapsed"
    fi
done

end_time=$(date +%s)
total_elapsed=$((end_time - start_time))

echo ""
echo ""
echo "===================================="
echo "Results Summary"
echo "===================================="
echo ""
echo "Total time:             ${total_elapsed}s"
echo ""
echo "Total files tested:     $total"
echo ""
echo "Cerberus stage:"
echo "  Success:              $cerberus_success"
echo "  Failed:               $cerberus_fail"
echo ""
echo "Pretty-printer comparison (of Cerberus successes):"
echo "  Match:                $pp_match"
echo "  Mismatch:             $pp_mismatch"
echo ""

if [[ $cerberus_success -gt 0 ]]; then
    match_rate=$((pp_match * 100 / cerberus_success))
    echo "Match rate:             ${match_rate}%"
fi

echo ""

# Show first few mismatches
if [[ -s "$DIFF_LOG" ]]; then
    echo "First differences found:"
    echo "------------------------"
    head -10 "$DIFF_LOG"
    echo ""
fi

echo "Output files saved to: $OUTPUT_DIR"
echo "  - JSON files: *.json"
echo "  - Cerberus output: *.cerberus.core"
echo "  - Lean output: *.lean.core"
echo "Diff log: $DIFF_LOG"

# Show how to investigate a mismatch
if [[ $pp_mismatch -gt 0 ]]; then
    first_mismatch=$(head -1 "$DIFF_LOG" | cut -d: -f1)
    echo ""
    echo "To investigate a mismatch, e.g. '$first_mismatch':"
    echo "  diff $OUTPUT_DIR/${first_mismatch}_*.cerberus.core $OUTPUT_DIR/${first_mismatch}_*.lean.core"
    echo ""
    echo -e "${RED}FAILED: $pp_mismatch pretty-printer mismatch(es)${NC}"
    exit 1
fi
