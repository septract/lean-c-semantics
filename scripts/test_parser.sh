#!/bin/bash
# Test the Lean JSON parser against Cerberus test suite
#
# Usage: ./scripts/test_parser.sh [options] [test_dir]

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
set -euo pipefail

usage() {
    cat <<'EOF'
Test the Lean JSON parser against Cerberus test suite.

Usage: ./scripts/test_parser.sh [options] [test_dir]

Arguments:
  test_dir      Directory containing .c files (default: cerberus/tests)

Options:
  --quick        Test first 50 files only
  --max N        Test first N files
  -v, --verbose  Show per-file results
  -h, --help     Show this help message

Examples:
  ./scripts/test_parser.sh --quick
  ./scripts/test_parser.sh --max 500
  ./scripts/test_parser.sh cerberus/tests/ci
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

# Build Lean parser
build_lean cerblean_testbatch

# Create output directory
OUTPUT_DIR=$(make_temp_dir "parser-test")
register_cleanup "$OUTPUT_DIR"
ERROR_LOG="$OUTPUT_DIR/errors.log"
CERBERUS_ERROR_LOG="$OUTPUT_DIR/cerberus_errors.log"
> "$ERROR_LOG"
> "$CERBERUS_ERROR_LOG"

# Counters
total=0
cerberus_success=0
cerberus_fail=0
parse_success=0
parse_fail=0

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
echo "Running tests..."
echo "================"

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

    if $VERBOSE; then
        echo -n "[$total] $cfile ... "
    fi

    # Run Cerberus to generate JSON
    cerberus_err_file=$(mktemp "$TMP_DIR/cerb-err.XXXXXXXXXX")
    register_cleanup "$cerberus_err_file"
    if ! "$CERBERUS" --json_core_out="$json_file" "$cfile" 2>"$cerberus_err_file"; then
        cerberus_fail=$((cerberus_fail + 1))
        # Log the error
        cerberus_err=$(head -1 "$cerberus_err_file")
        echo "$cfile: $cerberus_err" >> "$CERBERUS_ERROR_LOG"
        if $VERBOSE; then
            echo "CERBERUS_FAIL: $cerberus_err"
        fi
        continue
    fi

    cerberus_success=$((cerberus_success + 1))

    # Check if JSON was created
    if [[ ! -f "$json_file" ]]; then
        cerberus_fail=$((cerberus_fail + 1))
        if $VERBOSE; then
            echo "NO_JSON"
        fi
        continue
    fi

    # Run Lean parser
    result=$("$LEAN_DIR/.lake/build/bin/cerblean_testbatch" "$json_file" 2>&1) || true

    if echo "$result" | grep -q "^✓"; then
        parse_success=$((parse_success + 1))
        if $VERBOSE; then
            echo "OK"
        fi
    else
        parse_fail=$((parse_fail + 1))
        # Log error for later analysis
        error_msg=$(echo "$result" | grep "^✗" | sed 's/^✗ [^:]*: //' | head -1)
        echo "$cfile: $error_msg" >> "$ERROR_LOG"
        if $VERBOSE; then
            echo "PARSE_FAIL: $error_msg"
        fi
    fi

    # Progress indicator (every 100 files)
    if ! $VERBOSE && [[ $((total % 100)) -eq 0 ]]; then
        now=$(date +%s)
        elapsed=$((now - start_time))
        elapsed_safe=$((elapsed > 0 ? elapsed : 1))
        rate=$((total * 10 / elapsed_safe))
        target=$((MAX_TESTS > 0 ? MAX_TESTS : total_available))
        pct=$((total * 100 / target))
        rate_safe=$((rate > 0 ? rate : 1))
        remaining=$(( (target - total) * 10 / rate_safe ))
        echo "  [$total/$target] ${pct}% | cerberus: $cerberus_success/$cerberus_fail | parser: $parse_success/$parse_fail | ${elapsed}s elapsed, ~${remaining}s remaining"
    fi
done

end_time=$(date +%s)
total_elapsed=$((end_time - start_time))

echo ""
echo ""
echo "================"
echo "Results Summary"
echo "================"
echo ""
echo "Total time:             ${total_elapsed}s"
echo ""
echo "Total files tested:     $total"
echo ""
echo "Cerberus stage:"
echo "  Success:              $cerberus_success"
echo "  Failed:               $cerberus_fail"
echo ""
echo "Parser stage (of Cerberus successes):"
echo "  Success:              $parse_success"
echo "  Failed:               $parse_fail"
echo ""

if [[ $cerberus_success -gt 0 ]]; then
    parse_rate=$((parse_success * 100 / cerberus_success))
    echo "Parse success rate:     ${parse_rate}%"
fi

echo ""

# Show Cerberus error categories if there are failures
if [[ -s "$CERBERUS_ERROR_LOG" ]]; then
    echo "Top Cerberus error categories:"
    echo "------------------------------"
    sed 's/^[^:]*\.c: //' "$CERBERUS_ERROR_LOG" | \
        sed 's/^[^:]*:[0-9]*:[0-9]*: //' | \
        sed "s/'[^']*'/'...'/g" | \
        sort | uniq -c | sort -rn | head -10 | while IFS= read -r line; do
        printf "  %s\n" "$line"
    done
    echo ""
fi

# Show parser error categories if there are failures
if [[ -s "$ERROR_LOG" ]]; then
    echo "Top parser error categories:"
    echo "----------------------------"
    sed 's/^[^:]*\.c: //' "$ERROR_LOG" | sort | uniq -c | sort -rn | head -10 | while IFS= read -r line; do
        printf "  %s\n" "$line"
    done
    echo ""
fi

echo "JSON files saved to: $OUTPUT_DIR"
echo "Parser error log: $ERROR_LOG"
echo "Cerberus error log: $CERBERUS_ERROR_LOG"

# Exit with failure if there were parser errors
if [[ $parse_fail -gt 0 ]]; then
    echo ""
    echo -e "${RED}FAILED: $parse_fail parser error(s)${NC}"
    exit 1
fi
