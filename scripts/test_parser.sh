#!/bin/bash
# Test the Lean JSON parser against Cerberus test suite
# Usage: ./scripts/test_parser.sh [--quick] [--verbose] [test_dir]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
CERBERUS_DIR="$PROJECT_DIR/cerberus"
LEAN_DIR="$PROJECT_DIR/lean"

# Cerberus requires OCaml 4.14.1 (crashes on OCaml 5.x)
OPAM_SWITCH="cerberus-414"
CERBERUS="OPAMSWITCH=$OPAM_SWITCH opam exec -- cerberus"

# Configuration
QUICK_MODE=false
VERBOSE=false
TEST_DIR=""
MAX_TESTS=0  # 0 = unlimited
OUTPUT_DIR=$(mktemp -d "${TMPDIR:-/tmp}/c-to-lean-test.XXXXXXXXXX")
ERROR_LOG="$OUTPUT_DIR/errors.log"

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --quick)
            QUICK_MODE=true
            MAX_TESTS=50
            shift
            ;;
        --verbose|-v)
            VERBOSE=true
            shift
            ;;
        --max)
            MAX_TESTS=$2
            shift 2
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

# Check prerequisites - verify opam switch exists
if ! opam switch list 2>/dev/null | grep -q "$OPAM_SWITCH"; then
    echo "Error: opam switch '$OPAM_SWITCH' not found"
    echo "Run 'make cerberus-setup' first"
    exit 1
fi

# Build Lean parser
echo "Building Lean parser..."
cd "$LEAN_DIR"
lake build ctolean_testbatch 2>&1 | tail -5

# Create output directory
mkdir -p "$OUTPUT_DIR"
> "$ERROR_LOG"  # Clear error log
CERBERUS_ERROR_LOG="$OUTPUT_DIR/cerberus_errors.log"
> "$CERBERUS_ERROR_LOG"  # Clear cerberus error log

# Counters
total=0
cerberus_success=0
cerberus_fail=0
parse_success=0
parse_fail=0

# Find all .c files (excluding syntax-only tests)
echo ""
echo "Finding test files in $TEST_DIR..."
test_files=$(find "$TEST_DIR" -name "*.c" ! -name "*.syntax-only.c" | sort)
total_available=$(echo "$test_files" | wc -l | tr -d ' ')
echo "Found $total_available test files"

if [[ "$QUICK_MODE" == "true" ]]; then
    echo "Quick mode: testing first $MAX_TESTS files"
fi

echo ""
echo "Running tests..."
echo "================"

start_time=$(date +%s)

# Process each file
while IFS= read -r cfile; do
    # Check max tests
    if [[ $MAX_TESTS -gt 0 && $total -ge $MAX_TESTS ]]; then
        break
    fi

    ((total++)) || true

    # Generate unique name for output
    basename=$(basename "$cfile" .c)
    hash=$(echo "$cfile" | md5 | cut -c1-8)
    json_file="$OUTPUT_DIR/${basename}_${hash}.json"

    if [[ "$VERBOSE" == "true" ]]; then
        echo -n "[$total] $cfile ... "
    fi

    # Run Cerberus to generate JSON
    cerberus_err_file=$(mktemp)
    if ! eval $CERBERUS --json_core_out="$json_file" "$cfile" 2>"$cerberus_err_file"; then
        ((cerberus_fail++)) || true
        # Log the error
        cerberus_err=$(head -1 "$cerberus_err_file")
        echo "$cfile: $cerberus_err" >> "$CERBERUS_ERROR_LOG"
        rm -f "$cerberus_err_file"
        if [[ "$VERBOSE" == "true" ]]; then
            echo "CERBERUS_FAIL: $cerberus_err"
        fi
        continue
    fi
    rm -f "$cerberus_err_file"

    ((cerberus_success++)) || true

    # Check if JSON was created
    if [[ ! -f "$json_file" ]]; then
        ((cerberus_fail++)) || true
        if [[ "$VERBOSE" == "true" ]]; then
            echo "NO_JSON"
        fi
        continue
    fi

    # Run Lean parser
    result=$("$LEAN_DIR/.lake/build/bin/ctolean_testbatch" "$json_file" 2>&1)

    if echo "$result" | grep -q "^✓"; then
        ((parse_success++)) || true
        if [[ "$VERBOSE" == "true" ]]; then
            echo "OK"
        fi
    else
        ((parse_fail++)) || true
        # Log error for later analysis - extract everything after the filename
        error_msg=$(echo "$result" | grep "^✗" | sed 's/^✗ [^:]*: //' | head -1)
        echo "$cfile: $error_msg" >> "$ERROR_LOG"
        if [[ "$VERBOSE" == "true" ]]; then
            echo "PARSE_FAIL: $error_msg"
        fi
    fi

    # Progress indicator (every 100 files)
    if [[ "$VERBOSE" != "true" && $((total % 100)) -eq 0 ]]; then
        now=$(date +%s)
        elapsed=$((now - start_time))
        rate=$((total * 10 / (elapsed > 0 ? elapsed : 1)))  # files per 10 seconds
        target=$((MAX_TESTS > 0 ? MAX_TESTS : total_available))
        pct=$((total * 100 / target))
        remaining=$(( (target - total) * 10 / (rate > 0 ? rate : 1) ))
        echo "  [$total/$target] ${pct}% | cerberus: $cerberus_success/$cerberus_fail | parser: $parse_success/$parse_fail | ${elapsed}s elapsed, ~${remaining}s remaining"
    fi

done <<< "$test_files"

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
    # Extract error category: strip source file, then strip line:col:, then normalize
    # e.g., "/path/file.c: /other/path.c:10:8: error: foo bar" -> "error: foo bar"
    sed 's/^[^:]*\.c: //' "$CERBERUS_ERROR_LOG" | \
        sed 's/^[^:]*:[0-9]*:[0-9]*: //' | \
        sed "s/'[^']*'/'...'/g" | \
        sort | uniq -c | sort -rn | head -10 | while read count err; do
        # Find an example file for this error pattern
        example=$(grep -m1 "" "$CERBERUS_ERROR_LOG" | head -1 | cut -d: -f1)
        example_short=$(basename "$example" 2>/dev/null || echo "unknown")
        printf "%5d  %-50s\n" "$count" "$err"
    done
    echo ""
fi

# Show parser error categories if there are failures
if [[ -s "$ERROR_LOG" ]]; then
    echo "Top parser error categories:"
    echo "----------------------------"
    # Extract just the error message (everything after the .c: )
    sed 's/^[^:]*\.c: //' "$ERROR_LOG" | sort | uniq -c | sort -rn | head -10 | while read count err; do
        example=$(grep -F ": ${err}" "$ERROR_LOG" | head -1 | sed 's/: .*//')
        example_short=$(basename "$example")
        printf "%5d  %-50s  (e.g. %s)\n" "$count" "$err" "$example_short"
    done
    echo ""
fi

echo "JSON files saved to: $OUTPUT_DIR"
echo "Parser error log: $ERROR_LOG"
echo "Cerberus error log: $CERBERUS_ERROR_LOG"
