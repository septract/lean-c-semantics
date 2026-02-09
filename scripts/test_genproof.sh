#!/bin/bash
# Test the full genproof pipeline:
# 1. Run Cerberus to generate Core JSON
# 2. Strip the JSON to minimal dependencies
# 3. Generate Lean proof file
# 4. Test that the generated file compiles

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
set -euo pipefail

usage() {
    cat <<'EOF'
Test the full genproof pipeline on a C file.

Usage: ./scripts/test_genproof.sh [options] <input.c> [output_dir]

Arguments:
  input.c       C source file to process
  output_dir    Where to save output (default: auto temp dir)

Options:
  --nolibc       Use --nolibc with Cerberus (much smaller output)
  --no-strip     Skip the JSON stripping step
  --aggressive   Use aggressive stripping
  --keep         Keep intermediate files (don't clean up)
  --production   Output to lean/CerbLean/Verification/Programs/ with proper naming
  -v, --verbose  Show verbose output
  -h, --help     Show this help message

Examples:
  ./scripts/test_genproof.sh tests/minimal/001-return-literal.c
  ./scripts/test_genproof.sh --nolibc tests/minimal/001-return-literal.c
  ./scripts/test_genproof.sh tests/minimal/001-return-literal.c --production
EOF
    exit 0
}

# Parse arguments
NO_STRIP=false
AGGRESSIVE=false
KEEP=false
VERBOSE=false
NOLIBC=false
PRODUCTION=false
INPUT_FILE=""
OUTPUT_DIR=""

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help) usage ;;
        --nolibc)
            NOLIBC=true
            shift
            ;;
        --no-strip)
            NO_STRIP=true
            shift
            ;;
        --aggressive)
            AGGRESSIVE=true
            shift
            ;;
        --keep)
            KEEP=true
            shift
            ;;
        --production)
            PRODUCTION=true
            KEEP=true  # Always keep production files
            shift
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
            if [[ -z "$INPUT_FILE" ]]; then
                INPUT_FILE="$1"
            elif [[ -z "$OUTPUT_DIR" ]]; then
                OUTPUT_DIR="$1"
            else
                echo "Error: Too many arguments" >&2
                usage
            fi
            shift
            ;;
    esac
done

if [[ -z "$INPUT_FILE" ]]; then
    usage
fi

if [[ ! -f "$INPUT_FILE" ]]; then
    echo -e "${RED}Error: Input file not found: $INPUT_FILE${NC}" >&2
    exit 1
fi

# Build required targets
build_lean cerblean_test
build_lean cerblean_genproof

# Convert basename to PascalCase module name (portable, no GNU awk needed)
to_module_name() {
    local name="${1%.c}"
    local IFS='-_'
    local result=""
    local word first_char
    for word in $name; do
        if [[ -n "$word" ]]; then
            first_char=$(printf '%s' "${word:0:1}" | tr '[:lower:]' '[:upper:]')
            result+="${first_char}${word:1}"
        fi
    done
    printf '%s\n' "$result"
}

# Set up output directory
BASENAME=$(basename "$INPUT_FILE" .c)
MODULE_NAME=$(to_module_name "$BASENAME")

if [[ "$PRODUCTION" == "true" ]]; then
    OUTPUT_DIR="$LEAN_DIR/CerbLean/Verification/Programs"
    LEAN_FILE="$OUTPUT_DIR/${MODULE_NAME}.lean"
    echo -e "${YELLOW}Production mode: outputting to $LEAN_FILE${NC}"
elif [[ -z "$OUTPUT_DIR" ]]; then
    OUTPUT_DIR=$(make_temp_dir "genproof")
    if ! $KEEP; then
        register_cleanup "$OUTPUT_DIR"
    fi
fi
mkdir -p "$OUTPUT_DIR"

JSON_FILE="$OUTPUT_DIR/${BASENAME}.json"
STRIPPED_FILE="$OUTPUT_DIR/${BASENAME}_stripped.json"
if [[ "$PRODUCTION" != "true" ]]; then
    LEAN_FILE="$OUTPUT_DIR/${BASENAME}_proof.lean"
fi

log() {
    if $VERBOSE; then
        echo -e "$1"
    fi
}

# Step 1: Run Cerberus to generate JSON
echo -e "${YELLOW}[1/4] Running Cerberus...${NC}"
CERBERUS_ARGS=("--json_core_out=$JSON_FILE")
if $NOLIBC; then
    CERBERUS_ARGS+=("--nolibc")
fi
log "  cerberus ${CERBERUS_ARGS[*]} $INPUT_FILE"
if ! "$CERBERUS" "${CERBERUS_ARGS[@]}" "$INPUT_FILE" 2>/dev/null; then
    echo -e "${RED}FAILED: Cerberus failed to process $INPUT_FILE${NC}"
    exit 1
fi
JSON_SIZE=$(wc -c < "$JSON_FILE" | tr -d ' ')
log "  Generated: $JSON_FILE ($JSON_SIZE bytes)"

# Step 2: Strip the JSON (optional)
if ! $NO_STRIP; then
    echo -e "${YELLOW}[2/4] Stripping JSON...${NC}"
    STRIP_ARGS=()
    if $AGGRESSIVE; then
        STRIP_ARGS+=("--aggressive")
    fi
    log "  python3 strip_core_json.py ${STRIP_ARGS[*]+"${STRIP_ARGS[*]}"} $JSON_FILE $STRIPPED_FILE"
    if ! python3 "$SCRIPT_DIR/strip_core_json.py" ${STRIP_ARGS[@]+"${STRIP_ARGS[@]}"} "$JSON_FILE" "$STRIPPED_FILE" 2>/dev/null; then
        echo -e "${RED}FAILED: JSON stripping failed${NC}"
        exit 1
    fi
    STRIPPED_SIZE=$(wc -c < "$STRIPPED_FILE" | tr -d ' ')
    PERCENT=$(echo "scale=1; $STRIPPED_SIZE * 100 / $JSON_SIZE" | bc)
    log "  Stripped: $STRIPPED_FILE ($STRIPPED_SIZE bytes, $PERCENT%)"
    FINAL_JSON="$STRIPPED_FILE"
else
    echo -e "${YELLOW}[2/4] Skipping JSON stripping${NC}"
    FINAL_JSON="$JSON_FILE"
fi

# Step 3: Verify stripped JSON runs with interpreter
echo -e "${YELLOW}[3/4] Verifying JSON with interpreter...${NC}"
log "  cerblean_test $FINAL_JSON"
INTERP_OUTPUT=$("$LEAN_DIR/.lake/build/bin/cerblean_test" "$FINAL_JSON" 2>&1) || true
if echo "$INTERP_OUTPUT" | grep -q "Error"; then
    echo -e "${YELLOW}  Warning: Interpreter reported error (may be expected for some tests)${NC}"
    log "  $INTERP_OUTPUT"
fi

# Step 4: Generate Lean proof file
echo -e "${YELLOW}[4/4] Generating Lean proof file...${NC}"
log "  cerblean_genproof $FINAL_JSON $LEAN_FILE"
if ! "$LEAN_DIR/.lake/build/bin/cerblean_genproof" "$FINAL_JSON" "$LEAN_FILE" 2>&1; then
    echo -e "${RED}FAILED: genproof failed${NC}"
    exit 1
fi
LEAN_SIZE=$(wc -c < "$LEAN_FILE" | tr -d ' ')
log "  Generated: $LEAN_FILE ($LEAN_SIZE bytes)"

# Step 5: Test that the generated file compiles
echo -e "${YELLOW}[5/5] Testing Lean compilation...${NC}"
log "  lake env lean $LEAN_FILE"

compile_output=$(cd "$LEAN_DIR" && lake env lean "$LEAN_FILE" 2>&1) || true
echo "$compile_output" | head -20

if echo "$compile_output" | grep -q "error:"; then
    echo -e "${RED}FAILED: Generated Lean file has errors${NC}"
    echo ""
    echo "Output file: $LEAN_FILE"
    exit 1
else
    echo -e "${GREEN}SUCCESS: Generated Lean file compiles${NC}"
fi

echo ""
echo "Output files:"
echo "  JSON: $JSON_FILE"
if ! $NO_STRIP; then
    echo "  Stripped: $STRIPPED_FILE"
fi
echo "  Lean: $LEAN_FILE"

if $KEEP; then
    echo ""
    echo "Files kept in: $OUTPUT_DIR"
fi
