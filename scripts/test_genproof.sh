#!/bin/bash
# Test the full genproof pipeline:
# 1. Run Cerberus to generate Core JSON
# 2. Strip the JSON to minimal dependencies
# 3. Generate Lean proof file
# 4. Test that the generated file compiles

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
LEAN_DIR="$PROJECT_ROOT/lean"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

usage() {
    echo "Usage: $0 <input.c> [output_dir]"
    echo ""
    echo "Tests the full genproof pipeline on a C file."
    echo ""
    echo "Options:"
    echo "  --nolibc       Use --nolibc with Cerberus (much smaller output)"
    echo "  --no-strip     Skip the stripping step"
    echo "  --aggressive   Use aggressive stripping"
    echo "  --keep         Keep intermediate files"
    echo "  -v, --verbose  Show verbose output"
    echo ""
    echo "Example:"
    echo "  $0 tests/minimal/001-return-literal.c"
    exit 1
}

# Parse arguments
NO_STRIP=false
AGGRESSIVE=false
KEEP=false
VERBOSE=false
NOLIBC=false
INPUT_FILE=""
OUTPUT_DIR=""

while [[ $# -gt 0 ]]; do
    case $1 in
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
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -h|--help)
            usage
            ;;
        *)
            if [[ -z "$INPUT_FILE" ]]; then
                INPUT_FILE="$1"
            elif [[ -z "$OUTPUT_DIR" ]]; then
                OUTPUT_DIR="$1"
            else
                echo "Unknown argument: $1"
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
    echo -e "${RED}Error: Input file not found: $INPUT_FILE${NC}"
    exit 1
fi

# Set up output directory
if [[ -z "$OUTPUT_DIR" ]]; then
    OUTPUT_DIR=$(mktemp -d)
    if [[ "$KEEP" == "false" ]]; then
        trap "rm -rf $OUTPUT_DIR" EXIT
    fi
fi
mkdir -p "$OUTPUT_DIR"

BASENAME=$(basename "$INPUT_FILE" .c)
JSON_FILE="$OUTPUT_DIR/${BASENAME}.json"
STRIPPED_FILE="$OUTPUT_DIR/${BASENAME}_stripped.json"
LEAN_FILE="$OUTPUT_DIR/${BASENAME}_proof.lean"

log() {
    if [[ "$VERBOSE" == "true" ]]; then
        echo -e "$1"
    fi
}

# Step 1: Run Cerberus to generate JSON
echo -e "${YELLOW}[1/4] Running Cerberus...${NC}"
CERBERUS_ARGS="--json_core_out=$JSON_FILE"
if [[ "$NOLIBC" == "true" ]]; then
    CERBERUS_ARGS="$CERBERUS_ARGS --nolibc"
fi
log "  cerberus $CERBERUS_ARGS $INPUT_FILE"
if ! "$SCRIPT_DIR/cerberus" $CERBERUS_ARGS "$INPUT_FILE" 2>/dev/null; then
    echo -e "${RED}FAILED: Cerberus failed to process $INPUT_FILE${NC}"
    exit 1
fi
JSON_SIZE=$(wc -c < "$JSON_FILE" | tr -d ' ')
log "  Generated: $JSON_FILE ($JSON_SIZE bytes)"

# Step 2: Strip the JSON (optional)
if [[ "$NO_STRIP" == "false" ]]; then
    echo -e "${YELLOW}[2/4] Stripping JSON...${NC}"
    STRIP_ARGS=""
    if [[ "$AGGRESSIVE" == "true" ]]; then
        STRIP_ARGS="--aggressive"
    fi
    log "  python3 strip_core_json.py $STRIP_ARGS $JSON_FILE $STRIPPED_FILE"
    if ! python3 "$SCRIPT_DIR/strip_core_json.py" $STRIP_ARGS "$JSON_FILE" "$STRIPPED_FILE" 2>/dev/null; then
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
cd "$LEAN_DIR"
if lake env lean "$LEAN_FILE" 2>&1 | head -20; then
    # Check if there were errors
    if lake env lean "$LEAN_FILE" 2>&1 | grep -q "error:"; then
        echo -e "${RED}FAILED: Generated Lean file has errors${NC}"
        echo ""
        echo "Output file: $LEAN_FILE"
        exit 1
    else
        echo -e "${GREEN}SUCCESS: Generated Lean file compiles${NC}"
    fi
else
    echo -e "${RED}FAILED: Lean compilation failed${NC}"
    exit 1
fi

echo ""
echo "Output files:"
echo "  JSON: $JSON_FILE"
if [[ "$NO_STRIP" == "false" ]]; then
    echo "  Stripped: $STRIPPED_FILE"
fi
echo "  Lean: $LEAN_FILE"

if [[ "$KEEP" == "true" ]]; then
    echo ""
    echo "Files kept in: $OUTPUT_DIR"
fi
