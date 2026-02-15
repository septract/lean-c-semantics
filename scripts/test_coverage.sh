#!/usr/bin/env bash
# Generate OCaml code coverage reports for Cerberus.
#
# Usage: ./scripts/test_coverage.sh [options] [test_dir...]
#
# This script:
#   1. Builds Cerberus with bisect_ppx instrumentation (using the coverage switch)
#   2. Runs our test suites through the instrumented binary
#   3. Generates HTML + terminal coverage reports
#
# Requires: make cerberus-coverage-setup (one-time)
#
# Options:
#   --no-build        Skip the build step (reuse previous instrumented build)
#   --no-tests        Skip running tests (just regenerate report from existing data)
#   --ci              Also run Cerberus CI suite (cerberus/tests/ci)
#   -h, --help        Show this help message
#
# Default test dirs: tests/minimal tests/debug tests/float tests/coverage

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
set -euo pipefail

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
COVERAGE_DIR="$PROJECT_ROOT/_coverage"
CERBERUS_COV_BIN="$CERBERUS_DIR/_build/coverage/backend/driver/main.exe"
CERBERUS_COV_RUNTIME="$CERBERUS_DIR/_build/install/default"

# Coverage uses a separate local opam switch (OCaml 5.1.1 + bisect_ppx)
COVERAGE_SWITCH_DIR="$PROJECT_ROOT/_opam-coverage"
OPAM_COV_EXEC="opam exec --switch=$COVERAGE_SWITCH_DIR --"

DO_BUILD=true
DO_TESTS=true
RUN_CI=false
TEST_DIRS=()

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
usage() {
    cat <<'EOF'
Generate OCaml code coverage reports for Cerberus.

Usage: ./scripts/test_coverage.sh [options] [test_dir...]

Requires: make cerberus-coverage-setup (one-time)

Options:
  --no-build        Skip the build step (reuse previous instrumented build)
  --no-tests        Skip running tests (regenerate report from existing data)
  --ci              Also run Cerberus CI suite (cerberus/tests/ci)
  -h, --help        Show this help message

Default test dirs: tests/minimal tests/debug tests/float tests/coverage
EOF
    exit 0
}

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)    usage ;;
        --no-build)   DO_BUILD=false; shift ;;
        --no-tests)   DO_TESTS=false; shift ;;
        --ci)         RUN_CI=true; shift ;;
        -*)
            echo "Unknown option: $1" >&2
            exit 1
            ;;
        *)
            TEST_DIRS+=("$1")
            shift
            ;;
    esac
done

# Default test directories
if [[ ${#TEST_DIRS[@]} -eq 0 ]]; then
    TEST_DIRS=("$PROJECT_ROOT/tests/minimal" "$PROJECT_ROOT/tests/debug" "$PROJECT_ROOT/tests/float")
    if $RUN_CI; then
        TEST_DIRS+=("$CERBERUS_DIR/tests/ci")
    fi
fi

# Coverage tests are always included (run directly through Cerberus, not test_interp.sh)
COVERAGE_TEST_DIR="$PROJECT_ROOT/tests/coverage"

# ---------------------------------------------------------------------------
# Prerequisites
# ---------------------------------------------------------------------------
if [[ ! -d "$COVERAGE_SWITCH_DIR/_opam" ]]; then
    echo "Error: Coverage opam switch not found at $COVERAGE_SWITCH_DIR/_opam/" >&2
    echo "Run 'make cerberus-coverage-setup' first." >&2
    exit 1
fi

if ! $OPAM_COV_EXEC which bisect-ppx-report &>/dev/null; then
    echo "Error: bisect-ppx-report not found in the coverage switch." >&2
    echo "Run 'make cerberus-coverage-setup' to install bisect_ppx." >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Step 1: Build Cerberus with coverage instrumentation
# ---------------------------------------------------------------------------
if $DO_BUILD; then
    echo "=== Building Cerberus with coverage instrumentation ==="
    cd "$CERBERUS_DIR"
    $OPAM_COV_EXEC dune build --workspace=dune-workspace.coverage cerberus-lib.install cerberus.install
    cd "$PROJECT_ROOT"
    echo "  Done. Instrumented binary: $CERBERUS_COV_BIN"
fi

if [[ ! -x "$CERBERUS_COV_BIN" ]]; then
    echo "Error: Instrumented binary not found at $CERBERUS_COV_BIN" >&2
    echo "Run without --no-build first." >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Step 2: Run tests, collecting .coverage files
# ---------------------------------------------------------------------------
if $DO_TESTS; then
    echo ""
    echo "=== Running tests with coverage collection ==="

    # Clean old coverage data
    mkdir -p "$COVERAGE_DIR"
    rm -f "$COVERAGE_DIR"/bisect*.coverage

    # Point bisect_ppx output to our coverage directory
    export BISECT_FILE="$COVERAGE_DIR/bisect"

    # Create a temporary wrapper script that invokes the coverage binary
    # instead of the default one. test_interp.sh uses $CERBERUS (scripts/cerberus),
    # which resolves the binary path from _build/default/. We override CERBERUS
    # to point to a wrapper that uses the coverage binary.
    COV_WRAPPER=$(make_temp_dir "cov-wrapper")
    register_cleanup "$COV_WRAPPER"

    cat > "$COV_WRAPPER/cerberus" <<WRAPPER
#!/bin/bash
$OPAM_COV_EXEC "$CERBERUS_COV_BIN" --runtime="$CERBERUS_COV_RUNTIME" "\$@"
WRAPPER
    chmod +x "$COV_WRAPPER/cerberus"

    # Override CERBERUS so test_interp.sh picks up the instrumented binary
    export CERBERUS="$COV_WRAPPER/cerberus"

    for test_dir in "${TEST_DIRS[@]}"; do
        if [[ ! -e "$test_dir" ]]; then
            echo "  Warning: $test_dir does not exist, skipping" >&2
            continue
        fi
        echo "  Running: $test_dir"
        "$PROJECT_ROOT/scripts/test_interp.sh" --nolibc "$test_dir" || true
    done

    # -----------------------------------------------------------------------
    # Run coverage-specific tests directly through the instrumented Cerberus
    # binary (no Lean interpreter involved). This exercises Cerberus code
    # paths that our existing test suites may not reach.
    # -----------------------------------------------------------------------
    if [[ -d "$COVERAGE_TEST_DIR" ]]; then
        echo ""
        echo "  Running coverage tests (direct Cerberus execution)..."
        COV_PASS=0
        COV_FAIL=0
        COV_TOTAL=0

        for c_file in $(find "$COVERAGE_TEST_DIR" -name '*.c' | sort); do
            COV_TOTAL=$((COV_TOTAL + 1))
            rel_path="${c_file#$PROJECT_ROOT/}"

            # Determine if this test needs libc (either in libc/ dir or .libc.c suffix)
            if [[ "$c_file" == */libc/* ]] || [[ "$c_file" == *.libc.c ]]; then
                nolibc_flag=""
            else
                nolibc_flag="--nolibc"
            fi

            if $CERBERUS --exec --batch $nolibc_flag "$c_file" &>/dev/null; then
                COV_PASS=$((COV_PASS + 1))
            else
                # Failures are OK — UB tests, crashes, etc. still generate coverage
                COV_FAIL=$((COV_FAIL + 1))
            fi
        done

        echo "    Coverage tests: $COV_TOTAL total, $COV_PASS passed, $COV_FAIL failed/UB"
    fi

    COV_COUNT=$(ls -1 "$COVERAGE_DIR"/bisect*.coverage 2>/dev/null | wc -l | tr -d ' ')
    echo "  Collected $COV_COUNT coverage files"
fi

# ---------------------------------------------------------------------------
# Step 3: Generate reports
# ---------------------------------------------------------------------------
echo ""
echo "=== Generating coverage reports ==="

if ! ls "$COVERAGE_DIR"/bisect*.coverage &>/dev/null; then
    echo "Error: No coverage data found in $COVERAGE_DIR/" >&2
    echo "Run tests first (without --no-tests)." >&2
    exit 1
fi

# Run reports from the cerberus directory so bisect_ppx can find sources
cd "$CERBERUS_DIR"

# Terminal summary
echo ""
echo "--- Per-file coverage summary ---"
$OPAM_COV_EXEC bisect-ppx-report summary \
    --coverage-path "$COVERAGE_DIR" \
    --per-file

# HTML report
$OPAM_COV_EXEC bisect-ppx-report html \
    --coverage-path "$COVERAGE_DIR" \
    --ignore-missing-files \
    -o "$COVERAGE_DIR/html"
cd "$PROJECT_ROOT"

echo ""
echo "=== Coverage report generated ==="
echo "  HTML report: $COVERAGE_DIR/html/index.html"
echo "  Open with:   open $COVERAGE_DIR/html/index.html"
