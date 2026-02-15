# C-to-Lean Project Makefile

.PHONY: all lean cerberus cerberus-setup cerberus-coverage cerberus-coverage-setup clean \
        test test-unit test-memory test-cn test-cn-unit \
        test-interp test-interp-full test-interp-ci test-interp-seq \
        test-parser test-pp test-parser-quick test-pp-quick \
        test-genproof test-verified verified-programs test-one \
        test-coverage \
        ci fuzz init update-cerberus help

# Configuration
# OCaml version for Cerberus (5.4.0+ recommended, 4.14.1 also works)
OCAML_VERSION := 5.4.0
# Use a local opam switch in cerberus/_opam/ for project isolation
CERBERUS_DIR := $(shell pwd)/cerberus
OPAM_EXEC := opam exec --switch=$(CERBERUS_DIR) --

# Coverage: separate local switch with OCaml 5.1.1 (bisect_ppx requires < 5.2)
COVERAGE_OCAML_VERSION := 5.1.1
COVERAGE_SWITCH_DIR := $(shell pwd)/_opam-coverage
OPAM_COV_EXEC := opam exec --switch=$(COVERAGE_SWITCH_DIR) --

# Default target
all: lean

# ------------------------------------------------------------------------------
# Build
# ------------------------------------------------------------------------------

# Build Lean project (library and test executables)
lean:
	cd lean && lake build

# Build verified programs (separate target due to slow native_decide proofs)
verified-programs: lean
	cd lean && lake build VerifiedPrograms

# Build Cerberus (requires local opam switch in cerberus/_opam/)
cerberus:
	cd cerberus && $(OPAM_EXEC) make cerberus

# Build Cerberus with coverage instrumentation (requires cerberus-coverage-setup)
cerberus-coverage:
	cd cerberus && $(OPAM_COV_EXEC) make cerberus-coverage

# ------------------------------------------------------------------------------
# Setup
# ------------------------------------------------------------------------------

# Initialize submodules (first time setup)
init:
	git submodule update --init --recursive

# First-time Cerberus setup: create local opam switch and install
cerberus-setup: init
	@echo "Creating local opam switch in cerberus/ with OCaml $(OCAML_VERSION)..."
	cd cerberus && opam switch create . $(OCAML_VERSION) --no-install || true
	@echo "Installing Cerberus dependencies..."
	cd cerberus && opam install --switch=. --deps-only -y ./cerberus-lib.opam ./cerberus.opam
	@echo "Building Cerberus..."
	cd cerberus && $(OPAM_EXEC) make cerberus
	@echo "Verifying Cerberus works..."
	$(OPAM_EXEC) dune exec --root cerberus -- cerberus --runtime=cerberus/_build/install/default --exec cerberus/tests/ci/0001-emptymain.c
	@echo "Cerberus setup complete!"
	@echo "Local switch created at: cerberus/_opam/"

# First-time coverage setup: create local switch with OCaml 5.1.1 + bisect_ppx
cerberus-coverage-setup: init
	@echo "Creating local coverage switch at $(COVERAGE_SWITCH_DIR) with OCaml $(COVERAGE_OCAML_VERSION)..."
	mkdir -p $(COVERAGE_SWITCH_DIR)
	cd $(COVERAGE_SWITCH_DIR) && opam switch create . $(COVERAGE_OCAML_VERSION) --no-install || true
	@echo "Installing Cerberus dependencies..."
	opam install --switch=$(COVERAGE_SWITCH_DIR) --deps-only -y ./cerberus/cerberus-lib.opam ./cerberus/cerberus.opam
	@echo "Installing bisect_ppx..."
	opam install --switch=$(COVERAGE_SWITCH_DIR) -y bisect_ppx
	@echo "Building Cerberus with coverage instrumentation..."
	cd cerberus && $(OPAM_COV_EXEC) make cerberus-coverage
	@echo "Coverage setup complete!"
	@echo "Local switch: $(COVERAGE_SWITCH_DIR)/_opam/"
	@echo "Run 'make test-coverage' to generate a coverage report."

# ------------------------------------------------------------------------------
# Clean
# ------------------------------------------------------------------------------

# Clean build artifacts (including accumulated temp files)
clean:
	cd lean && lake clean
	cd cerberus && make clean 2>/dev/null || true
	rm -rf tmp/

# ------------------------------------------------------------------------------
# Testing
#
# Scripts self-build their Lean targets (lake build is incremental),
# so most test targets don't need `lean` or `cerberus` as prerequisites.
# ------------------------------------------------------------------------------

# Run all quick tests (unit + memory + interp + genproof)
# NOTE: test-cn is excluded because CN is a prototype with known failures
test: test-unit test-memory test-interp test-interp-seq test-genproof

# Run exactly what CI runs (for local verification before pushing)
ci: test test-verified

# Verified programs (slow, native_decide proofs)
test-verified: verified-programs
	@echo "✓ Verified programs built successfully"

# Unit Tests (No Cerberus required)
test-unit: lean
	cd lean && .lake/build/bin/cerblean_test

test-memory: lean
	cd lean && .lake/build/bin/cerblean_memtest

# Test a single C file: make test-one FILE=tests/minimal/001-return-literal.c
test-one:
	@test -n "$(FILE)" || { echo "Usage: make test-one FILE=path/to/test.c"; exit 1; }
	./scripts/test_interp.sh --nolibc $(FILE)

# Parser Tests
test-parser-quick:
	./scripts/test_parser.sh --quick

test-parser:
	./scripts/test_parser.sh

# Pretty-Printer Tests
test-pp-quick:
	./scripts/test_pp.sh --quick

test-pp:
	./scripts/test_pp.sh

# GenProof Tests (test proof generation pipeline)
test-genproof:
	@echo "Testing genproof pipeline..."
	./scripts/test_genproof.sh --nolibc tests/minimal/001-return-literal.c
	@echo "✓ GenProof pipeline test passed"

# Interpreter Tests (fast mode with --nolibc, skips *.libc.c tests)
test-interp:
	./scripts/test_interp.sh --nolibc tests/minimal
	./scripts/test_interp.sh --nolibc tests/debug
	./scripts/test_interp.sh --nolibc tests/float

# Full interpreter tests (with libc, slower but complete)
test-interp-full:
	./scripts/test_interp.sh tests/minimal
	./scripts/test_interp.sh tests/debug
	./scripts/test_interp.sh tests/float

# CI suite (with libc)
test-interp-ci:
	./scripts/test_interp.sh

# Sequentialized mode (uses --sequentialise, excludes unseq tests)
test-interp-seq:
	./scripts/test_interp.sh --nolibc --sequentialise --exclude=unseq tests/minimal

# Coverage Tests
test-coverage: cerberus-coverage
	./scripts/test_coverage.sh --no-build

# CN Tests
# test-cn: run integration tests on tests/cn/*.c (requires Cerberus)
test-cn:
	./scripts/test_cn.sh

# test-cn-unit: run unit tests only (fast, no Cerberus)
test-cn-unit:
	./scripts/test_cn.sh --unit

# ------------------------------------------------------------------------------
# Fuzzing
# ------------------------------------------------------------------------------

# Run csmith fuzzer (generates random C programs and compares interpreters)
# Usage: make fuzz [N=100] - run N tests (default 100)
fuzz:
	./scripts/fuzz_csmith.sh $(or $(N),100)

# ------------------------------------------------------------------------------
# Maintenance
# ------------------------------------------------------------------------------

# Check that required dependencies are installed
check-deps:
	@echo "Checking dependencies..."
	@command -v opam >/dev/null 2>&1 || { echo "❌ opam not found"; exit 1; }
	@command -v lake >/dev/null 2>&1 || { echo "❌ lake not found (install elan)"; exit 1; }
	@command -v timeout >/dev/null 2>&1 || { echo "❌ timeout not found (brew install coreutils)"; exit 1; }
	@echo "✓ All dependencies found"

# Update Cerberus submodule
update-cerberus:
	git submodule update --remote cerberus

# ------------------------------------------------------------------------------
# Help
# ------------------------------------------------------------------------------

# Show help
help:
	@echo "C-to-Lean Project"
	@echo ""
	@echo "Setup (first time):"
	@echo "  make check-deps      Check required dependencies are installed"
	@echo "  make init            Initialize git submodules"
	@echo "  make cerberus-setup  Create local OCaml $(OCAML_VERSION) switch and install Cerberus"
	@echo "  make cerberus-coverage-setup  Create local coverage switch (OCaml $(COVERAGE_OCAML_VERSION) + bisect_ppx)"
	@echo ""
	@echo "Build:"
	@echo "  make                 Build Lean project (default)"
	@echo "  make verified-programs  Build verified programs (slow)"
	@echo "  make cerberus        Build Cerberus"
	@echo "  make cerberus-coverage  Build Cerberus with coverage instrumentation"
	@echo "  make clean           Clean all build artifacts"
	@echo ""
	@echo "Quick Tests:"
	@echo "  make test            Run all quick tests (unit + memory + interp + CN + genproof)"
	@echo "  make ci              Full CI suite (test + verified programs)"
	@echo "  make test-unit       Run Lean unit tests only"
	@echo "  make test-memory     Run memory model unit tests"
	@echo "  make test-cn         Run CN integration tests"
	@echo "  make test-cn-unit    Run CN unit tests only (fast)"
	@echo "  make test-genproof   Test proof generation pipeline"
	@echo "  make test-verified   Build verified programs (slow native_decide)"
	@echo "  make test-one FILE=path/to/test.c   Test a single C file"
	@echo ""
	@echo "Interpreter Tests:"
	@echo "  make test-interp       Fast interpreter tests (--nolibc)"
	@echo "  make test-interp-full  Full interpreter tests (with libc)"
	@echo "  make test-interp-ci    Run on Cerberus CI suite (~5500 files)"
	@echo "  make test-interp-seq   Sequentialized mode (no unseq, faster)"
	@echo ""
	@echo "Integration Tests (slow):"
	@echo "  make test-parser     Full parser test (~5500 files)"
	@echo "  make test-pp         Full pretty-printer test (~5500 files)"
	@echo ""
	@echo "Fuzzing:"
	@echo "  make fuzz            Run csmith fuzzer (100 tests)"
	@echo "  make fuzz N=500      Run csmith fuzzer (500 tests)"
	@echo ""
	@echo "Coverage:"
	@echo "  make test-coverage   Run tests and generate Cerberus OCaml coverage report"
	@echo ""
	@echo "Maintenance:"
	@echo "  make update-cerberus   Update Cerberus submodule"
	@echo "  make help              Show this help"
