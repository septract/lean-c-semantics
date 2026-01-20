# C-to-Lean Project Makefile

.PHONY: all lean cerberus cerberus-setup clean
.PHONY: test test-unit test-memory ci check-deps
.PHONY: test-parser test-pp test-parser-quick test-pp-quick
.PHONY: test-interp test-interp-minimal test-interp-debug test-one
.PHONY: test-interp-full test-interp-minimal-full test-interp-debug-full test-interp-ci
.PHONY: test-genproof
.PHONY: fuzz init update-cerberus help

# Configuration
# Cerberus requires OCaml 4.14.1 (crashes on OCaml 5.x)
OPAM_SWITCH := cerberus-414
OPAM_EXEC := OPAMSWITCH=$(OPAM_SWITCH) opam exec --
# Run Cerberus from local build (avoids pinning/reinstalling)
CERBERUS_CMD := $(OPAM_EXEC) dune exec --root cerberus -- cerberus --runtime=cerberus/_build/install/default

# Default target
all: lean

# ------------------------------------------------------------------------------
# Build
# ------------------------------------------------------------------------------

# Build Lean project (library and test executables)
lean:
	cd lean && lake build

# Build Cerberus (requires cerberus-414 opam switch)
cerberus:
	cd cerberus && $(OPAM_EXEC) make cerberus

# ------------------------------------------------------------------------------
# Setup
# ------------------------------------------------------------------------------

# Initialize submodules (first time setup)
init:
	git submodule update --init --recursive

# First-time Cerberus setup: create opam switch and install
cerberus-setup: init
	@echo "Creating opam switch $(OPAM_SWITCH) with OCaml 4.14.1..."
	opam switch create $(OPAM_SWITCH) 4.14.1 || true
	@echo "Installing Cerberus dependencies..."
	cd cerberus && $(OPAM_EXEC) opam install --deps-only -y ./cerberus-lib.opam ./cerberus.opam
	@echo "Building Cerberus..."
	cd cerberus && $(OPAM_EXEC) make cerberus
	@echo "Verifying Cerberus works..."
	$(CERBERUS_CMD) --exec cerberus/tests/ci/0001-emptymain.c
	@echo "Cerberus setup complete!"

# ------------------------------------------------------------------------------
# Clean
# ------------------------------------------------------------------------------

# Clean build artifacts
clean:
	cd lean && lake clean
	cd cerberus && make clean 2>/dev/null || true

# ------------------------------------------------------------------------------
# Testing
# ------------------------------------------------------------------------------

# Run quick tests (same as CI)
test: test-unit test-interp test-genproof

# Run exactly what CI runs (for local verification before pushing)
ci: test-unit test-interp test-genproof

# Unit Tests (No Cerberus required)
test-unit: lean
	cd lean && .lake/build/bin/cerblean_test

test-memory: lean
	cd lean && .lake/build/bin/cerblean_memtest

# Test a single C file: make test-one FILE=tests/minimal/001-return-literal.c
test-one:
	@test -n "$(FILE)" || { echo "Usage: make test-one FILE=path/to/test.c"; exit 1; }
	@$(MAKE) lean cerberus
	./scripts/test_interp.sh --nolibc $(FILE)

# Parser Tests
test-parser-quick: lean cerberus
	./scripts/test_parser.sh --quick

test-parser: lean cerberus
	./scripts/test_parser.sh

# Pretty-Printer Tests
test-pp-quick: lean cerberus
	./scripts/test_pp.sh --quick

test-pp: lean cerberus
	./scripts/test_pp.sh

# GenProof Tests (test proof generation pipeline)
test-genproof: lean cerberus
	@echo "Testing genproof pipeline..."
	./scripts/test_genproof.sh --nolibc tests/minimal/001-return-literal.c
	@echo "✓ GenProof pipeline test passed"

# Interpreter Tests (fast mode with --nolibc, skips *.libc.c tests)
test-interp-minimal: lean cerberus
	./scripts/test_interp.sh --nolibc tests/minimal

test-interp-debug: lean cerberus
	./scripts/test_interp.sh --nolibc tests/debug

# Run minimal and debug interpreter tests (fast)
test-interp: test-interp-minimal test-interp-debug

# Full interpreter tests (with libc, slower but complete)
test-interp-minimal-full: lean cerberus
	./scripts/test_interp.sh tests/minimal

test-interp-debug-full: lean cerberus
	./scripts/test_interp.sh tests/debug

test-interp-full: test-interp-minimal-full test-interp-debug-full

# CI suite (with libc)
test-interp-ci: lean cerberus
	./scripts/test_interp.sh

# ------------------------------------------------------------------------------
# Fuzzing
# ------------------------------------------------------------------------------

# Run csmith fuzzer (generates random C programs and compares interpreters)
# Usage: make fuzz [N=100] - run N tests (default 100)
fuzz: lean cerberus
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
	@echo "  make cerberus-setup  Create OCaml 4.14 switch and install Cerberus"
	@echo ""
	@echo "Build:"
	@echo "  make                 Build Lean project (default)"
	@echo "  make cerberus        Build Cerberus"
	@echo "  make clean           Clean all build artifacts"
	@echo ""
	@echo "Quick Tests:"
	@echo "  make test            Run quick tests (unit + interpreter + genproof)"
	@echo "  make ci              Same as 'test' - verify before pushing"
	@echo "  make test-unit       Run Lean unit tests only"
	@echo "  make test-genproof   Test proof generation pipeline"
	@echo "  make test-one FILE=path/to/test.c   Test a single C file"
	@echo ""
	@echo "Interpreter Tests:"
	@echo "  make test-interp       Fast interpreter tests (--nolibc)"
	@echo "  make test-interp-full  Full interpreter tests (with libc)"
	@echo "  make test-interp-ci    Run on Cerberus CI suite (~5500 files)"
	@echo ""
	@echo "Integration Tests (slow):"
	@echo "  make test-parser     Full parser test (~5500 files)"
	@echo "  make test-pp         Full pretty-printer test (~5500 files)"
	@echo ""
	@echo "Fuzzing:"
	@echo "  make fuzz            Run csmith fuzzer (100 tests)"
	@echo "  make fuzz N=500      Run csmith fuzzer (500 tests)"
	@echo ""
	@echo "Maintenance:"
	@echo "  make update-cerberus   Update Cerberus submodule"
	@echo "  make help              Show this help"