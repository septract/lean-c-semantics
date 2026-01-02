# C-to-Lean Project Makefile

.PHONY: all lean cerberus cerberus-setup clean
.PHONY: test test-unit test-memory
.PHONY: test-parser test-pp test-parser-quick test-pp-quick
.PHONY: test-interp test-interp-minimal test-interp-debug test-interp-ci
.PHONY: init update-cerberus help

# Configuration
# Cerberus requires OCaml 4.14.1 (crashes on OCaml 5.x)
OPAM_SWITCH := cerberus-414
OPAM_EXEC := OPAMSWITCH=$(OPAM_SWITCH) opam exec --
# Run Cerberus from local build (avoids pinning/reinstalling)
CERBERUS_CMD := $(OPAM_EXEC) dune exec --root cerberus -- cerberus

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

# Run all quick tests (unit tests + parser + pretty-printer with 50 files each)
test: test-unit test-parser-quick test-pp-quick

# Unit Tests (No Cerberus required)
test-unit: lean
	cd lean && .lake/build/bin/ctolean_test

test-memory: lean
	cd lean && .lake/build/bin/ctolean_memtest

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

# Interpreter Tests
test-interp-minimal: lean cerberus
	./scripts/test_interp.sh tests/minimal

test-interp-debug: lean cerberus
	./scripts/test_interp.sh tests/debug

test-interp-ci: lean cerberus
	./scripts/test_interp.sh

# Run minimal and debug interpreter tests
test-interp: test-interp-minimal test-interp-debug

# ------------------------------------------------------------------------------
# Maintenance
# ------------------------------------------------------------------------------

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
	@echo "  init              Initialize git submodules"
	@echo "  cerberus-setup    Create OCaml 4.14 switch and install Cerberus"
	@echo ""
	@echo "Build:"
	@echo "  all               Build Lean project (default)"
	@echo "  lean              Build Lean project"
	@echo "  cerberus          Build Cerberus"
	@echo "  clean             Clean all build artifacts"
	@echo ""
	@echo "Test Suites:"
	@echo "  test              Run quick sanity checks (Unit + Quick Parser/PP)"
	@echo "  test-unit         Run Lean unit tests (Memory + Parser)"
	@echo "  test-memory       Run Memory model unit tests only"
	@echo ""
	@echo "Integration Tests (Full Suites):"
	@echo "  test-parser       Run full parser test (~5500 files)"
	@echo "  test-pp           Run full pretty-printer test (~5500 files)"
	@echo "  test-interp       Run interpreter tests (Minimal + Debug)"
	@echo "  test-interp-ci    Run interpreter tests on Cerberus CI suite"
	@echo ""
	@echo "Maintenance:"
	@echo "  update-cerberus   Update Cerberus submodule"
	@echo "  help              Show this help"