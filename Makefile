# C-to-Lean Project Makefile

.PHONY: all lean cerberus cerberus-setup clean test test-unit test-memory test-parser-full test-pp-full test-interp test-interp-minimal test-interp-debug test-interp-ci help

# Cerberus requires OCaml 4.14.1 (crashes on OCaml 5.x)
OPAM_SWITCH := cerberus-414
OPAM_EXEC := OPAMSWITCH=$(OPAM_SWITCH) opam exec --

# Default target
all: lean

# Build Lean project (library and test executables)
lean:
	cd lean && lake build

# Build Cerberus (requires cerberus-414 opam switch)
cerberus:
	cd cerberus && $(OPAM_EXEC) make cerberus

# First-time Cerberus setup: create opam switch and install
cerberus-setup:
	@echo "Creating opam switch $(OPAM_SWITCH) with OCaml 4.14.1..."
	opam switch create $(OPAM_SWITCH) 4.14.1 || true
	@echo "Installing Cerberus dependencies..."
	cd cerberus && $(OPAM_EXEC) opam install --deps-only -y ./cerberus-lib.opam ./cerberus.opam
	@echo "Pinning and installing Cerberus..."
	cd cerberus && $(OPAM_EXEC) opam pin --yes --no-action add cerberus-lib .
	cd cerberus && $(OPAM_EXEC) opam pin --yes --no-action add cerberus .
	$(OPAM_EXEC) opam install --yes cerberus
	@echo "Verifying Cerberus works..."
	$(OPAM_EXEC) cerberus --exec cerberus/tests/ci/0001-emptymain.c
	@echo "Cerberus setup complete!"

# Clean build artifacts
clean:
	cd lean && lake clean
	cd cerberus && make clean 2>/dev/null || true

# Run all quick tests (unit tests + parser + pretty-printer with 50 files each)
test: lean cerberus
	cd lean && .lake/build/bin/ctolean_test
	./scripts/test_parser.sh --quick
	./scripts/test_pp.sh --quick

# Run unit tests only (no Cerberus required)
test-unit: lean
	cd lean && .lake/build/bin/ctolean_test

# Run memory model unit tests only (no Cerberus required)
test-memory: lean
	cd lean && .lake/build/bin/ctolean_memtest

# Run full parser test suite (~5500 files, ~12 min)
test-parser-full: lean cerberus
	./scripts/test_parser.sh

# Run full pretty-printer test (~5500 files)
test-pp-full: lean cerberus
	./scripts/test_pp.sh

# Run interpreter tests on minimal test suite (30 simple C programs)
test-interp-minimal: lean cerberus
	./scripts/test_interp.sh tests/minimal

# Run interpreter tests on debug test cases
test-interp-debug: lean cerberus
	./scripts/test_interp.sh tests/debug

# Run interpreter tests on Cerberus CI suite
test-interp-ci: lean cerberus
	./scripts/test_interp.sh

# Run interpreter tests (all: minimal + debug + CI)
test-interp: test-interp-minimal test-interp-debug

# Update Cerberus submodule
update-cerberus:
	git submodule update --remote cerberus

# Initialize submodules (first time setup)
init:
	git submodule update --init --recursive

# Show help
help:
	@echo "C-to-Lean Project"
	@echo ""
	@echo "Setup (first time):"
	@echo "  init              Initialize git submodules"
	@echo "  cerberus-setup    Create OCaml 4.14 switch and install Cerberus"
	@echo ""
	@echo "Targets:"
	@echo "  all               Build Lean project (default)"
	@echo "  lean              Build Lean project"
	@echo "  cerberus          Build Cerberus (requires cerberus-setup first)"
	@echo "  clean             Clean all build artifacts"
	@echo ""
	@echo "Testing (no Cerberus required):"
	@echo "  test-unit         Run all unit tests (parser smoke + memory)"
	@echo "  test-memory       Run memory model unit tests only"
	@echo ""
	@echo "Testing (requires Cerberus):"
	@echo "  test              Run quick tests (unit + 50 parser + 50 PP files)"
	@echo "  test-parser-full  Run full parser test (~5500 files, ~12 min)"
	@echo "  test-pp-full      Run full pretty-printer test (~5500 files)"
	@echo ""
	@echo "Interpreter Testing (requires Cerberus):"
	@echo "  test-interp          Run interpreter on minimal + debug tests"
	@echo "  test-interp-minimal  Run interpreter on tests/minimal/ (30 simple programs)"
	@echo "  test-interp-debug    Run interpreter on tests/debug/ (debugging cases)"
	@echo "  test-interp-ci       Run interpreter on Cerberus CI suite"
	@echo ""
	@echo "Maintenance:"
	@echo "  update-cerberus   Update Cerberus submodule"
	@echo "  help              Show this help"
