# C-to-Lean Project Makefile

.PHONY: all lean cerberus clean test test-unit test-memory test-parser-full test-pp-full help

# Default target
all: lean

# Build Lean project (library and test executables)
lean:
	cd lean && lake build

# Build Cerberus (requires opam environment with lem)
cerberus:
	cd cerberus && make cerberus

# Clean build artifacts
clean:
	cd lean && lake clean
	cd cerberus && make clean 2>/dev/null || true

# Run all quick tests (unit tests + parser + pretty-printer with 100 files each)
test: lean cerberus
	cd lean && .lake/build/bin/ctolean_test
	./scripts/test_parser.sh --quick
	./scripts/test_pp.sh --max 100

# Run unit tests only (no Cerberus required)
test-unit: lean
	cd lean && .lake/build/bin/ctolean_test

# Run memory model unit tests only (no Cerberus required)
test-memory: lean
	cd lean && .lake/build/bin/ctolean_memtest

# Run full parser test suite (~5500 files, ~12 min)
test-parser-full: lean cerberus
	./scripts/test_parser.sh

# Run full pretty-printer test (all CI files)
test-pp-full: lean cerberus
	./scripts/test_pp.sh

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
	@echo "Targets:"
	@echo "  all               Build Lean project (default)"
	@echo "  lean              Build Lean project"
	@echo "  cerberus          Build Cerberus (requires opam)"
	@echo "  clean             Clean all build artifacts"
	@echo ""
	@echo "Testing (no Cerberus required):"
	@echo "  test-unit         Run all unit tests (parser smoke + memory)"
	@echo "  test-memory       Run memory model unit tests only"
	@echo ""
	@echo "Testing (requires Cerberus):"
	@echo "  test              Run quick tests (unit + 100 parser + 100 PP files)"
	@echo "  test-parser-full  Run full parser test (~5500 files, ~12 min)"
	@echo "  test-pp-full      Run full pretty-printer test (all CI files)"
	@echo ""
	@echo "Setup:"
	@echo "  init              Initialize git submodules"
	@echo "  update-cerberus   Update Cerberus submodule"
	@echo "  help              Show this help"
