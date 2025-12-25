# C-to-Lean Project Makefile

.PHONY: all lean cerberus clean test test-full help

# Default target
all: lean

# Build Lean project (library and test executables)
lean:
	cd lean && lake build ctolean_testbatch

# Build Cerberus (requires opam environment with lem)
cerberus:
	cd cerberus && make cerberus

# Clean build artifacts
clean:
	cd lean && lake clean
	cd cerberus && make clean 2>/dev/null || true

# Run quick tests (first 100 files)
test: lean cerberus
	./scripts/test_parser.sh --quick

# Run full test suite (~5500 files, ~12 min)
test-full: lean cerberus
	./scripts/test_parser.sh

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
	@echo "  all             Build Lean project (default)"
	@echo "  lean            Build Lean project"
	@echo "  cerberus        Build Cerberus (requires opam)"
	@echo "  clean           Clean all build artifacts"
	@echo "  test            Run quick tests (100 files, ~15s)"
	@echo "  test-full       Run full test suite (~5500 files, ~12 min)"
	@echo "  init            Initialize git submodules"
	@echo "  update-cerberus Update Cerberus submodule"
	@echo "  help            Show this help"
