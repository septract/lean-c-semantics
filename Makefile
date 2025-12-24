# C-to-Lean Project Makefile

.PHONY: all lean cerberus clean test help

# Default target
all: lean

# Build Lean project
lean:
	cd lean && lake build

# Build Cerberus (requires opam environment)
cerberus:
	cd cerberus && dune build

# Clean build artifacts
clean:
	cd lean && lake clean
	cd cerberus && dune clean 2>/dev/null || true

# Run tests (placeholder - will be expanded)
test: lean
	@echo "Tests not yet implemented"

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
	@echo "  test            Run tests"
	@echo "  init            Initialize git submodules"
	@echo "  update-cerberus Update Cerberus submodule"
	@echo "  help            Show this help"
