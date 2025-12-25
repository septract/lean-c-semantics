# C-to-Lean Project

## Overview
This project translates C code into Lean 4 code that captures C semantics, enabling formal reasoning about C programs in Lean.

## Architecture

### Pipeline
```
C source → Cerberus → Core IR (JSON) → Lean Parser → Lean AST → Lean Interpreter
                                                              ↓
                                                    UB-freeness theorems
```

### Key Components
- **Cerberus** (submodule): C frontend that produces Core IR
- **Lean Parser**: Parses JSON-serialized Core into Lean types
- **Lean Interpreter**: Executes Core programs with configurable memory model
- **Theorem Generator**: Produces UB-freeness theorem statements

## Project Structure
```
c-to-lean/
├── cerberus/          # Git submodule - Cerberus C semantics tool (private fork)
├── docs/
│   └── DETAILED_PLAN.md   # Full implementation roadmap
├── lean/              # Lean 4 project
│   └── CToLean/
│       ├── Core/      # Core AST types
│       ├── Parser.lean # JSON parser (100% success on test suite)
│       ├── Memory/    # Memory model implementations (future)
│       ├── Semantics/ # Interpreter (future)
│       ├── Theorems/  # UB-freeness definitions (future)
│       └── Test*.lean # Test utilities
├── scripts/           # Development scripts
│   └── test_parser.sh # Run parser against Cerberus test suite
├── tests/             # Simple C test files
├── context/           # Background materials
├── CLAUDE.md          # This file
├── PLAN.md            # High-level goals
└── TODO.md            # Current tasks
```

## Key Design Decisions

### 1. Manual Translation (not Lem/Ott backends)
We manually translate Cerberus Core semantics to Lean rather than creating automated backends because:
- Allows idiomatic Lean 4 code
- Decoupled from Cerberus toolchain
- Lem-to-Coq experience suggests poor fit for proof assistants

### 2. JSON Export from Cerberus
We modify Cerberus to export Core IR as JSON rather than parsing pretty-printed text:
- Cleaner, unambiguous parsing
- Structured data easier to work with

### 3. Memory Model Type Class
Memory operations use a type class for incremental complexity:
- **Simple**: Integer addresses, no provenance (start here)
- **Concrete**: Allocation IDs, bounds checking (Cerberus default)
- **PNVI**: Full provenance semantics (future)

### 4. Sequential Fragment First
Focus on sequential Core initially:
- Use `core_sequentialise` pass to eliminate concurrency
- Concurrent semantics (`Epar`, `Eunseq`) deferred

## Cerberus Reference

### Key Files
| File | Description |
|------|-------------|
| `cerberus/frontend/ott/core-ott/core.ott` | Core AST grammar (~600 lines) |
| `cerberus/frontend/model/core_run.lem` | Execution semantics (~1655 lines) |
| `cerberus/frontend/model/core_eval.lem` | Expression evaluation (~1198 lines) |
| `cerberus/frontend/model/mem_common.lem` | Memory interface (~705 lines) |
| `cerberus/frontend/model/core_sequentialise.lem` | Concurrency elimination |
| `cerberus/memory/concrete/impl_mem.ml` | Concrete memory model (~3015 lines) |

### Core AST Types (from core.ott)
- `core_object_type`: integer, floating, pointer, array, struct, union
- `core_base_type`: unit, boolean, ctype, list, tuple, object, loaded
- `binop`: arithmetic and logical operators
- `value`: Core values
- `generic_pexpr`: Pure expressions
- `generic_expr`: Effectful expressions (memory operations)
- `generic_file`: Complete Core program

### Running Cerberus

The Cerberus executable is at `cerberus/_build/default/backend/driver/main.exe`.

```bash
CERBERUS=./cerberus/_build/default/backend/driver/main.exe

# Pretty-print Core to stdout
$CERBERUS --pp=core input.c

# Pretty-print Core to file (requires --pp=core flag too)
$CERBERUS --pp=core --pp_core_out=output.core input.c

# Export Core as JSON (for Lean parser)
$CERBERUS --json_core_out=output.json input.c

# Execute C program
$CERBERUS --exec input.c

# Get help
$CERBERUS --help
```

## Validation

### Test Suite
Cerberus has 5500+ test files in `cerberus/tests/`:
- `tests/ci/*.c` - Main CI tests
- `*.undef.c` - Expected undefined behavior
- `*.syntax-only.c` - Parse-only tests

### Differential Testing
Compare Lean interpreter output against Cerberus:
1. Run Cerberus on C file, get Core + execution result
2. Parse Core in Lean
3. Execute in Lean interpreter
4. Compare results (return value, UB detection)

Target: 90%+ agreement on sequential tests.

## Development Notes

### Building

Use the top-level Makefile:
```bash
make lean       # Build Lean project
make cerberus   # Build Cerberus (requires opam environment)
make test       # Quick test (100 files)
make test-full  # Full test suite (~5500 files)
make clean      # Clean all build artifacts
```

Or build individually:
```bash
# Cerberus - use 'make cerberus', NOT 'dune build' (avoids z3/coq deps)
cd cerberus && make cerberus

# Lean
cd lean && lake build
```

## References
- [Cerberus Project](https://github.com/rems-project/cerberus)
- [Lem Language](https://github.com/rems-project/lem)
- [Ott Tool](https://github.com/ott-lang/ott)
- [Lean 4](https://lean-lang.org/)
