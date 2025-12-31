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
│       ├── Parser.lean      # JSON parser (100% success on test suite)
│       ├── PrettyPrint.lean # Pretty-printer matching Cerberus output
│       ├── Memory/    # Memory model (concrete with allocation-ID provenance)
│       ├── Semantics/ # Interpreter (future)
│       ├── Theorems/  # UB-freeness definitions (future)
│       └── Test*.lean # Test utilities
├── scripts/           # Development scripts
│   ├── test_parser.sh # Run parser against Cerberus test suite
│   └── test_pp.sh     # Run pretty-printer comparison tests
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

# Pretty-print Core in compact mode (single line, for diffing)
$CERBERUS --pp=core --pp_core_compact input.c

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

### Test Scripts

**Parser Test** (`scripts/test_parser.sh`):
Tests that the Lean JSON parser can successfully parse Cerberus JSON output.
```bash
./scripts/test_parser.sh --quick    # Test first 100 files
./scripts/test_parser.sh            # Full test suite (~5500 files)
./scripts/test_parser.sh --max 500  # Test first 500 files
```

**Pretty-Printer Test** (`scripts/test_pp.sh`):
Compares Lean pretty-printer output against Cerberus pretty-printer output.
```bash
./scripts/test_pp.sh --max 100      # Test first 100 files
./scripts/test_pp.sh --max 100 -v   # Verbose mode (show each file)
./scripts/test_pp.sh                # Full test (all CI files)
```
The script generates JSON from Cerberus, runs the Lean pretty-printer, compares with Cerberus compact output, and reports match rate. Output files are saved to a temp directory for investigation.

Current status:
- **CI tests**: 100% match rate (121/121 files)
- **Full test suite (5501 files)**: 99% match rate (1809/1817 files)

See `docs/PP_DISCREPANCIES.md` for remaining issues (NULL type parsing for complex types - deferred pending Cerberus-side fix).

**Memory Model Tests** (`make test-memory`):
Unit tests for the memory model implementation.
```bash
make test-memory                           # Run memory model unit tests
cd lean && .lake/build/bin/ctolean_memtest # Run directly
```
Tests include: layout (sizeof/alignof), allocation, store/load roundtrip, null dereference detection, use-after-free detection, double-free detection, out-of-bounds detection, read-only protection, pointer arithmetic.

**Investigating Pretty-Printer Mismatches**:
The test script outputs files to a temp directory. To investigate a specific mismatch:
```bash
# Run tests and note the output directory
./scripts/test_pp.sh --max 250

# Use the Lean comparison tool directly (normalizes whitespace, strips section comments)
./lean/.lake/build/bin/ctolean_pp /path/to/OUTPUT_DIR/filename.json --compare /path/to/OUTPUT_DIR/filename.cerberus.core

# Example output showing the first difference:
# First difference at position 458:
#   Lean:     'store('signed int', a_530,'
#   Cerberus: 'store_lock('signed int', a'
```
Do NOT use `diff` directly - it doesn't normalize whitespace. Always use the `--compare` flag with the Lean tool.

### Differential Testing (Future)
Compare Lean interpreter output against Cerberus:
1. Run Cerberus on C file, get Core + execution result
2. Parse Core in Lean
3. Execute in Lean interpreter
4. Compare results (return value, UB detection)

Target: 90%+ agreement on sequential tests.

## Development Notes

### CRITICAL: Never Undo Changes Without Permission
**NEVER revert, undo, or `git checkout` any changes without explicit user confirmation.** Even if you think a change caused a problem, ASK FIRST before reverting. The user may have made intentional changes you're not aware of.

### Shell Commands
**IMPORTANT**: Do NOT use `sed`, `awk`, `tr`, or similar shell string manipulation tools for ad-hoc text processing. These commands are error-prone and often fail silently or produce unexpected results across different platforms.

If string manipulation is needed:
- Write a proper Lean program to do the transformation
- Or wrap the shell commands in a well-designed, tested shell script in `scripts/`

### Building

Use the top-level Makefile:
```bash
make lean             # Build Lean project
make cerberus         # Build Cerberus (requires opam environment)
make test             # Run all quick tests (parser + PP + memory)
make test-memory      # Run memory model unit tests only
make test-parser-full # Full parser test suite (~5500 files, ~12 min)
make test-pp-full     # Full pretty-printer test (all CI files)
make clean            # Clean all build artifacts
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
