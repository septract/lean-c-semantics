# Lean C Semantics

## Overview
A Lean 4 implementation of C semantics via Cerberus. Cerberus compiles C to its Core intermediate representation; this project parses and executes Core in Lean, enabling formal reasoning about C programs.

## Architecture

### Pipeline
```
C source → Cerberus → Core IR (JSON) → Lean Parser → Lean AST → Lean Interpreter
```

### Key Components
- **Cerberus** (submodule): C frontend that produces Core IR
- **Lean Parser**: Parses JSON-serialized Core into Lean types
- **Lean Interpreter**: Executes Core programs with configurable memory model

## Project Structure
```
lean-c-semantics/
├── cerberus/          # Git submodule - Cerberus C semantics tool (fork with JSON export)
├── docs/
│   └── DETAILED_PLAN.md   # Full implementation roadmap
├── lean/              # Lean 4 project
│   └── CToLean/
│       ├── Core/      # Core AST types
│       ├── Parser.lean      # JSON parser (100% success on test suite)
│       ├── PrettyPrint.lean # Pretty-printer matching Cerberus output
│       ├── Memory/    # Memory model (concrete with allocation-ID provenance)
│       ├── Semantics/ # Interpreter
│       ├── Test/      # Unit tests (Memory, Parser smoke tests)
│       └── Test*.lean # Test CLI entry points
├── scripts/           # Development scripts
│   ├── test_parser.sh # Run parser against Cerberus test suite
│   └── test_pp.sh     # Run pretty-printer comparison tests
├── tests/             # C test files for differential testing
│   ├── minimal/       # Core test suite (NNN-description.c)
│   ├── debug/         # Debug/investigation tests (category-NN-description.c)
│   └── csmith/        # Csmith fuzz testing infrastructure
├── CLAUDE.md          # This file
└── TODO.md            # Current tasks
```

## Key Design Decisions

### 0. CRITICAL: Interpreter Must Match Cerberus EXACTLY

**The Lean interpreter MUST mirror Cerberus semantics EXACTLY.**

- Each function must be auditable against the corresponding Cerberus code
- NO innovation or "improvements" - only faithful translation
- Any deviation from Cerberus must be explicitly signed off by the user
- When in doubt, copy Cerberus's approach exactly
- Document correspondence with comments linking to Cerberus source (file:lines)

This is not about writing "good Lean code" - it's about creating a verifiable translation that can be audited for correctness against the Cerberus reference implementation.

See `docs/INTERPRETER_REFACTOR.md` for the audit checklist and correspondence documentation requirements.

See `docs/MEMORY_AUDIT.md` for the memory model audit plan and Cerberus correspondence mapping.

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

### Cerberus Setup

**IMPORTANT**: Cerberus requires OCaml 4.14.1. It crashes on OCaml 5.x.

First-time setup:
```bash
make cerberus-setup
```
This creates the `cerberus-414` opam switch, installs dependencies, and builds Cerberus locally.

Verify it works:
```bash
./scripts/cerberus --exec cerberus/tests/ci/0001-emptymain.c
```

### Updating Cerberus After Local Changes

If you modify Cerberus source code (in `cerberus/`), rebuild:
```bash
make cerberus
```
This runs `lem` (to update OCaml sources) and `dune build`.

### Running Cerberus

Use the wrapper script `scripts/cerberus` (which uses `dune exec`):
```bash
# Pretty-print Core to stdout
./scripts/cerberus --pp=core input.c

# Pretty-print Core in compact mode (single line, for diffing)
./scripts/cerberus --pp=core --pp_core_compact input.c

# Export Core as JSON (for Lean parser)
./scripts/cerberus --json_core_out=output.json input.c

# Execute C program
./scripts/cerberus --exec input.c

# Execute with batch output (for differential testing)
./scripts/cerberus --exec --batch input.c

# Get help
./scripts/cerberus --help
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

**Csmith Fuzz Testing** (`scripts/fuzz_csmith.sh`):
Generates random C programs with csmith and compares Cerberus vs our interpreter.
```bash
# Generate and test 100 random programs (default)
./scripts/fuzz_csmith.sh

# Generate and test N random programs
./scripts/fuzz_csmith.sh 500

# Specify output directory
./scripts/fuzz_csmith.sh 100 tests/csmith/my_results
```

The script:
1. Generates random csmith tests with `--no-argc --no-bitfields`
2. Replaces csmith.h with our `csmith_cerberus.h` (uses exit() instead of printf)
3. Runs `test_interp.sh` on all generated tests
4. Saves bugs to `bugs/` subdirectory, timeouts to `timeouts/`

Output categories in `fuzz_log.txt`:
- **MATCH**: Both interpreters return the same value (good!)
- **FAIL**: **BUG** - Lean interpreter error when Cerberus succeeded
- **MISMATCH**: **BUG** - Different concrete values between interpreters
- **DIFF**: **BUG** - One detected UB, the other didn't
- **TIMEOUT**: Lean took too long (may need more fuel)

**IMPORTANT**: Any difference from Cerberus (FAIL, MISMATCH, DIFF) is a BUG! The script exits with code 1 if any bugs are found.

Generate a single csmith test for debugging:
```bash
./scripts/gen_csmith_test.sh 12345 tests/csmith/debug.c
./scripts/test_interp.sh tests/csmith/debug.c
```

**Known csmith limitations**:
- Many csmith tests fail Cerberus compilation due to pointer type strictness
- Tests using unions may show DIFF (Unspecified vs concrete) - we don't track active union member
- Large tests may exhaust interpreter fuel (TIMEOUT, not necessarily a bug)

### Differential Testing
Compare Lean interpreter output against Cerberus:
1. Run Cerberus on C file, get Core + execution result
2. Parse Core in Lean
3. Execute in Lean interpreter
4. Compare results (return value, UB detection)

Target: 90%+ agreement on sequential tests.

### Test Files (`tests/`)

**Naming conventions:**
- `tests/minimal/`: Core test suite with numbered files: `NNN-description.c`
  - Examples: `001-return-literal.c`, `068-div-by-zero.undef.c`
  - Files with `.undef.c` suffix test undefined behavior detection
- `tests/debug/`: Debug/investigation tests: `category-NN-description.c`
  - Examples: `conv-01-neg-to-unsigned.c`, `ptr-03-no-decr.c`, `struct-01-init.c`
  - Categories group related tests (conv, ptr, rec, struct, etc.)

**Debugging strategy:**
When investigating a bug or unexpected behavior:
1. Create a minimal reproducer in `tests/debug/` with an appropriate category prefix
2. Run `./scripts/test_interp.sh tests/debug` to compare against Cerberus
3. Debug tests should be committed for future regression testing
4. Once fixed, consider adding to `tests/minimal/` if it covers a new case

## Development Notes

### ABSOLUTE RULE: NEVER Silently Swallow Errors

**NEVER EVER catch an error and silently substitute a default value. NEVER. UNDER ANY CIRCUMSTANCES. This applies to the ENTIRE project - parser, interpreter, memory model, everything.**

This is absolutely forbidden:
```lean
-- FORBIDDEN - NEVER DO THIS
| .error _ => .ok Loc.unknown
| .error _ => .ok defaultValue
| .error _ => pure []
match parse x with | .error _ => someDefault | .ok v => v
```

The ONLY acceptable use of error catching is for local control flow where you have an alternative strategy that still propagates errors:
```lean
-- OK: trying alternative strategies, error still propagates
match parseFormatA x with
| .ok v => .ok v
| .error _ => parseFormatB x  -- still returns Except, error propagates
```

If something fails, the error MUST propagate. Period. No exceptions. No "reasonable defaults." No "it's just a location, it doesn't matter." No "this field is optional so we'll just use empty." NOTHING.

Silent error swallowing hides bugs. We discovered the parser was completely broken for structured locations but all tests passed because errors silently became `Loc.unknown`. This is unacceptable.

### CRITICAL: Never Undo Changes Without Permission
**NEVER revert, undo, or `git checkout` any changes without explicit user confirmation.** Even if you think a change caused a problem, ASK FIRST before reverting. The user may have made intentional changes you're not aware of.

### Shell Commands
**IMPORTANT**: Do NOT use `sed`, `awk`, `tr`, or similar shell string manipulation tools for ad-hoc text processing. These commands are error-prone and often fail silently or produce unexpected results across different platforms.

**CRITICAL**: NEVER use `sed -n 'X,Yp'` or similar to read file contents. ALWAYS use the Read tool to read files. The Read tool is reliable and works consistently.

If string manipulation is needed:
- Write a proper Lean program to do the transformation
- Or wrap the shell commands in a well-designed, tested shell script in `scripts/`

### Building

Use the top-level Makefile:
```bash
make lean             # Build Lean project
make cerberus         # Build Cerberus (requires opam environment)
make clean            # Clean all build artifacts

# Testing (no Cerberus required)
make test-unit        # Run all unit tests (parser smoke + memory)
make test-memory      # Run memory model unit tests only

# Testing (requires Cerberus)
make test             # Quick tests: unit + 100 parser + 100 PP files
make test-parser-full # Full parser test suite (~5500 files, ~12 min)
make test-pp-full     # Full pretty-printer test (all CI files)
```

See `docs/TESTING.md` for full testing documentation.

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
