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
├── docs/              # Documentation (YYYY-MM-DD_title.md format)
│   └── 2025-12-24_DETAILED_PLAN.md   # Full implementation roadmap
├── lean/              # Lean 4 project
│   └── CerbLean/
│       ├── Core/      # Core AST types
│       ├── Parser.lean      # JSON parser (100% success on test suite)
│       ├── PrettyPrint.lean # Pretty-printer matching Cerberus output
│       ├── Memory/    # Memory model (concrete with allocation-ID provenance)
│       ├── Semantics/ # Interpreter
│       ├── Verification/    # Verified C programs (see Program Verification section)
│       │   └── Programs/    # Individual verified programs
│       ├── GenProof.lean    # Generates proof skeleton files from Core JSON
│       ├── Test/      # Unit tests (Memory, Parser smoke tests)
│       └── Test*.lean # Test CLI entry points
├── scripts/           # Development scripts
│   ├── test_parser.sh # Run parser against Cerberus test suite
│   ├── test_pp.sh     # Run pretty-printer comparison tests
│   ├── test_interp.sh # Run interpreter differential testing
│   ├── test_genproof.sh # Test proof generation pipeline
│   ├── strip_core_json.py # Strip Core JSON to minimal dependencies (for smaller proofs)
│   ├── fuzz_csmith.sh # Fuzz testing with csmith
│   ├── creduce_interestingness.sh # For minimizing failing tests with creduce
│   └── docker_entrypoint.sh # Docker container entrypoint
├── tests/             # C test files for differential testing
│   ├── minimal/       # Core test suite (NNN-description.c)
│   ├── debug/         # Debug/investigation tests (category-NN-description.c)
│   └── csmith/        # Csmith fuzz testing infrastructure
├── .github/workflows/ # CI/CD workflows
│   ├── ci.yml         # Build and test on push/PR
│   └── docker.yml     # Build and push Docker image
├── Dockerfile         # Multi-stage build for Cerberus + Lean
├── .dockerignore      # Files excluded from Docker build context
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

See `docs/2025-12-31_INTERPRETER_REFACTOR.md` for the audit checklist and correspondence documentation requirements.

See `docs/2026-01-01_MEMORY_AUDIT.md` for the memory model audit plan and Cerberus correspondence mapping.

### 0.1 CRITICAL: CN Types Must Match CN Implementation EXACTLY

**The Lean CN type system MUST mirror the CN implementation EXACTLY.**

- Type definitions must match CN's OCaml types (in `lib/baseTypes.ml`, `lib/indexTerms.ml`, etc.)
- Implementation strategy must follow CN's approach - no "improvements" or alternative designs
- Each type and function must be auditable against the corresponding CN code
- Document correspondence with comments linking to CN source (file:lines)
- This allows us to reuse CN's theory and proofs

Example audit comment:
```lean
-- CN: lib/baseTypes.ml lines 15-30
inductive BaseType where
  | Unit
  | Bool
  ...
```

Key CN source files for reference:
| File | Purpose |
|------|---------|
| `cn/lib/baseTypes.ml` | CN base types |
| `cn/lib/indexTerms.ml` | Index term representation |
| `cn/lib/argumentTypes.ml` | Function spec structure |
| `cn/lib/logicalReturnTypes.ml` | Postcondition structure |
| `cn/lib/logicalConstraints.ml` | Constraint representation |
| `cn/lib/resource.ml` | Ownership predicates |
| `cn/lib/request.ml` | Resource requests |

**CN Repository**: The CN source is available at https://github.com/rems-project/cn. If needed for reference, clone it to `tmp/cn/`:
```bash
mkdir -p tmp && cd tmp && git clone --depth 1 https://github.com/rems-project/cn.git
```

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
- Parallel semantics (`Epar`, `Ewait`) deferred
- Note: Unsequenced expressions (`Eunseq`) are now fully supported with race detection

## Cerberus Reference

### CRITICAL: Deprecated Files

**`cerberus/frontend/model/core_run.lem` is DEPRECATED and will be removed.**

Always refer to **`core_reduction.lem`** for:
- Small-step dynamics of effectful Core expressions
- Neg action transformation (unsequenced race handling)
- Contextual decomposition (`get_ctx`, `apply_ctx`)

The driver (`driver.lem`) uses `core_reduction.lem`, NOT `core_run.lem`.

(Confirmed by Cerberus developers, January 2026)

### Key Files
| File | Description |
|------|-------------|
| `cerberus/frontend/ott/core-ott/core.ott` | Core AST grammar (~600 lines) |
| `cerberus/frontend/model/core_reduction.lem` | **PRIMARY**: Small-step reduction semantics |
| `cerberus/frontend/model/core_run.lem` | **DEPRECATED** - do not use |
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

### Known Cerberus Issues

**Non-determinism**: Cerberus exhibits non-deterministic behavior on certain tests. The same test may succeed on one run and fail on another with errors like "calling an unknown procedure". This has been observed on tests like pr34099.c and pr43629.c. **TODO**: Investigate the source of this non-determinism in the future.

**Unsequenced race detection**: We now support `Eunseq` expressions and detect unsequenced races following `core_reduction.lem`. The neg action transformation creates `unseq` structures that accumulate memory footprints, and race detection happens at `Eunseq` completion via `one_step_unseq_aux`. Tests in `cerberus/tests/ci/030*-unseq_race*.c` should detect UB035.

### Cerberus Setup

**IMPORTANT**: Cerberus requires OCaml 4.14.1 or 5.4.0+. The version is configured in the Makefile via `OCAML_VERSION`.

First-time setup:
```bash
make cerberus-setup
```
This creates a **local opam switch** in `cerberus/_opam/`, installs dependencies, and builds Cerberus locally.

**Benefits of local switches:**
- Each checkout can have its own isolated OCaml environment
- Multiple development versions can coexist without conflicts
- The switch is scoped to this project directory

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

Use the wrapper script `scripts/cerberus` (which uses the local opam switch):
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

See `docs/2025-12-26_PP_DISCREPANCIES.md` for remaining issues (NULL type parsing for complex types - deferred pending Cerberus-side fix).

**Memory Model Tests** (`make test-memory`):
Unit tests for the memory model implementation.
```bash
make test-memory                           # Run memory model unit tests
cd lean && .lake/build/bin/cerblean_memtest # Run directly
```
Tests include: layout (sizeof/alignof), allocation, store/load roundtrip, null dereference detection, use-after-free detection, double-free detection, out-of-bounds detection, read-only protection, pointer arithmetic.

**Investigating Pretty-Printer Mismatches**:
The test script outputs files to a temp directory. To investigate a specific mismatch:
```bash
# Run tests and note the output directory
./scripts/test_pp.sh --max 250

# Use the Lean comparison tool directly (normalizes whitespace, strips section comments)
./lean/.lake/build/bin/cerblean_pp /path/to/OUTPUT_DIR/filename.json --compare /path/to/OUTPUT_DIR/filename.cerberus.core

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

**Using creduce to minimize failing tests** (`scripts/creduce_interestingness.sh`):
When you find a complex failing test (from csmith or elsewhere), use creduce to automatically minimize it to the smallest reproducer:

```bash
# 1. Copy the failing test to /tmp
cp path/to/failing_test.c /tmp/test.c

# 2. Verify the interestingness test works on your file
cd /tmp
/path/to/project/scripts/creduce_interestingness.sh test.c
echo $?  # Should print 0 if the bug reproduces

# 3. Run creduce to minimize
creduce /path/to/project/scripts/creduce_interestingness.sh test.c

# 4. The minimized test is now in test.c - save it to tests/debug/
cp test.c /path/to/project/tests/debug/category-NN-description.c
```

The interestingness script (`scripts/creduce_interestingness.sh`):
- Returns 0 (interesting) if: Cerberus succeeds but Lean reports an error
- Returns 1 (not interesting) otherwise
- Has built-in 10-second timeouts to handle infinite loops creduce might create

Customize the script for different bug patterns:
- Change the grep pattern to match different error types
- Modify success conditions (e.g., mismatch instead of error)

Example: minimizing a "out of bounds" bug:
```bash
# The default script looks for "out of bounds" errors
# Edit the script to match your specific error if needed:
if echo "$LEAN_OUT" | grep -q "your error pattern"; then
    exit 0  # Interesting
fi
```

### Differential Testing
Compare Lean interpreter output against Cerberus:
1. Run Cerberus on C file, get Core + execution result
2. Parse Core in Lean
3. Execute in Lean interpreter
4. Compare results (return value, UB detection)

Target: 90%+ agreement on sequential tests.

**Generating a full test log:**
```bash
./scripts/test_interp.sh cerberus/tests --nolibc -v 2>&1 | tee logs/interp-full-$(date +%Y%m%d-%H%M%S).log
```

**Note:** Using `--nolibc` is much faster (2MB vs 200MB JSON per test) but many Cerberus tests will fail at the Cerberus stage because they require libc functions. This is expected - we're measuring match rate on tests that both interpreters can run.

**WARNING:** This is expensive (1-2 hours) and should only be run when the user explicitly requests it.

Note: The script automatically skips certain directories and file types:
- `*.syntax-only.c` - Parse-only tests (not executable)
- `*.exhaust.c` - Exhaustive interleaving tests
- `bmc/` - Bounded model checking tests (requires `--bmc` mode)
- `cheri-ci/` - CHERI memory model tests
- `csmith/` - Csmith tests (use `fuzz_csmith.sh` instead)
- `pnvi_testsuite/` - PNVI provenance tests

See `scripts/test_interp.sh` for the exact skip logic.

### Test Files (`tests/`)

**Naming conventions:**
- `tests/minimal/`: Core test suite with numbered files: `NNN-description.c`
  - Examples: `001-return-literal.c`, `068-div-by-zero.undef.c`
  - Files with `.undef.c` suffix test undefined behavior detection
  - Files with `.libc.c` suffix require libc (skipped with `--nolibc`)
- `tests/debug/`: Debug/investigation tests: `category-NN-description.c`
  - Examples: `conv-01-neg-to-unsigned.c`, `ptr-03-no-decr.c`, `struct-01-init.c`
  - Categories group related tests (conv, ptr, rec, struct, libc, etc.)

**Debugging strategy:**
When investigating a bug or unexpected behavior:
1. Create a minimal reproducer in `tests/debug/` with an appropriate category prefix
2. Run `./scripts/test_interp.sh tests/debug` to compare against Cerberus
3. Debug tests should be committed for future regression testing
4. Once fixed, consider adding to `tests/minimal/` if it covers a new case

## Program Verification

The project supports proving properties of C programs directly in Lean using the interpreter semantics. Programs are embedded as Lean definitions (Core AST), and properties like UB-freedom and return values can be proven using `native_decide`.

### Verification Pipeline

```
C source → Cerberus → Core JSON → strip_core_json.py → GenProof → Lean file with proof stubs
                                                                          ↓
                                                        Fill proofs (native_decide or Aristotle)
```

### Directory Structure

- `CerbLean/Verification/Programs/` - Verified C programs with proofs
  - `MinimalReturn.lean` - Hand-constructed program returning 42
  - `CountingLoop.lean` - Loop counting 0→3 with save/run pattern
  - `ReturnLiteral.lean` - Auto-generated from C, proven by Aristotle

### Proof Patterns

**UB-Freedom Proof** (no undefined behavior):
```lean
/-- Helper for native_decide -/
theorem program_noError_bool : (runMain program).error.isNone = true := by
  native_decide

/-- The program completes without undefined behavior -/
theorem program_noError : (runMain program).error = none := by
  have := @program_noError_bool
  cases h : (runMain program).error <;> simp_all
```

**Return Value Existence**:
```lean
theorem program_returns_expected :
    ∃ v, (runMain program).returnValue = some v := by
  have h_code : (runMain program).returnValue.isSome := by native_decide
  exact Option.isSome_iff_exists.mp h_code
```

### Generating Proof Files

**Using test_genproof.sh**:
```bash
# Test the full pipeline (temp directory, auto-cleanup)
./scripts/test_genproof.sh tests/minimal/001-return-literal.c

# Generate production file to Verification/Programs/
./scripts/test_genproof.sh tests/minimal/001-return-literal.c --production

# Options:
#   --nolibc       Use --nolibc with Cerberus (smaller JSON)
#   --no-strip     Skip JSON stripping step
#   --aggressive   Use aggressive stripping
#   --keep         Keep intermediate files
#   --production   Output to Verification/Programs/ with proper naming
#   -v, --verbose  Show verbose output
```

**Using GenProof directly**:
```bash
# Generate JSON from C
./scripts/cerberus --json_core_out=program.json tests/minimal/001-return-literal.c

# Optionally strip to reduce size
python3 scripts/strip_core_json.py program.json program_stripped.json

# Generate Lean proof file
./lean/.lake/build/bin/cerblean_genproof program_stripped.json lean/CerbLean/Verification/Programs/MyProgram.lean
```

The GenProof tool automatically generates proper namespaces from paths containing "CerbLean/" (e.g., `CerbLean.Verification.Programs.MyProgram`).

### JSON Stripping

The `strip_core_json.py` script removes unused stdlib functions and impl definitions from Core JSON, dramatically reducing file size and proof complexity.

```bash
# Basic stripping (removes unused functions)
python3 scripts/strip_core_json.py input.json output.json

# Aggressive stripping (also removes location info, descriptions)
python3 scripts/strip_core_json.py --aggressive input.json output.json

# Show what was removed
python3 scripts/strip_core_json.py -v input.json output.json
```

**Size reduction example:**
- Original JSON (with libc): ~200MB
- After stripping: ~40KB (for simple programs)
- With `--nolibc`: ~2MB → ~20KB

The stripper performs dependency analysis to keep only functions reachable from `main`, making the resulting Lean AST much more manageable for `native_decide` proofs.

### Limitations

- **`native_decide` only works for concrete programs**: Programs with no inputs can be fully evaluated at compile time. Programs with parameters or preconditions require symbolic reasoning.
- **Proof complexity**: Large programs may cause `native_decide` to time out or run out of memory.
- **Aristotle integration**: For complex proofs, the Aristotle theorem prover can fill `sorry` statements automatically.

### Testing the Pipeline

```bash
# CI test: verify genproof pipeline works
make test-genproof

# Quick test on a single file
./scripts/test_genproof.sh tests/minimal/001-return-literal.c --nolibc -v
```

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

### CRITICAL: Never Commit Without Running Tests
**NEVER commit changes without first running `make test`.** This ensures the build succeeds and all tests pass. A commit that breaks tests is unacceptable.

### Always Use Build Targets for Testing
**Always use Makefile targets** (e.g., `make test`, `make test-cn`) rather than invoking test binaries directly. Build targets ensure proper dependencies are built first and use the correct invocation.

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

See `docs/2025-12-31_TESTING.md` for full testing documentation.

Or build individually:
```bash
# Cerberus - use 'make cerberus', NOT 'dune build' (avoids z3/coq deps)
cd cerberus && make cerberus

# Lean
cd lean && lake build
```

### Docker

A Docker image is available that bundles Cerberus and the Lean interpreter.

**Using the published image:**
```bash
# Pull from GitHub Container Registry
docker pull ghcr.io/septract/lean-c-semantics:main

# Run on a C file (mount current directory)
docker run --rm -v "$(pwd):$(pwd)" -w "$(pwd)" ghcr.io/septract/lean-c-semantics:main program.c

# Recommended: create an alias for convenience
alias cerblean='docker run --rm -v "$(pwd):$(pwd)" -w "$(pwd)" ghcr.io/septract/lean-c-semantics:main'
cerblean program.c
```

**Container options:**
```bash
cerblean program.c              # Execute with Lean interpreter
cerblean --batch program.c      # Machine-readable output (for scripts)
cerblean --cerberus program.c   # Run Cerberus only (for comparison)
cerblean --json program.c       # Output Core IR as JSON
cerblean --nolibc program.c     # Skip libc (faster, but limited)
cerblean --help                 # Show all options
```

**Building locally:**
```bash
docker build -t cerblean .
docker run --rm -v "$(pwd):$(pwd)" -w "$(pwd)" cerblean program.c
```

**Layer caching:** The Dockerfile is optimized for incremental rebuilds:
- Lean toolchain download is cached unless `lean-toolchain` changes
- Cerberus opam dependencies are cached unless `*.opam` files change
- Source changes only trigger rebuilds, not dependency re-downloads

**CI/CD:** The `.github/workflows/docker.yml` workflow:
- Builds and pushes to GHCR on pushes to `main`
- Creates versioned tags on `v*` releases (e.g., `v0.1.0` → `:0.1.0`, `:0.1`)
- PRs only build (no push) to validate the Dockerfile

## Documentation

**Note:** Documentation may be out of date. The date prefix indicates when the document was created - consider this when reading older docs as the codebase may have evolved since then.

### Naming Convention
All documentation files in `docs/` should use date-prefixed names:
```
YYYY-MM-DD_title.md
```
Examples:
- `2026-01-16_TODO_AUDIT.md`
- `2026-01-02_FULL_TEST_RESULTS.md`

This ensures documents are chronologically ordered and clearly dated.

## References
- [Cerberus Project](https://github.com/rems-project/cerberus)
- [Lem Language](https://github.com/rems-project/lem)
- [Ott Tool](https://github.com/ott-lang/ott)
- [Lean 4](https://lean-lang.org/)
