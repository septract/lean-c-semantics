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
├── cerberus/          # Git submodule - Cerberus C semantics tool (fork with JSON export)
├── docs/              # Documentation (YYYY-MM-DD_title.md format)
├── lean/CerbLean/     # Lean 4 project
│   ├── Core/          # Core AST types (Sym, Expr, File, etc.)
│   ├── CN/            # CN separation logic type system (Types/, TypeChecking/, Verification/, Semantics/)
│   ├── Parser.lean    # JSON parser
│   ├── PrettyPrint.lean # Pretty-printer matching Cerberus output
│   ├── Memory/        # Memory model (concrete with allocation-ID provenance)
│   ├── Semantics/     # Core interpreter
│   ├── Verification/  # Verified C programs with proofs
│   ├── GenProof.lean  # Generates proof skeleton files from Core JSON
│   └── Test/          # Unit tests + Test*.lean CLI entry points
├── scripts/           # Development scripts (all support --help)
├── tests/             # C test files for differential testing
│   ├── minimal/       # Core test suite (NNN-description.c)
│   ├── debug/         # Debug/investigation tests (category-NN-description.c)
│   ├── coverage/      # Cerberus code coverage tests (category-NNN-description.c)
│   ├── cn/            # CN verification tests
│   └── csmith/        # Csmith fuzz testing infrastructure
├── Dockerfile         # Multi-stage build for Cerberus + Lean
├── CLAUDE.md          # This file
└── TODO.md            # Current tasks
```

## Key Design Decisions

### CRITICAL: Interpreter Must Match Cerberus EXACTLY

**The Lean interpreter MUST mirror Cerberus semantics EXACTLY.**

- Each function must be auditable against the corresponding Cerberus code
- NO innovation or "improvements" - only faithful translation
- Any deviation from Cerberus must be explicitly signed off by the user
- When in doubt, copy Cerberus's approach exactly
- Document correspondence with comments linking to Cerberus source (file:lines)

See `docs/2025-12-31_INTERPRETER_REFACTOR.md` for the audit checklist.
See `docs/2026-01-01_MEMORY_AUDIT.md` for the memory model correspondence mapping.

### CRITICAL: CN Implementation Must Match CN EXACTLY

**The Lean CN type system and type checker MUST mirror the CN implementation EXACTLY.**

- Type definitions must match CN's OCaml types (in `lib/baseTypes.ml`, `lib/indexTerms.ml`, etc.)
- Type checking functions must match CN's OCaml implementation - no "improvements" or alternative designs
- Each type and function must be auditable against the corresponding CN code
- Document correspondence with comments linking to CN source (file:lines)
- Every function should have: module-level comment, docstring linking to CN function, "Audited: YYYY-MM-DD" note

Key CN source files: `cn/lib/baseTypes.ml`, `indexTerms.ml`, `check.ml`, `typing.ml`, `wellTyped.ml`, `resourceInference.ml`, `core_to_mucore.ml`, `compile.ml`. CN repo: https://github.com/rems-project/cn (clone to `tmp/cn/` if needed).

### Other Design Choices

Manual Lean translation (not Lem/Ott backends) of Cerberus Core semantics, using JSON export from Cerberus. Concrete memory model with allocation-ID provenance matching `impl_mem.ml`. Sequential execution with `Eunseq` race detection via neg action transformation; parallel semantics (`Epar`, `Ewait`) out of scope.

## Cerberus Reference

### CRITICAL: Deprecated Files

**`cerberus/frontend/model/core_run.lem` is DEPRECATED and will be removed.**

Always refer to **`core_reduction.lem`** for:
- Small-step dynamics of effectful Core expressions
- Neg action transformation (unsequenced race handling)
- Contextual decomposition (`get_ctx`, `apply_ctx`)

The driver (`driver.lem`) uses `core_reduction.lem`, NOT `core_run.lem`.

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

### Known Cerberus Issues

**Non-determinism**: Cerberus exhibits non-deterministic behavior on certain tests (e.g., pr34099.c, pr43629.c). The same test may succeed or fail between runs.

**Unsequenced race detection**: Fully supported via `core_reduction.lem`. Tests in `cerberus/tests/ci/030*-unseq_race*.c` should detect UB035.

### Cerberus Setup

**IMPORTANT**: Cerberus requires OCaml 5.4.0 (configured in Makefile via `OCAML_VERSION`).

```bash
make cerberus-setup    # First-time: creates local opam switch, installs deps, builds
./scripts/cerberus --exec cerberus/tests/ci/0001-emptymain.c  # Verify
```

After modifying Cerberus source:
```bash
make cerberus          # Runs lem + dune build
```

### Running Cerberus

Use the wrapper script `scripts/cerberus` (uses local opam switch):
```bash
./scripts/cerberus --pp=core input.c                    # Pretty-print Core
./scripts/cerberus --pp=core --pp_core_compact input.c  # Compact mode (for diffing)
./scripts/cerberus --json_core_out=output.json input.c  # Export Core as JSON
./scripts/cerberus --exec input.c                       # Execute C program
./scripts/cerberus --exec --batch input.c               # Batch output (differential testing)
```

## Validation

Cerberus has 5500+ test files in `cerberus/tests/`: `tests/ci/*.c` (main CI tests), `*.undef.c` (expected UB), `*.syntax-only.c` (parse-only).

### Test Scripts

**Parser Test** (`scripts/test_parser.sh`):
```bash
./scripts/test_parser.sh --quick    # Test first 100 files
./scripts/test_parser.sh            # Full test suite (~5500 files)
./scripts/test_parser.sh --max 500  # Test first 500 files
```

**Pretty-Printer Test** (`scripts/test_pp.sh`):
```bash
./scripts/test_pp.sh --max 100      # Test first 100 files
./scripts/test_pp.sh --max 100 -v   # Verbose mode (show each file)
./scripts/test_pp.sh                # Full test (all CI files)
```

**Investigating PP Mismatches**: Do NOT use `diff` - it doesn't normalize whitespace. Use the `--compare` flag:
```bash
./lean/.lake/build/bin/cerblean_pp /path/to/OUTPUT_DIR/filename.json --compare /path/to/OUTPUT_DIR/filename.cerberus.core
```

**Memory Model Tests** (`make test-memory`):
```bash
make test-memory                           # Run memory model unit tests
cd lean && .lake/build/bin/cerblean_memtest # Run directly
```

**CN Verification Tests** (`make test-cn`):
```bash
make test-cn                              # Run all CN integration tests (nolibc + libc)
make test-cn-nolibc                       # Run integration tests (fast, --nolibc)
make test-cn-libc                         # Run libc-only tests (*.libc.* files)
make test-cn-unit                         # Run unit tests only (fast, no Cerberus)
./scripts/test_cn.sh --nolibc             # Run tests without libc (skips *.libc.* tests)
./scripts/test_cn.sh                      # Run all tests in tests/cn/
./scripts/test_cn.sh /path/to/test.c      # Run a specific test
./scripts/test_cn.sh --unit               # Run unit tests only
```

CN test file conventions: `NNN-description.c` (pass), `NNN-description.fail.c` (expected fail), `NNN-description.libc.fail.c` (expected-fail requiring libc, skipped with --nolibc), `NNN-description.smt-fail.c` (SMT-level fail). The `.fail.c` and `.smt-fail.c` suffixes auto-pass `--expect-fail`.

**Cerberus OCaml Code Coverage** (`scripts/test_coverage.sh`):
```bash
make cerberus-coverage-setup              # One-time setup
./scripts/test_coverage.sh               # Build instrumented Cerberus, run tests, generate report
./scripts/test_coverage.sh --no-build    # Reuse previous instrumented build
./scripts/test_coverage.sh --ci          # Also include Cerberus CI suite
```
Generates HTML report at `_coverage/index.html`. See `docs/2026-02-14_CERBERUS_COVERAGE.md` for details.

**Csmith Fuzz Testing** (`scripts/fuzz_csmith.sh`):
```bash
./scripts/fuzz_csmith.sh                  # Generate and test 100 random programs
./scripts/fuzz_csmith.sh 500              # Test N random programs
./scripts/fuzz_csmith.sh 100 tests/csmith/my_results  # Specify output directory
./scripts/gen_csmith.sh 12345 tests/csmith/debug.c    # Single test for debugging
```
**IMPORTANT**: Any difference from Cerberus (FAIL, MISMATCH, DIFF) is a BUG.

**creduce** (`scripts/creduce_interestingness.sh`): Minimizes failing tests to smallest reproducer.
```bash
creduce ./scripts/creduce_interestingness.sh test.c
```

### Differential Testing (`scripts/test_interp.sh`)

```bash
./scripts/test_interp.sh tests/debug                   # Test debug suite
./scripts/test_interp.sh tests/coverage -v             # Test coverage suite
./scripts/test_interp.sh cerberus/tests --nolibc -v    # Full Cerberus suite
```

`--nolibc` is much faster (2MB vs 200MB JSON per test) but many tests require libc. Full suite is expensive (1-2 hours) - only run when user explicitly requests it.

Auto-skipped: `*.syntax-only.c`, `*.exhaust.c`, `bmc/`, `cheri-ci/`, `csmith/`, `pnvi_testsuite/`.

### Test Files (`tests/`)

**Naming conventions:**
- `tests/minimal/`: `NNN-description.c` (e.g., `001-return-literal.c`, `068-div-by-zero.undef.c`)
- `tests/debug/`: `category-NN-description.c` (e.g., `conv-01-neg-to-unsigned.c`, `ptr-03-no-decr.c`)
- `tests/coverage/`: `category-NNN-description.c` - targets specific Cerberus code paths

**Special file suffixes:**
- `.undef.c` — tests for undefined behavior detection
- `.libc.c` — requires libc (skipped with `--nolibc`)
- `.unsupported.c` — expected to fail due to unimplemented features. Reported as `UNSUPPORTED` (not `FAIL`), doesn't trigger non-zero exit. If unexpectedly passes: `UNSUPPORTED_PASS`.

**Debugging strategy:**
1. Create a minimal reproducer in `tests/debug/` with an appropriate category prefix
2. Run `./scripts/test_interp.sh tests/debug` to compare against Cerberus
3. Debug tests should be committed for future regression testing
4. Once fixed, consider adding to `tests/minimal/` if it covers a new case

## Program Verification

Proves properties of C programs in Lean using interpreter semantics. Programs are embedded as Core AST definitions; UB-freedom and return values proven via `native_decide`.

```
C source → Cerberus → Core JSON → strip_core_json.py → GenProof → Lean file with proof stubs
                                                                          ↓
                                                        Fill proofs (native_decide or Aristotle)
```

```bash
make test-genproof                                                          # CI test
./scripts/test_genproof.sh tests/minimal/001-return-literal.c               # Quick test
./scripts/test_genproof.sh tests/minimal/001-return-literal.c --production  # Generate to Verification/Programs/
python3 scripts/strip_core_json.py input.json output.json                   # Strip unused functions
python3 scripts/strip_core_json.py --aggressive input.json output.json      # Also strip locations
```

**Limitations**: `native_decide` only works for concrete programs (no inputs). Large programs may time out.

**Aristotle-Generated Proofs**: [Aristotle](https://aristotle.harmonic.fun) can auto-generate Lean 4 proofs. Always add attribution comments:
```lean
theorem my_theorem : P := by
  -- Proof generated by Aristotle (project: cf869c1a-...)
```
MCP server: https://github.com/septract/lean-aristotle-mcp

## Development Notes

### ⚠️ ABSOLUTE RULE: Fail, Never Guess

**It is ALWAYS better to fail than to be incorrect. NEVER approximate. NEVER guess. NEVER add fall-through cases. This is the single most important rule in this codebase.**

This applies to EVERYTHING: parser, interpreter, type checker, memory model. No exceptions.

**The rule is simple**: If the code doesn't know the correct answer, it MUST fail. Returning a wrong answer - even one that "might work" - is absolutely forbidden.

```lean
-- ❌ FORBIDDEN: fall-through / catch-all cases
| _ => someValue
| _, _ => defaultResult

-- ❌ FORBIDDEN: guessing when information is missing
| none => assumedDefault

-- ❌ FORBIDDEN: .getD with default values (VERY COMMON VIOLATION)
pe.ty.map convertType |>.getD .unit   -- NO! Silently defaults to unit
option.getD defaultValue              -- NO! Propagate the none instead
```

**Dangerous patterns**: `.getD` silently swallows missing information (caused 15+ violations in one audit). Using `.unit` as a default type is especially insidious - it compiles fine but corrupts type information. Same for `Int` as default SMT sort, `true`/`false` as default booleans, `[]` as default lists.

The ONLY acceptable behavior when the correct answer is unknown:
```lean
| _ => throw "unhandled case: ..."
| _ => .error "unexpected: ..."
| _ => throw "not yet implemented: ..."  -- for incomplete implementations
| none => none  -- propagate the unknown
| _ => panic! "impossible case" -- if truly impossible
```

**Incomplete implementations** MUST fail explicitly with `throw "not yet implemented: X"`, not guess.

**Why this matters**: This project implements formal semantics. Wrong answers hide bugs, are nearly impossible to debug, compound silently, and undermine the entire purpose of formal verification. A failure is immediately visible and fixable; an incorrect result can hide for months.

**If you find yourself writing `| _ =>` that returns a value (not an error), STOP.** See `docs/2026-02-01_CN_ANTIPATTERN_AUDIT.md` for 48 violations found in one audit.

#### Never Silently Swallow Errors

Never catch an error and substitute a default value:
```lean
-- FORBIDDEN
| .error _ => .ok Loc.unknown
| .error _ => .ok defaultValue
| .error _ => pure []
```

The ONLY acceptable error catching is trying alternative strategies that still propagate errors:
```lean
match parseFormatA x with
| .ok v => .ok v
| .error _ => parseFormatB x  -- still returns Except
```

We discovered the parser was completely broken for structured locations but all tests passed because errors silently became `Loc.unknown`.

---

### CRITICAL: Never Undo Changes Without Permission
**NEVER revert, undo, or `git checkout` any changes without explicit user confirmation.**

### CRITICAL: Never Commit Without Running Tests
**NEVER commit changes without first running `make test`.**

### ABSOLUTE RULE: NEVER Modify Tests to Achieve a Pass

**NEVER modify, weaken, or remove a test to make it pass.** Fix the implementation instead.

The ONLY acceptable reasons to modify a test:
1. The test itself has a bug (wrong expected behavior)
2. Requirements have genuinely changed (confirmed by user)
3. Adding MORE coverage to an existing test

### ABSOLUTE RULE: Backwards Compatibility is an Anti-Goal

**Backwards compatibility with previous versions of our own code is an ANTI-GOAL.** The ONLY source of truth is Cerberus and CN. If our implementation diverges, it is WRONG and must be fixed, even if it breaks tests, changes behavior, or invalidates proofs. Fix it immediately. There is no "deprecation period" for incorrect semantics.

### Marking Known Divergences: `DIVERGES-FROM-CN`

When our implementation intentionally diverges from CN or Cerberus (e.g., missing padding handling, simplified rollback), mark the code with a `DIVERGES-FROM-CN` comment. This makes divergences greppable and ensures they get revisited.

**Format**:
```lean
-- DIVERGES-FROM-CN: <short description of what CN does differently>
```

**Rules**:
- Every `DIVERGES-FROM-CN` must explain what CN does and how we differ
- The divergence must be **intentional and justified** (e.g., internally consistent simplification, feature not yet needed). If it's not justified, fix it instead of marking it
- Divergences that would cause **incorrect results** are NOT acceptable — those must be fixed immediately. `DIVERGES-FROM-CN` is only for cases where our behavior is correct but less complete than CN
- Periodically grep for `DIVERGES-FROM-CN` to audit and close gaps

**Example**:
```lean
-- DIVERGES-FROM-CN: CN's unpack_owned (pack.ml:113-124) also produces padding
-- resources (Owned<char[N]>(Uninit) at padding offsets). We only produce member
-- resources. Internally consistent since tryRepackStruct also skips padding.
let fieldResources := fields.filterMap fun (field : FieldDef) =>
```

### Marking Bugs Found During Audit: `FIXME`

When you spot a bug or incorrect behavior during an audit but can't fix it on the spot, mark it with `FIXME`. This is for things that are **actually wrong** — not intentional simplifications (use `DIVERGES-FROM-CN` for those).

**Format**:
```lean
-- FIXME: <what's wrong and why it matters>
```

**Rules**:
- `FIXME` means the code produces or could produce **incorrect results**. Fix ASAP
- Must explain what's wrong, not just flag the line
- If you can fix it now, fix it instead of tagging it
- Periodically grep for `FIXME` — the count should trend toward zero

**Distinction from `DIVERGES-FROM-CN`**:

| Tag | Meaning | Correct? | Action |
|-----|---------|----------|--------|
| `DIVERGES-FROM-CN` | Intentional, behavior correct but incomplete | Yes | Revisit when needed |
| `FIXME` | Bug or incorrect behavior | No | Fix ASAP |

**Example**:
```lean
-- FIXME: we compare Sym by id only, but CN uses digest+id (Sym.equal).
-- This could match the wrong symbol if two syms share an id but differ in digest.
if sym1.id == sym2.id then
```

### Always Use Build Targets for Testing
**Always use Makefile targets** (`make test`, `make test-cn`, etc.) rather than invoking test binaries directly.

### Shell Commands
Do NOT use `sed`, `awk`, `tr` for ad-hoc text processing. NEVER use `sed -n 'X,Yp'` to read files - use the Read tool. Run long-running commands in the background.

### Git Commits and the Sandbox

**Use regular double-quoted strings for commit messages**, not heredocs (sandbox breaks `$(cat <<'EOF')`).

For submodule commits: `cd` into submodule, commit, **push submodule first**, then commit/push parent reference.

### Building

```bash
make lean             # Build Lean project
make cerberus         # Build Cerberus (NOT 'dune build' - avoids z3/coq deps)
make clean            # Clean all build artifacts
make test-unit        # Unit tests (no Cerberus required)
make test-memory      # Memory model unit tests only
make test             # Quick tests: unit + 100 parser + 100 PP files
make test-parser-full # Full parser test (~5500 files, ~12 min)
make test-pp-full     # Full pretty-printer test (all CI files)
```

### Docker

```bash
docker pull ghcr.io/septract/lean-c-semantics:main
alias cerblean='docker run --rm -v "$(pwd):$(pwd)" -w "$(pwd)" ghcr.io/septract/lean-c-semantics:main'
cerblean program.c              # Execute with Lean interpreter
cerblean --batch program.c      # Machine-readable output
cerblean --cerberus program.c   # Run Cerberus only
cerblean --json program.c       # Output Core IR as JSON
cerblean --nolibc program.c     # Skip libc (faster)
docker build -t cerblean .      # Build locally
```

## Documentation

Docs may be out of date - the date prefix indicates creation date. All docs use `YYYY-MM-DD_title.md` format.

## References
- [Cerberus Project](https://github.com/rems-project/cerberus)
- [Lem Language](https://github.com/rems-project/lem)
- [Ott Tool](https://github.com/ott-lang/ott)
- [Lean 4](https://lean-lang.org/)
