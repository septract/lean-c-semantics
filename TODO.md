# TODO - C-to-Lean Project

## Current Status: Interpreter Working (100% on minimal/debug, 98% on full CI)

**Test Results (2026-01-18):**
- Minimal test suite: 76/76 (100% match with Cerberus)
- Debug test suite: 65/65 (100% match with Cerberus)
- Full CI suite: 98% match rate (753/762 successful comparisons)
- See logs/ directory for detailed test runs

## Recent Fixes (2026-01-18)

- **Global/errno allocation order**: Fixed errno to allocate AFTER globals (not before)
  - Bug: We allocated errno first, but Cerberus allocates globals first then errno
  - Impact: Char arrays were getting 8-byte aligned addresses instead of 1-byte
  - Fix: Move `allocateErrno` call to after `initGlobals` in `runMain`
  - Corresponds to: driver.lem:1541-1618 (globals), driver.lem:1837-1845 (errno)
  - This fixes pr43987 and other alignment-related test discrepancies

- **Float memory semantics**: sizeof(float) = 8 (Cerberus stores all floats as doubles)
  - Added IEEE 754 conversion functions for float32/float64
  - Comprehensive float test suite in tests/float/ (68 tests)

- **Cerberus wrapper optimization**: Use binary directly instead of dune exec
  - Much faster test runs (no dune rebuild check overhead)

## Bugs Discovered (Investigation Needed)

### ARCHITECTURAL: evalPexpr Returns Values, Not Pexprs
- **Cerberus behavior**: `step_eval_pexpr` returns `pexpr` (partially or fully evaluated)
- **Our behavior**: `evalPexpr` returns `Value` directly (always fully evaluated)
- **Impact**: We can't return partially evaluated expressions
- **Analysis**: For sequential execution, our design should be equivalent
- **Status**: Acceptable for sequential execution
- **Location**: `Semantics/Eval.lean:evalPexpr`

### Union Active Member Tracking (not implemented)
Reading a union member other than the last one written produces "Unspecified" in Cerberus.
- Our interpreter returns a concrete value (type punning reinterpretation)
- Cerberus tracks which union member was last written
- We would need to track "active member" metadata per union allocation
- **Impact:** Programs doing type punning via unions may show DIFF (not MISMATCH)

### Cerberus Non-determinism (pr34099, pr52286)
These tests show as MISMATCH in some runs but are caused by Cerberus non-determinism.
- Cerberus sometimes returns `Specified(0)`, sometimes errors with "calling an unknown procedure"
- Running the same test multiple times gives different results
- This is a known Cerberus issue documented in CLAUDE.md
- **Not a bug in our interpreter**

### CERB_INCONSISTENT: JSON Generation Fails When Exec Succeeds
When Cerberus `--exec` detects UB for constraint violations (incomplete types, alignment errors),
it reports `Undefined {...}`. But `--json_core_out` fails earlier in the pipeline for the same tests.
- ~30 tests affected (mostly `.undef` and `.error` tests)
- Not a bug in our interpreter, but limits our ability to compare UB detection
- **Ideal fix**: Make Cerberus JSON export path as permissive as exec path

### Not Implemented (causes FAIL in tests)
- `pure_memop` - 5 tests (cast_*_byte.exec)
- `builtin_printf` and other I/O builtins - ~80 tests
- `par` (parallel execution) - 4 tests
- `builtin_open/write` - 2 tests

## Expected Differences (not bugs)

### Unsequenced Race Detection (6 tests)
Tests 0300-0306 and 6.5-2.* detect `UB035_unsequenced_race` in Cerberus.
- We use `--sequentialise` which picks one evaluation order
- Cerberus's default mode explores multiple orderings and detects races
- These show as DIFF but are expected behavior

## Completed Phases

### Phase 1: Core AST in Lean ✓
- [x] Define all Core IR types (ObjectType, BaseType, Binop, Value, Pexpr, Expr, File)
- [x] Add pretty-printer for round-trip validation

### Phase 2: Core JSON Export & Parser ✓
- [x] Create `json_core.ml` in Cerberus for JSON serialization
- [x] Implement JSON parser in Lean (**100% success rate on 5500+ test files**)
- [x] Write pretty-printer in Lean matching Cerberus format (**99% match rate**)
- [x] Export pointer values as structured JSON (not strings)
- [x] Export memop, impl, extern, mem_value as structured JSON

### Phase 3: Memory Model ✓
- [x] Define `MemoryOps` type class with core operations
- [x] Implement `Concrete` memory model (allocation-ID provenance)
- [x] Add memory model unit tests (`make test-memory`)
- [x] Audit against Cerberus `impl_mem.ml` - see `docs/2026-01-01_MEMORY_AUDIT.md`

### Phase 4: Core Interpreter ✓
- [x] Small-step interpreter with explicit stack/continuations
- [x] `collectLabeledContinuations` - matches `core_aux.lem:1880-1931`
- [x] `collectAllLabeledContinuations` - matches `core_aux.lem:2379-2393`
- [x] `callProc` - matches `core_run.lem:30-70`
- [x] `step` function - matches `core_thread_step2`
- [x] Eaction (create, store, load, kill)
- [x] Ememop (pointer operations)
- [x] Eccall (C function calls through pointers)
- [x] Implementation-defined functions (`evalImplCall`)
- [x] Struct/union reconstruction in memory model

### Phase 5: Validation Framework ✓
- [x] Test runner for interpreter (`scripts/test_interp.sh`)
- [x] Cerberus comparison with exit code matching
- [x] UB detection matching (both interpreters detect same UB)
- [x] Minimal test suite (76 tests including UB tests)
- [x] Debug test suite for investigating specific issues
- [x] Float test suite (68 tests)

## Future Work

### Driver Layer & I/O Builtins (Major Feature)
To support `builtin_printf` and other I/O functions, we need:
- [ ] Add driver layer (like Cerberus's `driver.lem`)
- [ ] Implement `Formatted.printf` with format string parsing (see `formatted.lem`)
- [ ] Add filesystem state for stdout/stderr
- [ ] Handle `Step_fs` step type for I/O operations
- [ ] Support `builtin_vprintf`, `builtin_vsnprintf`, etc.

**Affected tests:** ~80 tests that use printf
**Cerberus files:** `driver.lem`, `formatted.lem`, `core_run.lem:1062-1098`

### Out of Scope
- Concurrent semantics (`Epar`, `Eunseq`)
- PNVI/CHERI memory models
- Full C standard library

## Test Commands

```bash
# Run minimal test suite (76 tests, 100% pass)
make test-interp

# Run debug tests
./scripts/test_interp.sh tests/debug --nolibc

# Run on full Cerberus test suite (expensive, 1-2 hours)
./scripts/test_interp.sh cerberus/tests --nolibc -v 2>&1 | tee logs/interp-full-$(date +%Y%m%d-%H%M%S).log

# Run csmith fuzz testing (100 random programs)
./scripts/fuzz_csmith.sh

# Run all quick tests
make test
```

## Documentation
- `docs/2026-01-01_MEMORY_AUDIT.md` - Memory model Cerberus correspondence
- `docs/2025-12-31_TESTING.md` - Test infrastructure guide
- `CLAUDE.md` - Project overview and conventions
