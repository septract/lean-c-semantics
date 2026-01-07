# TODO - C-to-Lean Project

## Current Status: Interpreter Working (100% on minimal tests, 91% on CI)

**Test Results (2026-01-06):**
- Minimal test suite: 74/74 (100% match with Cerberus)
- Cerberus CI suite: 91% match rate on successful tests
- See `docs/INTERPRETER_STATUS.md` and `docs/FULL_TEST_RESULTS_2026-01-02.md` for detailed breakdown

## Recent Fixes (2026-01-06)

- **Floating point binary operations**: Added `evalFloatOp` for +, -, *, /, comparisons
  - Corresponds to: core_eval.lem:443-452 and defacto_memory.lem:1097-1110
- **Unspecified memory initialization**: Fixed `allocateImpl` to write unspecified bytes
  - Bug: Was zero-initializing instead of writing `value := none` bytes
  - Corresponds to: impl_mem.ml:1317-1322
- **Unspecified pattern matching**: Fixed to match `Unspecified [inner]` with 1 subpattern
  - Corresponds to: core_aux.lem:1121-1122
- **exit()/abort() builtins**: Implemented early termination support
- **Negative pointer arithmetic**: Fixed `arrayShiftPtrval` to handle negative offsets
  - Bug: `n.val.toNat` converted -1 to 0, breaking `p--` and `p - 1`
  - Fix: Use Int arithmetic throughout, convert to Nat only at end
- **941014-1 function pointer to int**: Fixed `intfromPtrImpl` to convert function symbol ID
  - Bug: Was throwing error for function pointers instead of converting
  - Corresponds to: impl_mem.ml:2249-2272
- **pr55875 false positive UB043**: Fixed `validForDerefImpl` to match Cerberus semantics
  - Bug: Was checking bounds in validForDeref, but Cerberus only checks alignment there
  - Bounds checking happens in load/store, not in validForDeref
  - Corresponds to: impl_mem.ml:2086-2123
- **b.c pointer equality**: Fixed `eqPtrvalImpl` to use provenance-aware comparison
  - Corresponds to: defacto_memory.lem:1430-1479
- **function_vs_var UB024**: Fixed pointer-to-integer range checking
  - Bug: Was not checking if address fits in target integer type
  - Fix: Changed memory allocation to use high addresses (downward from 0xFFFFFFFFFFFF)
  - Added `integerTypeMax`/`integerTypeMin` helpers for range checking
  - `intfromPtrImpl` now throws `MerrIntFromPtr` when address out of range
  - Corresponds to: impl_mem.ml:2439-2461, impl_mem.ml:2367-2437

## Bugs Discovered (Investigation Needed)

### ARCHITECTURAL: evalPexpr Returns Values, Not Pexprs
- **Cerberus behavior**: `step_eval_pexpr` returns `pexpr` (partially or fully evaluated)
  - `valueFromPexpr` extracts value only if pexpr is `PEval cval`, else returns `Nothing`
  - Unevaluated subexpressions are returned as-is (e.g., `PEmemberof tag member pe'`)
  - Partial evaluation happens for: concurrent model, PEconstrained, memory wait states
- **Our behavior**: `evalPexpr` returns `Value` directly (always fully evaluated)
- **Impact**: We can't return partially evaluated expressions
- **Analysis**:
  - For sequential execution without `PEconstrained`, sub-expressions either:
    1. Evaluate to a value (normal case)
    2. Fail with an error (UB, type error, etc.)
  - The "return partial expression" path in Cerberus is mainly for:
    - Concurrent execution (we don't support)
    - Constrained expressions (we don't support)
    - Memory operations that need to wait (sequential model completes immediately)
  - **Conclusion**: For sequential execution, our design should be equivalent
- **Status**: Acceptable for sequential execution, but worth auditing if any tests fail mysteriously
- **Location**: `Semantics/Eval.lean:evalPexpr`

### Struct Reconstruction Not Implemented - FIXED 2026-01-06
- ~~`reconstructValue` in `Memory/Concrete.lean:423` panics for structs~~
- Fixed: Implemented struct/union reconstruction matching Cerberus impl_mem.ml

### Remaining UB Issues
All previously reported UB detection issues (false positive and false negative) have been fixed as of 2026-01-06.

### Address Allocation Difference (needs investigation)
Our memory addresses differ from Cerberus by ~4608 bytes for the first allocation.
- Both use same initial address (0xFFFFFFFFFFFF) and same algorithm
- Our calculation matches the expected math; Cerberus is 4608 bytes lower
- Hypothesis: Cerberus allocates runtime structures before main()
- See `docs/ADDRESS_DIFFERENCE_INVESTIGATION.md` for details
- **Impact:** UB detection works correctly; only raw address values differ

### Other Semantic Differences (1 test)
- **treiber**: Uses `builtin_printf` (see Future Work below)

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
- [x] Audit against Cerberus `impl_mem.ml` - see `docs/MEMORY_AUDIT.md`

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

### Phase 5: Validation Framework ✓
- [x] Test runner for interpreter (`scripts/test_interp.sh`)
- [x] Cerberus comparison with exit code matching
- [x] UB detection matching (both interpreters detect same UB)
- [x] Minimal test suite (72 tests including 5 UB tests)

## Current Work

### Remaining Interpreter Issues (from CI tests)
See `docs/INTERPRETER_STATUS.md` for details.

**Fixed (2026-01-02 and 2026-01-06):**
- [x] 0056-unary_plus: Fixed by correcting test script to compare return values
- [x] 0335-non_decimal_unsigned_long_int_constants: Fixed floored remainder (`rem_f`) bug
- [x] 0297-atomic_memberof: Added atomic member access UB detection (UB042)
- [x] 0298-atomic_memberofptr: Fixed by same atomic member access check
- [x] exit()/abort() builtins: Implemented for early termination
- [x] Negative pointer arithmetic: Fixed `arrayShiftPtrval` Int handling

**Semantic Mismatches (7 tests):**
- [ ] 0300-0306 unseq_race tests: Out of scope (we sequentialize execution)

**Medium Priority (5 pattern match failures):**
- [ ] 0324-atomics
- [ ] 0328-indeterminate_block_declaration
- [ ] 0329, 0331, 0332 - rvalue temporary lifetime tests

**High Priority (struct support):**
- [ ] Implement struct reconstruction in `Memory/Concrete.lean:reconstructValue`

## Future Work

### Driver Layer & I/O Builtins (Major Feature)
To support `builtin_printf` and other I/O functions, we need:
- [ ] Add driver layer (like Cerberus's `driver.lem`)
- [ ] Implement `Formatted.printf` with format string parsing (see `formatted.lem`)
- [ ] Add filesystem state for stdout/stderr
- [ ] Handle `Step_fs` step type for I/O operations
- [ ] Support `builtin_vprintf`, `builtin_vsnprintf`, etc.

**Affected tests:** treiber + 13 other tests that use printf
**Cerberus files:** `driver.lem`, `formatted.lem`, `core_run.lem:1062-1098`

### Phase 6: UB-Freeness Theorems
- [ ] Define `UBFree` predicate
- [ ] Implement theorem statement generator
- [ ] Create example theorems for simple programs

### Out of Scope
- Concurrent semantics (`Epar`, `Eunseq`)
- PNVI/CHERI memory models
- Variadic functions
- Full C standard library

## Test Commands

```bash
# Run minimal test suite (72 tests, 100% pass)
make test-interp
# or: ./scripts/test_interp.sh tests/minimal

# Run on Cerberus CI suite (~200 tests)
./scripts/test_interp.sh cerberus/tests/ci

# Run all quick tests
make test
```

## Documentation
- `docs/INTERPRETER_STATUS.md` - Current test results and issues
- `docs/MEMORY_AUDIT.md` - Memory model Cerberus correspondence
- `docs/TESTING.md` - Test infrastructure guide
