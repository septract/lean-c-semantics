# TODO - C-to-Lean Project

## Current Status: Interpreter Working (100% on minimal tests, 91% on CI)

**Test Results (2026-01-06):**
- Minimal test suite: 74/74 (100% match with Cerberus)
- Cerberus CI suite: 91% match rate on successful tests
- See `docs/INTERPRETER_STATUS.md` and `docs/FULL_TEST_RESULTS_2026-01-02.md` for detailed breakdown

## Recent Fixes (2026-01-06)

- **exit()/abort() builtins**: Implemented early termination support
- **Negative pointer arithmetic**: Fixed `arrayShiftPtrval` to handle negative offsets
  - Bug: `n.val.toNat` converted -1 to 0, breaking `p--` and `p - 1`
  - Fix: Use Int arithmetic throughout, convert to Nat only at end

## Bugs Discovered (Investigation Needed)

### ARCHITECTURAL: evalPexpr Returns Values, Not Pexprs
- **Cerberus behavior**: `step_eval_pexpr` returns `pexpr` (partially or fully evaluated)
  - `valueFromPexpr` extracts value only if pexpr is `PEval cval`, else returns `Nothing`
  - Unevaluated subexpressions are returned as-is (e.g., `PEmemberof tag member pe'`)
- **Our behavior**: `evalPexpr` returns `Value` directly (always fully evaluated)
- **Impact**: We can't return partially evaluated expressions
- **Status**: This may be acceptable for sequential execution but needs audit
- **Location**: `Semantics/Eval.lean:evalPexpr`

### Struct Reconstruction Not Implemented - FIXED 2026-01-06
- ~~`reconstructValue` in `Memory/Concrete.lean:423` panics for structs~~
- Fixed: Implemented struct/union reconstruction matching Cerberus impl_mem.ml

### False Positive UB Issues (from full test suite)
See `docs/FULL_TEST_RESULTS_2026-01-02.md` for test names.

- **UB036_exceptional_condition** (5 tests): Need investigation - may be struct reconstruction issue
- **UB_CERB002a_out_of_bound_load** (2 tests): 20060412-1, 20080604-1
- **UB025_misaligned_pointer_conversion** (1 test): pr36339
- **UB_CERB004_unspecified__equality** (1 test): pr52129
- **UB_internal_type_error** (1 test): 941014-1

### False Negative UB
- **function_vs_var**: Missing UB024_out_of_range_pointer_to_integer_conversion

### Other Semantic Differences
- **0046-jump_inside_lifetime**: Lean returns 0, Cerberus returns UNSPECIFIED
- **treiber**: Lean returns UB_CERB004_unspecified__equality_ptr_vs_NULL, Cerberus returns 0

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

**Low Priority:**
- [ ] Implement `builtin_printf` for test compatibility (13 tests)

## Future Work

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
