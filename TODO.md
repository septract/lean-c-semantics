# TODO - C-to-Lean Project

## Current Status: Interpreter Working (100% on minimal tests, 90% on CI)

**Test Results (2026-01-02):**
- Minimal test suite: 72/72 (100% match with Cerberus)
- Cerberus CI suite: 90% match rate on successful tests
- See `docs/INTERPRETER_STATUS.md` for detailed breakdown

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

**Fixed (2026-01-02):**
- [x] 0056-unary_plus: Fixed by correcting test script to compare return values
- [x] 0335-non_decimal_unsigned_long_int_constants: Fixed floored remainder (`rem_f`) bug

**Semantic Mismatches (9 tests):**
- [ ] 0297-atomic_memberof: Need to detect atomic struct/union member access UB
- [ ] 0300-0306 unseq_race tests: Out of scope (we sequentialize execution)

**Medium Priority (5 pattern match failures):**
- [ ] 0324-atomics
- [ ] 0328-indeterminate_block_declaration
- [ ] 0329, 0331, 0332 - rvalue temporary lifetime tests

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
