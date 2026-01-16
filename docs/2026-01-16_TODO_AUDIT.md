# TODO and Deviation Audit

**Date:** 2026-01-16
**Scope:** All TODOs, panics, throwNotImpl, and documented deviations in lean/
**Status:** Based on current codebase state; some docs in docs/ are outdated

## Summary

| Category | Count | Action |
|----------|-------|--------|
| Critical (will crash) | 4 | Must fix or document as limitation |
| High Priority (throwNotImpl) | 12 | Fix if affects real programs |
| Medium Priority (documented deviations) | 8 | Review if causing test failures |
| Low Priority (acceptable tradeoffs) | 6 | Document and accept |
| Parser/PP only | 1 | Deferred (needs Cerberus-side fix) |

---

## Critical Priority: Panics That Will Crash

These `panic!` calls will crash the interpreter if hit. Most are rare edge cases but should be addressed.

### C1. Float NaN/Infinity Encoding
**Location:** `Memory/Concrete.lean:240-243`
```lean
| .nan => panic! "memValueToBytes: NaN float encoding not implemented"
| .posInf => panic! "memValueToBytes: +Inf float encoding not implemented"
| .negInf => panic! "memValueToBytes: -Inf float encoding not implemented"
```
**Impact:** Any C program storing NaN or Infinity to memory will crash.
**Resolution:** Implement IEEE 754 encoding for special float values.
**Difficulty:** Medium - need to implement proper bit patterns for NaN (0x7FC00000 for float), +Inf (0x7F800000), -Inf (0xFF800000).
**Priority:** HIGH - affects floating point programs

### C2. Symbolic/Device Provenance
**Location:** `Memory/Concrete.lean:45-47, 767-770`
```lean
| .symbolic iota => panic! s!"toAllocId: provenance is symbolic (iota={iota})"
| .device => panic! "toAllocId: provenance is device"
```
**Impact:** Programs using PNVI-ae-udi or device memory will crash.
**Resolution:** For now, these are fundamental limitations of the concrete memory model.
**Difficulty:** HIGH - requires implementing PNVI or device memory models.
**Priority:** LOW - out of scope for current project (concrete memory model only)
**Action:** Document as intentional limitation; remove panic and return proper error.

### C3. Layout Panics for Missing Tags
**Location:** `Memory/Layout.lean:267-273, 298-304, 387-406`
```lean
| none => panic! s!"sizeof: undefined struct tag {tag.name}"
| none => panic! s!"alignof: undefined union tag {tag.name}"
| none => panic! s!"memberOffset: member {member.name} not found in struct {tag.name}"
```
**Impact:** Programs referencing undefined struct/union tags will crash.
**Resolution:** These should be impossible if the parser succeeded - they indicate a bug.
**Difficulty:** Easy - convert to proper errors that propagate.
**Priority:** MEDIUM - defensive; should never happen but shouldn't panic if it does.

### C4. Memory Allocation Panics
**Location:** `Memory/Concrete.lean:143, 181, 619, 948-949`
```lean
| none => panic! s!"readBytes: address {addr + i} not in bytemap"
| none => panic! "bytesToInt: unexpected none value"
| none => panic! s!"storeImpl: allocation {allocId} not found when trying to lock"
```
**Impact:** Memory corruption or internal bugs will cause crash instead of error.
**Resolution:** Convert to proper memory errors.
**Difficulty:** Easy - use existing `MemError` types.
**Priority:** MEDIUM - defensive programming

---

## High Priority: Not Implemented (throwNotImpl)

These throw `InterpError.notImplemented` which is handled gracefully but causes test failures.

### H1. Union Punning (Type Reinterpretation)
**Location:** `Semantics/Eval.lean:993-995`
```lean
InterpM.throwNotImpl "TODO: evaluation of PEmemberof => union punning"
```
**Impact:** Reading a union member that differs from the last-written member fails.
**Cerberus Behavior:** Returns `Unspecified` value (not concrete reinterpretation).
**Resolution:**
- Option A: Track active union member per allocation (like Cerberus) → return Unspecified
- Option B: Implement actual type punning (reinterpret bytes) → may differ from Cerberus
**Difficulty:** Medium (Option A requires metadata), Low (Option B simpler but diverges)
**Priority:** HIGH - affects union-heavy code, causes DIFF results in csmith tests
**Recommendation:** Implement Option A to match Cerberus exactly

### H2. Atomic Operations (Fence, RMW, CompareExchange)
**Location:** `Semantics/Step.lean:516-524`
```lean
| .fence _ => throw (.notImplemented "fence")
| .rmw _ _ _ _ _ _ => throw (.notImplemented "rmw")
| .compare_exchange_strong _ _ _ _ _ _ => throw (.notImplemented "compare_exchange_strong")
| .compare_exchange_weak _ _ _ _ _ _ => throw (.notImplemented "compare_exchange_weak")
```
**Impact:** C11 atomic operations will fail.
**Cerberus Behavior:** Full atomic memory model.
**Resolution:** Implement basic sequentially-consistent atomics.
**Difficulty:** High - requires understanding C11 memory model.
**Priority:** MEDIUM - many programs don't use atomics; 5 CI tests affected
**Recommendation:** Defer unless blocking important tests

### H3. Pure Memops and Constrained Expressions
**Location:** `Semantics/Eval.lean:1032-1033, 1104-1106`
```lean
| .isScalar _e => InterpM.throwNotImpl "is_scalar"
| .isInteger _e => InterpM.throwNotImpl "is_integer"
| .bmcAssume _e => InterpM.throwNotImpl "bmc_assume"
| .pureMemop _op _args => InterpM.throwNotImpl "pure_memop"
| .constrained _cs => InterpM.throwNotImpl "constrained"
```
**Impact:** Model checking extensions and some type queries fail.
**Cerberus Usage:** Used for bounded model checking, not standard execution.
**Note:** `is_signed` and `is_unsigned` ARE implemented (Eval.lean:1041-1090).
**Resolution:**
- `is_scalar`/`is_integer`: Implement type checks (easy)
- `bmc_assume`/`constrained`: Out of scope (model checking)
- `pure_memop`: Evaluate based on actual memop
**Difficulty:** Easy (type checks), N/A (BMC features)
**Priority:** LOW - not used in standard execution mode
**Recommendation:** Implement type checks; document BMC features as unsupported

### H4. Unknown Builtin Functions
**Location:** `Semantics/Step.lean:334-336`
```lean
| .other name => s!"builtin function '{name}' not implemented (requires driver layer)"
throw (.notImplemented msg)
```
**Impact:** Programs using non-standard builtins fail.
**Cerberus Behavior:** Driver layer handles many builtins.
**Resolution:** Implement driver layer for common builtins (printf, etc.)
**Difficulty:** High - requires I/O layer, format string parsing.
**Priority:** LOW for now - 14 tests need printf; main interpreter works without it
**Recommendation:** Document as future work; focus on core semantics

### H5. CHERI Intrinsics
**Location:** `Semantics/Step.lean:795`
```lean
| .cheriIntrinsic name, _ => throw (.notImplemented s!"CHERI intrinsic: {name}")
```
**Impact:** CHERI capability programs fail.
**Resolution:** Out of scope - requires CHERI memory model.
**Difficulty:** Very High
**Priority:** OUT OF SCOPE
**Recommendation:** Keep as-is; document limitation

### H6. Parallel Execution (par, wait)
**Location:** `Semantics/Step.lean:804, 807`
```lean
throw (.notImplemented "par (parallel execution)")
throw (.notImplemented "wait")
```
**Impact:** Concurrent programs fail.
**Resolution:** Out of scope - we sequentialize execution intentionally.
**Difficulty:** Very High - requires concurrent memory model
**Priority:** OUT OF SCOPE
**Recommendation:** Keep as-is; documented limitation

### H7. Implementation Constants
**Location:** `Semantics/Eval.lean:797`
```lean
InterpM.throwNotImpl s!"implementation constant: {name}"
```
**Impact:** Unknown impl constants fail.
**Resolution:** Add constants as needed when encountered in tests.
**Difficulty:** Easy per constant
**Priority:** MEDIUM - add as needed
**Recommendation:** Fix when encountered; most common ones already implemented

### H8. Pure Function Calls (Not Found)
**Location:** `Semantics/Eval.lean:872-878`
```lean
InterpM.throwNotImpl s!"pure function call {s.name}: found proc, not fun"
InterpM.throwNotImpl s!"pure function call {s.name}: not found in stdlib"
```
**Impact:** Calling proc as fun, or missing stdlib function.
**Resolution:** Parser/type issue - should be caught earlier.
**Difficulty:** Easy - improve error messages
**Priority:** LOW - indicates malformed input

---

## Medium Priority: Documented Deviations

These are intentional simplifications that may cause test differences.

### M1. evalPexpr Returns Values, Not Pexprs
**Location:** `Semantics/Eval.lean` (architectural)
**Documented in:** `TODO.md:41-58`
**Cerberus:** `step_eval_pexpr` returns partially evaluated `pexpr`
**Our Behavior:** `evalPexpr` returns fully evaluated `Value`
**Impact:** Can't return partially evaluated expressions.
**Analysis:** For sequential execution without `PEconstrained`, this is equivalent.
**Priority:** LOW - acceptable for sequential execution
**Recommendation:** Keep as-is; document that concurrent/constrained features require refactor

### M2. No Trap Representation Checking
**Location:** `Memory/Concrete.lean:538-541`
```lean
Deviations:
- No trap representation checking for _Bool (TODO)
```
**Cerberus:** Checks `_Bool` loads return only 0 or 1
**Impact:** Loading non-0/1 into `_Bool` doesn't trigger UB.
**Resolution:** Add check in `loadImpl` for `_Bool` type.
**Difficulty:** Easy
**Priority:** MEDIUM - may affect some tests
**Recommendation:** Implement for correctness

### M3. Simplified Provenance Types
**Location:** `Core/Value.lean:20-22`
```lean
Deviations: Simplified from impl_mem.ml which has more variants
```
**Impact:** Only concrete provenance fully supported.
**Resolution:** Documented limitation - other provenances not needed for concrete model.
**Priority:** LOW - intentional simplification
**Recommendation:** Keep as-is

### M4. No Complex Floating Types
**Location:** `Core/Ctype.lean:70`
```lean
Deviations: Complex types not yet supported (commented out in Cerberus)
```
**Impact:** `_Complex float/double` not supported.
**Resolution:** Add when needed.
**Difficulty:** Medium
**Priority:** LOW - rare in practice
**Recommendation:** Keep as-is; add if tests need it

### M5. No Linux-Specific Actions
**Location:** `Core/Expr.lean:118`
```lean
Deviations: Linux-specific actions (LinuxFence, LinuxLoad, etc.) not included
```
**Impact:** Linux kernel code not supported.
**Resolution:** Out of scope.
**Priority:** OUT OF SCOPE
**Recommendation:** Keep as-is

### M6. Address Allocation Difference
**Location:** `TODO.md:67-73`
**Documented in:** `docs/2026-01-06_ADDRESS_DIFFERENCE_INVESTIGATION.md`
**Issue:** Our addresses differ from Cerberus by ~4608 bytes.
**Impact:** Raw address values differ; semantics identical.
**Resolution:** Acceptable - doesn't affect correctness.
**Priority:** LOW
**Recommendation:** Keep as-is; document

### M7. State Structure Simplifications
**Location:** `Semantics/State.lean:81, 207-208`
```lean
Deviations: We don't store parameter types (core_base_type)...
- We don't track exec_loc (debugging info only)
- We don't track current_loc (debugging info only)
```
**Impact:** Debugging info not available.
**Resolution:** Not needed for execution.
**Priority:** LOW
**Recommendation:** Keep as-is

### M8. Value Returns vs Object Type
**Location:** `Semantics/Eval.lean:353`
```lean
Deviations: Returns just the value (not the object type)
```
**Impact:** Object type not tracked through evaluation.
**Resolution:** Add if needed for type checking.
**Priority:** LOW
**Recommendation:** Keep as-is unless tests fail

---

## Low Priority: Acceptable Tradeoffs

### L1. Function Info Lookup by Name (Workaround)
**Location:** `Core/File.lean:320-325`
```lean
Note: This is a workaround because pointer values in JSON are exported as strings,
losing the symbol ID. We look up by name only...
```
**Impact:** Relies on unique function names within translation unit.
**Resolution:** Would need Cerberus JSON export changes.
**Difficulty:** Requires Cerberus changes
**Priority:** LOW - works in practice
**Recommendation:** Keep workaround; document limitation

### L2. UndefinedBehavior Catch-All
**Location:** `Core/Undefined.lean:5`
```lean
Deviations: Not all 200+ variants are included; uses `other` catch-all for rare variants
```
**Impact:** Some UB codes shown as `other("...")` instead of specific code.
**Resolution:** Add variants as encountered.
**Difficulty:** Easy but tedious
**Priority:** LOW - doesn't affect detection
**Recommendation:** Add variants as needed

### L3. File Attributes Not Used
**Location:** `Core/File.lean:248`
```lean
Deviations: attributes field not used (always empty in practice)
```
**Impact:** None - field always empty.
**Priority:** NONE
**Recommendation:** Keep as-is

### L4. PP Qualifier Handling (Matches Cerberus TODOs)
**Location:** `PrettyPrint.lean:135, 144`
```lean
-- pp_core_ctype.ml ignores qualifiers on function params (has TODO comment)
-- pp_core_ctype.ml ignores qualifiers on pointers (has TODO comment)
```
**Impact:** Qualifiers not printed in some contexts.
**Resolution:** Matches Cerberus behavior (Cerberus also has TODOs).
**Priority:** NONE - intentionally matches Cerberus
**Recommendation:** Keep as-is

### L5. Dummy UB Variant
**Location:** `Core/Undefined.lean:42-43`
```lean
-- Dummy/placeholder (undefined.lem:22)
| dummy (msg : String)
```
**Impact:** Placeholder for unknown UB.
**Resolution:** Matches Cerberus.
**Priority:** NONE
**Recommendation:** Keep as-is

### L6. Recursion Depth Limits
**Location:** `Semantics/Eval.lean:761, 1113, 1129, 1143`
```lean
| 0 => throw (.notImplemented "evalPexpr: recursion depth exceeded")
```
**Impact:** Very deep expressions fail.
**Resolution:** Increase depth if needed.
**Priority:** LOW - 1000 depth sufficient for normal programs
**Recommendation:** Keep as-is; increase if tests fail

---

## Parser/Pretty-Printer Only

### P1. NULL Type Parsing for Complex Types
**Location:** Documented in `docs/2025-12-26_PP_DISCREPANCIES.md` Category 22
**Impact:** 7 files show `NULL(void*)` instead of actual type
**Issue:** `parseCtypeStr` doesn't handle ptrdiff_t, function types, enum types, array types
**Resolution:** Requires either:
- Extend `parseCtypeStr` parser (complex)
- Cerberus-side fix to emit structured JSON for NULL types (preferred)
**Difficulty:** Medium (parser) or requires Cerberus changes
**Priority:** LOW - only affects pretty-printer output, not execution
**Recommendation:** Defer; request Cerberus-side structured JSON export

---

## Resolution Plan

### Immediate (before next release)
1. **C3, C4:** Convert panics to proper errors (defensive programming)
2. **H7:** Add implementation constants as tests encounter them

### Short Term (next sprint)
3. **C1:** Implement IEEE 754 NaN/Infinity encoding
4. **H1:** Implement union active member tracking (match Cerberus Unspecified behavior)
5. **M2:** Add `_Bool` trap representation checking

### Medium Term
6. **H2:** Consider basic atomic support if many tests need it
7. **H3:** Implement `is_scalar`/`is_integer` type checks

### Documented Limitations (no action)
- **C2:** Symbolic/device provenance (out of scope)
- **H4:** printf/driver layer (future work)
- **H5, H6:** CHERI, parallel execution (out of scope)
- **M1:** Returns values not pexprs (acceptable for sequential)
- **M3-M8:** Various simplifications (acceptable)
- **L1-L6:** Workarounds and catch-alls (working fine)
- **P1:** NULL type parsing (deferred to Cerberus)

---

## Test Impact Summary

| Issue | Tests Affected | Fix Impact |
|-------|----------------|------------|
| Union punning (H1) | csmith tests with unions | DIFF → MATCH |
| Atomics (H2) | 5 CI tests (0324, 0328-0332) | pattern match → pass |
| NaN/Inf (C1) | float edge cases | crash → pass |
| `_Bool` traps (M2) | unknown | may fix some UB detection |
| printf (H4) | 14 tests | would need driver layer |

**Current status (2026-01-06):** 91% match on CI tests, 100% on minimal tests (74/74)
**Target after fixes:** 95%+ on CI tests
