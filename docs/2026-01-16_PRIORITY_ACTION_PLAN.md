# Priority Action Plan

**Date:** 2026-01-16
**Based on:** `docs/2026-01-16_TODO_AUDIT.md`
**Principle:** Always match Cerberus exactly; drop audit comments after fixing

**Focus:** Issues that cause wrong results on CORRECT programs. Panics on malformed input are acceptable.

---

## Tier 1: Semantic Differences (Wrong Results)

These cause us to produce different results than Cerberus on valid programs.

### 1a. `_Bool` Trap Representation (M2) - DONE
**Location:** `Memory/Concrete.lean:113-133, 591-594`
**Fix:** Added `isBoolType` and `isBoolTrapRepresentation` helpers, check in `loadImpl`
**Test:** `tests/minimal/077-bool-trap.undef.c`
**Status:** COMPLETED 2026-01-16

### 1b. IEEE 754 NaN/Infinity Encoding (C1) - DONE
**Location:** `Parser.lean:745-747, 858-860`, `Memory/Concrete.lean:254-284`
**Fix:** Parse "NaN"/"Infinity" as Lean Floats (matching Cerberus FVconcrete with OCaml floats)
**Test:** `tests/minimal/078-float-special.c`, `tests/debug/float-01-infinity-literal.c`
**Status:** COMPLETED 2026-01-16

---

## Tier 2: Add Features As Needed

### 2a. Implementation Constants (H7)
**Location:** `Semantics/Eval.lean:797`
**Action:** Add constants as tests encounter them. Most common ones already implemented.

### 2b. Type Query Expressions (H3 partial)
**Location:** `Semantics/Eval.lean:1032-1033`
**Action:** Implement `is_scalar` and `is_integer` type checks if tests need them
**Skip:** `bmc_assume`, `pure_memop`, `constrained` (BMC features, out of scope)

### 2c. Atomics (H2)
**Location:** `Semantics/Step.lean:517-524`
**Affected tests:** 5 CI tests
**Action:** Implement if many tests need it; defer otherwise

---

## Not Bugs (Matches Cerberus)

### Union Punning (H1)
**Location:** `Semantics/Eval.lean:993-995`
**Cerberus:** `core_eval.lem:956-957` - `error "TODO: evaluation of PEmemberof => union puning"`
**Our behavior:** Same - `throwNotImpl`
**Status:** This is NOT a bug - we match Cerberus exactly. Both have this limitation.

---

## Out of Scope (Intentional Limitations)

| Feature | Reason |
|---------|--------|
| Symbolic/Device provenance (C2) | Concrete memory model only |
| printf/driver layer (H4) | Requires I/O layer |
| CHERI intrinsics (H5) | Requires CHERI memory model |
| Parallel execution (H6) | Sequential execution only |
| Complex floating types (M4) | Rare; add if needed |
| Linux-specific actions (M5) | Kernel code out of scope |

---

## Acceptable Defensive Panics

These panic on malformed/impossible input. Crashing is fine here:
- **C3:** Undefined struct/union tags (should never happen if Cerberus parsed it)
- **C4:** Missing allocations/bytes (internal invariant violation)

---

## Parser/PP (Resolved)

### P1. NULL Type Parsing - RESOLVED
**Issue:** 7 files showed `NULL(void*)` instead of actual type
**Root cause:** Was NOT a Cerberus issue. The `parseCtypeStr` function flagged in audit was DEAD CODE.
**Actual state:** Cerberus already exports structured JSON for NULL types via `json_pointer_value`.
  Our parser already uses `parseCtype` on this structured JSON (Parser.lean:761-764, 874-877).
**Action:** Removed dead `parseCtypeStr` function from Parser.lean.
**Status:** RESOLVED 2026-01-16

---

## Recommended Order

1. ~~**1a** (`_Bool` trap)~~ - DONE
2. ~~**1b** (NaN/Inf encoding)~~ - DONE
3. **2a-c** - As tests encounter them

---

## Verification

After each fix:
- [ ] `./scripts/test_interp.sh tests/minimal/` - must stay at 100%
- [ ] `./scripts/test_interp.sh tests/debug/` - check regressions
- [ ] Remove/update audit comment in code
