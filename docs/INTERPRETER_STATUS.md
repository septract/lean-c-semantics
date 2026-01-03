# Interpreter Status Report

**Date:** 2026-01-02
**Test Suite:** Cerberus CI tests (194 files)

## Summary

| Metric | Count | Rate |
|--------|-------|------|
| Cerberus Success | 129 | 66% |
| Cerberus Failed | 65 | 34% |
| Lean Success (of Cerberus success) | 95 | 74% |
| Lean Failed | 18 | 14% |
| Match (of both success) | 86 | **90%** |
| UB Match | 12 | - |
| UB Code Diff | 1 | - |
| Mismatch | 9 | 10% |

**Key insight:** When both interpreters succeed, we match Cerberus 90% of the time.

## Test Results by Category

### Passing Tests (86 matches)
- Basic arithmetic, control flow, functions
- Structs, unions, arrays
- Pointers, pointer arithmetic
- Type conversions (including signed/unsigned)
- Global variables
- Switch statements, goto
- Compound literals
- Integer constant handling

### UB Match (12 tests)
Both interpreters detect the same undefined behavior:
- Division/modulo by zero
- Signed overflow
- Null pointer dereference
- Out-of-bounds access
- Non-representable shifts

### UB Code Diff (1 test)
Both detect UB but report different codes (e.g., CERB002a vs UB043 for out-of-bounds).
This is acceptable - the important thing is both detect UB.

### Mismatches (9 tests)

**Unsequenced Race Detection (7 tests):**
```
0300-unseq_race_ko01.undef through 0306-unseq_race_ko07.undef
```
- **Expected:** We sequentialize execution, so don't detect unsequenced race UB
- **Status:** Out of scope - concurrent semantics not implemented

**Atomic Member Access (1 test):**
```
0297-atomic_memberof.undef
```
- **Issue:** We don't detect atomic struct/union member access UB
- **Fix:** Implement UB042 detection in member access

**Atomic Member Pointer (1 test) - FIXED:**
```
0298-atomic_memberofptr.undef
```
- Previously reported as false positive, now passing

### Pattern Match Failures (5 tests)

These tests hit unhandled patterns in the interpreter:

```
0324-atomics
0328-indeterminate_block_declaration
0329-rvalue-temporary-lifetime.undef
0331-modifying-rvalue-temporary-lifetime.undef
0332-rvalue-temporary-lifetime-pointer-zap
```

**Investigation needed:**
- Atomic operations (0324)
- Indeterminate values / uninitialized memory (0328)
- Rvalue temporary lifetime semantics (0329, 0331, 0332)

### Cerberus Failures (65 tests)
Tests where Cerberus itself fails (syntax errors, unsupported features, etc.)
These are skipped in our comparison.

## Recent Fixes

### 2026-01-02: Floored Remainder Bug
**Issue:** `rem_f` (floored remainder) was incorrectly implemented, causing unsigned integer conversion to fail.

**Example:** `-1 rem_f 2^64` returned `-1` instead of `2^64 - 1`.

**Fix:** Corrected formula in `evalIntOp`:
```lean
let tmod := n1 % n2  -- truncated remainder
let result := if tmod != 0 && (tmod < 0) != (n2 < 0) then tmod + n2 else tmod
```

**Tests fixed:** 0335-non_decimal_unsigned_long_int_constants, conv-03, conv-09

## Known Limitations

- No `printf` / stdio support (13 tests need this)
- No atomic operations beyond basic support
- No unsequenced race detection (we sequentialize)
- No VLA (variable-length arrays)
- No complex numbers
- No `_Generic` selection

## Test Commands

```bash
# Run on minimal test suite (72 tests, 100% match)
./scripts/test_interp.sh tests/minimal

# Run on full CI suite (194 tests)
./scripts/test_interp.sh cerberus/tests/ci

# Run on specific test
./scripts/cerberus --json_core_out=/tmp/test.json path/to/test.c
./lean/.lake/build/bin/ctolean_interp /tmp/test.json
```
