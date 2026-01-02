# Interpreter Status Report

**Date:** 2026-01-02
**Test Suite:** Cerberus CI tests (194 files)

## Summary

| Metric | Count | Rate |
|--------|-------|------|
| Cerberus Success | 194 | 100% |
| Lean Success | 82 | 42% |
| Lean Failed | 31 | 16% |
| Match (of both success) | 79 | **96%** |
| Mismatch | 3 | 4% |

**Key insight:** When both interpreters succeed, we match Cerberus 96% of the time.

## Failure Categories

### 1. `builtin_printf` Not Implemented (13 tests)

These tests use printf for output, which we haven't implemented.

```
0057-std_footnote_118
0067-band1
0068-bor1
0072-example03
0073-example03
0082-OK1
0083-array_initializers
0105-incr
0109-promotion_lt
0116-enum_constants
0126-duff_device
```

**Fix:** Implement `builtin_printf` in `evalImplCall` or as a stdlib proc.

### 2. UB Detection in `.undef` Tests (10 tests) - EXPECTED

These are tests that are *supposed* to trigger undefined behavior. Our interpreter correctly detects the UB and fails - this is the intended behavior.

| Test | UB Detected |
|------|-------------|
| 0028-division_by_zero.undef | UB045a_division_by_zero |
| 0029-modulo_by_zero.undef | UB045b_modulo_by_zero |
| 0074-fun_returns.undef | UB088_reached_end_of_function |
| 0086-literal_access.undef | write to const-qualified object |
| 0122-incr_overflow.undef | ub036_exceptionalCondition |
| 0123-decr_underflow.undef | ub036_exceptionalCondition |
| 0129-function-pointer-wrong-args.undef | UB038_number_of_args |
| 0295-global_const_int.undef | write to const-qualified object |
| 0296-global_const_array.undef | write to const-qualified object |
| 0333-shifts_non_representable.undef | UB052b_non_representable_left_shift |
| 0340-shl_promotion_to_signed.undef | UB052b_non_representable_left_shift |

**Status:** Working correctly - these should fail with UB.

### 3. Pattern Match Failures (5 tests)

These tests hit unhandled patterns in the interpreter.

```
0324-atomics
0328-indeterminate_block_declaration
0329-rvalue-temporary-lifetime.undef
0331-modifying-rvalue-temporary-lifetime.undef
0332-rvalue-temporary-lifetime-pointer-zap
```

**Investigation needed:** These likely involve:
- Atomic operations (0324)
- Indeterminate values / uninitialized memory (0328)
- Rvalue temporary lifetime semantics (0329, 0331, 0332)

### 4. Mismatches (3 tests)

These tests run successfully but produce different results than Cerberus.

| Test | Lean | Cerberus | Issue |
|------|------|----------|-------|
| 0056-unary_plus | -2147483648 | 0 | Unary plus on INT_MIN? |
| 0298-atomic_memberofptr.undef | UB043 | success | False positive UB detection |
| 0335-non_decimal_unsigned_long_int_constants | 15 | 10 | Unsigned long constant parsing |

**Priority:** These need investigation as they indicate semantic bugs.

## Test Breakdown by Category

### Passing Tests (82)
- Basic arithmetic, control flow, functions
- Structs, unions, arrays
- Pointers, pointer arithmetic
- Type conversions
- Global variables
- Switch statements, goto
- Compound literals

### Known Limitations
- No `printf` / stdio support
- No atomic operations beyond basic support
- No VLA (variable-length arrays)
- No complex numbers
- No `_Generic` selection

## Recommendations

### High Priority
1. Investigate the 3 mismatches - these are semantic bugs
2. Fix pattern match failures (5 tests)

### Medium Priority
3. Implement basic `builtin_printf` for test compatibility

### Low Priority
4. The `.undef` UB detection tests are working correctly - no action needed

## Test Commands

```bash
# Run on minimal test suite (67 tests, 100% pass)
./scripts/test_interp.sh tests/minimal

# Run on full CI suite (194 tests)
./scripts/test_interp.sh cerberus/tests/ci

# Run on specific test
./scripts/cerberus --json_core_out=/tmp/test.json path/to/test.c
./lean/.lake/build/bin/ctolean_interp /tmp/test.json
```
