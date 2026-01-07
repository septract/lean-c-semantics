# Full Test Suite Results

**Date:** 2026-01-02
**Test Suite:** cerberus/tests (excluding bmc/, cheri-ci/, pnvi_testsuite/)

## Summary

| Metric | Count |
|--------|-------|
| Total tests | 5014 |
| Cerberus success | 1505 |
| Cerberus failed | 3509 |
| Lean success | 648 |
| Lean failed | 828 |
| **Match rate** | **95%** (616/648) |

## Mismatches to Investigate

### False Positive UB (14 tests)

Lean detects UB but Cerberus returns a value. These need investigation.

| Test | Lean UB | Cerberus |
|------|---------|----------|
| 20000910-1 | UB043_indirection_invalid_value | 0 |
| 20020402-3 | UB043_indirection_invalid_value | 0 |
| 20021118-1 | UB036_exceptional_condition | 0 |
| 20030914-1 | UB036_exceptional_condition | 0 |
| 20050826-2 | UB036_exceptional_condition | 0 |
| 20060412-1 | UB_CERB002a_out_of_bound_load | 0 |
| 20080604-1 | UB_CERB002a_out_of_bound_load | 0 |
| 941014-1 | UB_internal_type_error | 0 |
| 950607-2 | UB036_exceptional_condition | 0 |
| 961223-1 | UB036_exceptional_condition | 0 |
| pr36339 | UB025_misaligned_pointer_conversion | 0 |
| pr38212 | UB043_indirection_invalid_value | 0 |
| pr52129 | UB_CERB004_unspecified__equality_both_arith_or_ptr | 0 |
| pr55875 | UB043_indirection_invalid_value | 0 |

**By UB category:**
- `UB043_indirection_invalid_value` (4 tests) - Invalid pointer dereference
- `UB036_exceptional_condition` (5 tests) - Arithmetic exception
- `UB_CERB002a_out_of_bound_load` (2 tests) - Out of bounds access
- `UB025_misaligned_pointer_conversion` (1 test) - Alignment issue
- `UB_CERB004_unspecified__equality` (1 test) - Pointer comparison
- `UB_internal_type_error` (1 test) - Internal type mismatch

### False Negative UB (1 test)

| Test | Lean | Cerberus UB |
|------|------|-------------|
| function_vs_var | 4096 | UB024_out_of_range_pointer_to_integer_conversion |

### Other Semantic Differences (3 tests)

| Test | Lean | Cerberus |
|------|------|----------|
| 0046-jump_inside_lifetime | 0 | UNSPECIFIED |
| b | 110 | 220 |
| treiber | UB_CERB004_unspecified__equality_ptr_vs_NULL | 0 |

### Unsequenced Race (12 tests) - Out of Scope

Expected mismatches - we sequentialize execution.

- 0300-unseq_race_ko01.undef through 0306-unseq_race_ko07.undef (7 tests)
- 6.5-2.1, 6.5-2.2
- call_race

## Lean Failure Categories (828 tests)

| Error | Count |
|-------|-------|
| `exit` procedure not found | 349 |
| Pattern match failures | 90 |
| `ImplConst.other` not implemented | 79 |
| Forward declaration issues | 50 |
| `main` with wrong args | 47 |
| Type errors on binary ops | 59 |
| Missing stdlib: `memset` | 20 |
| Missing stdlib: `abort` | 18 |
| `va_start` not implemented | 18 |
| `SHR_signed_negative` not implemented | 13 |
| Missing stdlib: `strcpy` | 9 |

## Priority Assessment

### High Priority - Semantic Bugs (18 tests)

These represent actual bugs in our interpreter that need fixing:

1. **False positive UB cases (14)** - We're detecting UB when Cerberus doesn't. Most likely causes:
   - Overly strict bounds checking
   - Incorrect pointer validity tracking
   - Alignment checks that Cerberus doesn't enforce

2. **False negative UB (1)** - `function_vs_var`: We miss a pointer-to-integer overflow

3. **Other semantic diffs (3)** - `0046-jump_inside_lifetime`, `b`, `treiber`

### Medium Priority - Missing Features (349+ tests)

Would unlock many more tests but not semantic bugs:

1. **`exit()` support (349)** - Single biggest unlock, but requires early termination semantics
2. **`main(argc, argv)` (47)** - Need to handle command-line args

### Low Priority - Out of Scope (90+ tests)

Not worth fixing for current goals:

1. **Pattern match failures (90)** - Rare Core constructs
2. **Unsequenced race (12)** - By design, we sequentialize
3. **Variadic functions (18)** - Complex, low value
4. **Missing stdlib (47)** - `memset`, `abort`, `strcpy` - would need stubs

### Recommendation

Focus on the 18 semantic bug tests first - these affect correctness. The `exit()` feature is tempting due to volume but doesn't affect match rate on tests that do run.
