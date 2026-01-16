# Full Test Suite Results

**Date:** 2026-01-02 (Updated: 2026-01-06)
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

## Update 2026-01-06

Many of the false positive UB cases have been fixed by recent interpreter improvements:
- Unspecified memory initialization fix
- Floating point binary operations
- Pattern matching for Unspecified values

### Re-tested False Positive UB Cases

Of the 14 originally reported false positives, **12 now pass**:
- ✅ 20000910-1, 20020402-3, 20021118-1, 20030914-1, 20050826-2
- ✅ 20060412-1, 20080604-1, 950607-2, 961223-1
- ✅ pr36339, pr38212, pr52129

**Still failing (2 tests):**

| Test | Lean UB | Cerberus | Notes |
|------|---------|----------|-------|
| 941014-1 | UB_internal_type_error | 0 | Internal type mismatch |
| pr55875 | UB043_indirection_invalid_value | 0 | Invalid pointer deref |

### False Negative UB (1 test)

| Test | Lean | Cerberus UB |
|------|------|-------------|
| function_vs_var | 4096 | UB024_out_of_range_pointer_to_integer_conversion |

### Other Semantic Differences (2 tests)

| Test | Lean | Cerberus | Notes |
|------|------|----------|-------|
| b | 110 | 220 | Memory model difference |
| treiber | FAIL (impl proc) | 0 | Uses unimplemented impl function |

**Note:** 0046-jump_inside_lifetime now passes (fixed by unspecified memory init)

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
