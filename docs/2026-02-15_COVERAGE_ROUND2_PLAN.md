# Coverage Round 2: Targeted Gap-Closing Tests

Created: 2026-02-15

## Baseline (after Round 1)

| File | Coverage | Expressions |
|------|----------|-------------|
| `impl_mem.ml` | **44.26%** | 913/2063 |
| `core_eval.ml` | **52.09%** | 411/789 |
| `core_reduction.ml` | **60.63%** | 519/856 |
| **Project total** | **31.27%** | 13,269/42,432 |

## Methodology

Round 1 wrote broad tests across categories. Round 2 targets specific uncovered functions
identified by analyzing the HTML coverage report. Each test is designed to hit a specific
uncovered code path.

## Triage: Reachable vs Unreachable

Many gaps are **unreachable** from `--exec --batch` and should not be targeted:

### Unreachable (skip these)

| Gap | Why unreachable | Uncov pts |
|-----|----------------|-----------|
| `mk_ui_values`, `serialise_*` | Web UI serialization, not called by `--exec` | ~127 |
| `pp_pointer_value`, `pp_mem_value` | Pretty-printing, not called by `--exec --batch` | ~55 |
| `dot_of_mem_state` | Debug DOT output, gated by debug constant | ~19 |
| `show_method` (core_step2) | Debug display, needs debug verbosity flag | ~41 |
| `PEmemop` (CHERI ops) | CHERI memory model only | ~24 |
| `pull_constrained` | PNVI provenance model only | ~50 |
| `Prov_symbolic` branches everywhere | PNVI-ae-udi model only (load/store/kill/shift/compare) | ~200+ |
| `Prov_device` branches | Memory-mapped IO, no standard C trigger | ~15 |
| RMW/Fence/CAS in `step_action` | Concurrency TODOs (all `error "TODO"`) | ~8 |
| `eval_pexpr_aux_broken`/`eval_pexpr` | Likely dead code (superseded by `eval_pexpr_aux2`) | ~18 |
| `PEis_scalar/integer/signed/unsigned` | Core-level intrinsics, not generated from C | ~28 |
| `PEbmc_assume` | BMC mode only | ~6 |

**Total unreachable: ~600+ expression points.** This means impl_mem.ml has a realistic
ceiling around 65-70% (not 100%) from `--exec --batch` testing alone.

### Reachable — Target These

Organized by estimated coverage gain (uncovered expression points).

## Test Plan

### Category 1: `builtin/` — GCC Builtins (~55 points in core_reduction.ml)

The `process_impl_proc` function handles `__builtin_ffs`, `__builtin_ctz`, `__builtin_bswap16/32/64`, and `exit()`. All completely uncovered. Trivially exercisable.

| Test | Target |
|------|--------|
| `builtin-001-ffs.c` | `__builtin_ffs(0)` returns 0, `__builtin_ffs(12)` returns 3 |
| `builtin-002-ctz.c` | `__builtin_ctz(8)` returns 3, `__builtin_ctz(1)` returns 0 |
| `builtin-003-bswap16.c` | `__builtin_bswap16(0x1234)` returns `0x3412` |
| `builtin-004-bswap32.c` | `__builtin_bswap32(0x12345678)` returns `0x78563412` |
| `builtin-005-bswap64.c` | `__builtin_bswap64(0x0102030405060708LL)` |
| `builtin-006-exit.c` | `exit(42)` — exercises the `exit` impl proc path (libc) |

### Category 2: `ptr2/` — Pointer Comparisons & Arithmetic (~150+ points in impl_mem.ml)

#### Pointer relational comparisons (45 pts: `le_ptrval`, `ge_ptrval`, `gt_ptrval` — all 0% covered)

Round 1 only tested `<` which hits `lt_ptrval`. Need `<=`, `>=`, `>`.

| Test | Target |
|------|--------|
| `ptr2-001-le-same-array.c` | `p1 <= p2` within array — exercises `le_ptrval` |
| `ptr2-002-ge-same-array.c` | `p1 >= p2` within array — exercises `ge_ptrval` |
| `ptr2-003-gt-same-array.c` | `p1 > p2` within array — exercises `gt_ptrval` |
| `ptr2-004-le-equal.c` | `p <= p` (same pointer) — boundary case |
| `ptr2-005-ge-equal.c` | `p >= p` (same pointer) — boundary case |

#### `eff_array_shift_ptrval` (104 pts — entirely 0% covered)

This is the effectful version of pointer arithmetic, called from `driver.ml` for `PtrArrayShift` memory actions. It does bounds checking. The pure version (`array_shift_ptrval`) is already covered. The effectful version is called when pointer arithmetic is a memory action (not a pure expression).

Key insight: `eff_array_shift_ptrval` is called via `PtrArrayShift` in the driver. This happens when C code does pointer arithmetic that goes through the effectful memory action path. This should be triggered by array indexing in effectful contexts (stores, loads through computed pointers).

| Test | Target |
|------|--------|
| `ptr2-006-eff-array-shift.c` | `*(arr + i)` where `i` is a variable — effectful shift |
| `ptr2-007-eff-negative-shift.c` | `*(p - 1)` where p points past first element |
| `ptr2-008-eff-one-past-end.c` | Pointer to one-past-end, compare but don't deref |
| `ptr2-009-eff-malloc-shift.c` | Array shift on `malloc`'d memory (libc) |
| `ptr2-010-eff-zero-shift.c` | `*(p + 0)` — zero offset edge case |

#### Function pointer operations (28 pts in `eq_ptrval` + 38 pts in `PEcfunction`)

| Test | Target |
|------|--------|
| `ptr2-011-funcptr-eq.c` | `&f == &f` — function pointer equality |
| `ptr2-012-funcptr-ne.c` | `&f != &g` — function pointer inequality |
| `ptr2-013-funcptr-call.c` | Call through function pointer — exercises `PEcfunction` |
| `ptr2-014-funcptr-array.c` | Array of function pointers, index and call |
| `ptr2-015-funcptr-param.c` | Pass function pointer as parameter and call |

### Category 3: `eval2/` — Core Evaluator Gaps (~90+ points in core_eval.ml)

#### `PEmemberof` (46 pts — struct/union member access on values)

`PEmemberof` extracts a member from a struct/union *value* (not a pointer). This is different from `PEmember_shift` which does pointer-level member access. `PEmemberof` is used when a struct value (not a pointer to struct) needs member extraction in a pure expression context.

| Test | Target |
|------|--------|
| `eval2-001-struct-member-value.c` | Return `s.x` where `s` is a struct value (not pointer) |
| `eval2-002-union-member-value.c` | Read union member from union value |
| `eval2-003-nested-member-value.c` | `s.inner.x` on nested struct values |
| `eval2-004-struct-init-member.c` | Access member of struct initializer: `(struct S){1,2}.x` |

#### Float operations in evaluator (45 pts — float comparison and arithmetic)

The float test files from Round 1 may not exercise the Core evaluator's float paths because they go through the memory model (store/load). Need float operations in *pure expression* context.

| Test | Target |
|------|--------|
| `eval2-005-float-compare-eq.c` | `f == g` float comparison in return |
| `eval2-006-float-compare-lt.c` | `f < g` float comparison |
| `eval2-007-float-compare-le.c` | `f <= g` float comparison |
| `eval2-008-float-compare-gt.c` | `f > g` float comparison |
| `eval2-009-float-compare-ge.c` | `f >= g` float comparison |
| `eval2-010-float-arith-pure.c` | `return (float)a + (float)b` — float arithmetic in pure expr |
| `eval2-011-float-sub-mul-div.c` | Float subtraction, multiplication, division in one expression |

#### `OpAnd`/`OpOr` boolean operations (20 pts)

| Test | Target |
|------|--------|
| `eval2-012-bool-and-false.c` | `(_Bool)0 && (_Bool)1` — OpAnd with false |
| `eval2-013-bool-or-true.c` | `(_Bool)1 || (_Bool)0` — OpOr with true |
| `eval2-014-bool-or-both-false.c` | `(_Bool)0 || (_Bool)0` — OpOr returns false |

#### `PEare_compatible` (6 pts)

| Test | Target |
|------|--------|
| `eval2-015-are-compatible.c` | `_Generic` expression to trigger type compatibility check |

### Category 4: `store2/` — Store/Load Gaps (~50+ points in impl_mem.ml)

#### `store_lock` path (part of 54 uncovered pts in `store`)

`store_lock` is called from `translation.ml` for string literals and const compound literals. It marks allocations as read-only after initialization.

| Test | Target |
|------|--------|
| `store2-001-string-literal.c` | `const char *s = "hello"; return s[0];` — string literal creates locked store |
| `store2-002-compound-literal.c` | `int *p = (int[]){1,2,3}; return p[0];` — compound literal with store_lock |
| `store2-003-const-compound.c` | `const int *p = (const int[]){10,20}; return p[1];` |
| `store2-004-string-compare.c` | Multiple string literals, compare characters |
| `store2-005-string-index.c` | Index into string literal at various positions |

### Category 5: `ctrl2/` — Reduction Gaps (~15 points in core_reduction.ml)

#### `SeqRMW` nested neg action (7 pts)

| Test | Target |
|------|--------|
| `ctrl2-001-seqrmw-sseq.c` | `(x++, x++)` — sequential RMW with sseq context |
| `ctrl2-002-postinc-in-expr.c` | `a[i++] = i++` in unsequenced context (UB, exercises neg action) |

#### `errno` builtin (covered but related)

| Test | Target |
|------|--------|
| `ctrl2-003-errno.c` | Access `errno` after operation (libc) |

### Category 6: `misc/` — Miscellaneous Gaps

| Test | Target | Points |
|------|--------|--------|
| `misc-001-void-ptr-arith.c` | `void *p = ...; p = p + 1;` — GNU extension void* arithmetic, exercises `is_void` branch in `array_shift_ptrval` | ~5 |
| `misc-002-null-member-shift.c` | Member shift on NULL pointer (if it doesn't crash Cerberus) — `member_shift_ptrval` PVnull branch | ~8 |
| `misc-003-offsetof.c` | `offsetof(struct S, field)` — exercises `offsetof_ival` | ~3 |

## Summary

| Category | Tests | Target file | Est. new points |
|----------|-------|-------------|----------------|
| `builtin/` | 6 | core_reduction.ml | ~55 |
| `ptr2/` | 15 | impl_mem.ml + core_eval.ml | ~150+ |
| `eval2/` | 15 | core_eval.ml | ~90+ |
| `store2/` | 5 | impl_mem.ml | ~30+ |
| `ctrl2/` | 3 | core_reduction.ml | ~15 |
| `misc/` | 3 | impl_mem.ml | ~15 |
| **Total** | **47** | | **~355+** |

## Expected Results

| File | Current | Est. After Round 2 | Change |
|------|---------|-------------------|--------|
| `impl_mem.ml` | 44.26% (913) | ~54% (~1110) | +~200 pts |
| `core_eval.ml` | 52.09% (411) | ~63% (~500) | +~90 pts |
| `core_reduction.ml` | 60.63% (519) | ~68% (~580) | +~60 pts |
| **Project total** | 31.27% (13,269) | ~33%+ (~14,000) | +~700 pts |

## Realistic Ceilings

Due to unreachable code (PNVI, CHERI, UI, debug), realistic maximum coverage
from `--exec --batch` testing alone:

| File | Realistic max | Why |
|------|--------------|-----|
| `impl_mem.ml` | ~65-70% | ~600 pts in PNVI/device/UI/debug code |
| `core_eval.ml` | ~75-80% | ~100 pts in PNVI constrained/CHERI/BMC code |
| `core_reduction.ml` | ~75-80% | ~100 pts in debug display/concurrency TODOs |

## Files to Modify

| File | Change |
|------|--------|
| `tests/coverage/builtin/*.c` | 6 new test files |
| `tests/coverage/ptr2/*.c` | 15 new test files |
| `tests/coverage/eval2/*.c` | 15 new test files |
| `tests/coverage/store2/*.c` | 5 new test files |
| `tests/coverage/ctrl2/*.c` | 3 new test files |
| `tests/coverage/misc/*.c` | 3 new test files |
