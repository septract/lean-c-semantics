# Coverage Round 3: Deep Gap-Closing Tests

Created: 2026-02-15

## Baseline (after Round 2)

| File | Coverage | Expressions |
|------|----------|-------------|
| `impl_mem.ml` | **45.90%** | 947/2063 |
| `core_eval.ml` | **56.02%** | 442/789 |
| `core_reduction.ml` | **70.09%** | 600/856 |
| `translation.ml` | **61.70%** | 2626/4255 |
| `driver.ml` | **38.87%** | 496/1276 |
| **Project total** | **32.57%** | 13,828/42,432 |

## Methodology

Rounds 1-2 covered broad categories and specific function-level gaps. Round 3 targets
remaining reachable code by analyzing the HTML coverage report line-by-line. Each test
targets specific uncovered expressions identified by line number.

## Test Plan

### Category 1: `union3/` -- Union Types (~50+ points across impl_mem.ml, core_eval.ml, translation.ml)

Unions are the single biggest cross-file gap. `PEunion` in core_eval.ml (L879-891) is
completely uncovered. `MVunion` in impl_mem.ml `repr` (L1215-1219) and `abst` (L1073-1093)
are uncovered. `AilEunion` in translation.ml (L2842-2863) is uncovered.

| Test | Target |
|------|--------|
| `union3-001-basic-store-load.c` | Store int to union member, read back -- `repr`/`abst` MVunion, PEunion |
| `union3-002-type-pun-int-float.c` | Write int, read as float -- union type punning through memory |
| `union3-003-union-init.c` | Designated union initializer `(union U){.f = 3.14}` -- AilEunion translation |
| `union3-004-union-copy.c` | Assign one union to another -- union bulk copy |
| `union3-005-union-return.c` | Return union from function -- union value passing |
| `union3-006-union-memberof.c` | Access union member from union value (not pointer) -- PEmemberof union path |
| `union3-007-nested-union.c` | Union containing struct, struct containing union -- nested repr/abst |

### Category 2: `varargs/` -- Variadic Functions (~30 points in impl_mem.ml)

`va_copy` (L2706-2721), `va_end` (L2743-2754), `va_list` (L2756-2764) all completely
uncovered. These are straightforward to trigger.

| Test | Target |
|------|--------|
| `varargs-001-va-copy.libc.c` | `va_copy` then iterate copy -- exercises va_copy path |
| `varargs-002-va-end.libc.c` | `va_start`/`va_end` pair -- exercises va_end cleanup |
| `varargs-003-va-multiple-types.libc.c` | Variadic with int, long, double args -- mixed type va_arg |
| `varargs-004-va-pass-through.libc.c` | Forward va_list to another function -- va_list as parameter |
| `varargs-005-va-sum.libc.c` | Sum N integers via varargs -- basic variadic pattern |

### Category 3: `arith3/` -- Uncovered Arithmetic Ops (~10 points in core_eval.ml)

`IOpDiv`, `IOpRem_t`, `IOpShl`, `IOpShr` in `mk_iop` (L89-92) are uncovered. These
are the wrapping integer operations used for unsigned arithmetic in Core.

| Test | Target |
|------|--------|
| `arith3-001-unsigned-div.c` | `unsigned x = UINT_MAX; return x / 3;` -- IOpDiv via PEwrapI |
| `arith3-002-unsigned-mod.c` | `unsigned x = UINT_MAX; return x % 7;` -- IOpRem_t via PEwrapI |
| `arith3-003-unsigned-shl.c` | `unsigned x = 1; return x << 16;` -- IOpShl via PEwrapI |
| `arith3-004-unsigned-shr.c` | `unsigned x = UINT_MAX; return x >> 16;` -- IOpShr via PEwrapI |
| `arith3-005-bool-conv.c` | `_Bool b = 42; return b;` -- mk_conv_int _Bool path (L65,69) |
| `arith3-006-wrap-unsigned-char.c` | `unsigned char c = 300; return c;` -- mk_conv_int wrapI (L79-80) |

### Category 4: `io/` -- Filesystem & Printf (~20+ points in core_reduction.ml, driver.ml)

The `Step_fs2` dispatch (core_reduction.ml L1440-1442) and driver.ml filesystem paths
(L315-395) are completely uncovered. Printf format conversion (driver.ml L134-155)
is uncovered.

| Test | Target |
|------|--------|
| `io-001-printf-basic.libc.c` | `printf("hello\n");` -- Step_fs2 dispatch, printf path |
| `io-002-printf-int.libc.c` | `printf("%d\n", 42);` -- printf format conversion |
| `io-003-printf-string.libc.c` | `printf("%s\n", "world");` -- string format |
| `io-004-puts.libc.c` | `puts("hello");` -- simpler FS function |
| `io-005-printf-multi.libc.c` | `printf("%d %d %d\n", 1, 2, 3);` -- variadic printf args |

### Category 5: `ptr3/` -- Remaining Pointer Gaps (~40+ points in impl_mem.ml)

#### `intfromptr` function pointer case (L2439-2461, ~10 pts)

| Test | Target |
|------|--------|
| `ptr3-001-funcptr-to-int.libc.c` | `(uintptr_t)&func` -- cast function pointer to integer |
| `ptr3-002-int-to-ptr-null.libc.c` | `(int*)(intptr_t)0` -- ptrfromint null path (L2126-2174) |
| `ptr3-003-int-to-ptr-roundtrip.libc.c` | `ptr → intptr_t → ptr` with non-null -- ptrfromint non-null |

#### `diff_ptrval` array path (L1954-1985, ~10 pts)

| Test | Target |
|------|--------|
| `ptr3-004-ptrdiff-array.c` | `&a[4] - &a[1]` with explicit array type -- diff_ptrval Array path |
| `ptr3-005-ptrdiff-cross-alloc.c` | `&a - &b` -- diff_ptrval error_postcond (different allocations, UB) |

#### `eq_ptrval` provenance mismatch (L1871-1879, ~6 pts)

| Test | Target |
|------|--------|
| `ptr3-006-eq-one-past-end.c` | Compare one-past-end of array A with start of array B -- provenance mismatch |

#### Pointer relational with NULL (L1890-1950, ~10 pts)

| Test | Target |
|------|--------|
| `ptr3-007-null-lt-null.c` | `(int*)0 < (int*)0` -- null pointer relational comparison |
| `ptr3-008-null-le-null.c` | `(int*)0 <= (int*)0` -- null pointer le |

### Category 6: `mem3/` -- Memory Model Deep Gaps (~30+ points in impl_mem.ml)

#### `_Bool` trap representation (L1580-1598, ~14 pts)

| Test | Target |
|------|--------|
| `mem3-001-bool-load.c` | `_Bool b = 1; return b;` -- triggers is_Bool check in load |
| `mem3-002-bool-trap.c` | Write non-0/1 value via char* to _Bool -- trap representation check |

#### `readonly_status` / `select_ro_kind` (L1325-1332, L1704-1710, ~12 pts)

| Test | Target |
|------|--------|
| `mem3-003-const-compound-literal.c` | `const int *p = (const int[]){10,20}; return p[0];` -- PrefTemporaryLifetime |
| `mem3-004-string-write-attempt.c` | Attempt to write to string literal -- select_ro_kind PrefStringLiteral |

#### `merge_taint` NewTaint (L932-939, ~12 pts)

| Test | Target |
|------|--------|
| `mem3-005-struct-multi-ptr.c` | Struct with two pointer members, store and load back -- merge_taint |
| `mem3-006-array-of-ptrs.c` | Array of pointers, store and load -- taint merging |

#### `realloc(NULL)` (L2668-2696, ~4 pts)

| Test | Target |
|------|--------|
| `mem3-007-realloc-null.libc.c` | `realloc(NULL, 16)` -- null realloc acts as malloc |

#### `eff_member_shift_ptrval` (L2359, ~1 pt)

| Test | Target |
|------|--------|
| `mem3-008-eff-member-shift.c` | `p->field = 42;` where p is a pointer to struct -- effectful member shift |

### Category 7: `ctrl3/` -- Reduction Engine Gaps (~20+ points in core_reduction.ml)

#### Alloc eval branch (L813-819, ~6 pts)

| Test | Target |
|------|--------|
| `ctrl3-001-malloc-computed-size.libc.c` | `malloc(n * sizeof(int))` where n is a variable -- Alloc0 operand eval |

#### Null function pointer call (L1407, ~1 pt)

| Test | Target |
|------|--------|
| `ctrl3-002-null-funcptr-call.c` | `void (*fp)(void) = 0; fp();` -- UB, null function pointer |

#### Function pointer via void* cast (L1411 in core_reduction, L919-926 in core_eval)

| Test | Target |
|------|--------|
| `ctrl3-003-funcptr-void-cast.c` | Cast function ptr to void*, cast back, call -- PEcfunction void* path |

#### UB088: fall off non-void function (core_eval.ml L621)

| Test | Target |
|------|--------|
| `ctrl3-004-falloff-nonvoid.c` | `int f(void) { }` -- UB, reached end of non-void function |

#### Unsequenced race reordering (L253-258, ~3 pts)

| Test | Target |
|------|--------|
| `ctrl3-005-unseq-neg-pos.c` | `f(a++, b)` where neg action is first -- DA_neg vs DA_pos ordering |

### Category 8: `compound/` -- Compound Assignment & Assert (~20+ pts in translation.ml)

| Test | Target |
|------|--------|
| `compound-001-add-assign.c` | `x += 5;` -- compound assignment translation (L750-770) |
| `compound-002-sub-assign.c` | `x -= 3;` |
| `compound-003-mul-assign.c` | `x *= 2;` |
| `compound-004-div-assign.c` | `x /= 4;` |
| `compound-005-mod-assign.c` | `x %= 3;` |
| `compound-006-shl-assign.c` | `x <<= 2;` |
| `compound-007-shr-assign.c` | `x >>= 1;` |
| `compound-008-and-assign.c` | `x &= 0xFF;` |
| `compound-009-or-assign.c` | `x |= 0x80;` |
| `compound-010-xor-assign.c` | `x ^= 0xFF;` |
| `compound-011-assert-true.libc.c` | `assert(1);` -- assert() translation (L2697-2718) |
| `compound-012-assert-expr.libc.c` | `assert(x > 0);` -- assert with expression |

## Summary

| Category | Tests | Primary target files | Est. new points |
|----------|-------|---------------------|----------------|
| `union3/` | 7 | impl_mem.ml + core_eval.ml + translation.ml | ~50+ |
| `varargs/` | 5 | impl_mem.ml | ~30 |
| `arith3/` | 6 | core_eval.ml | ~10 |
| `io/` | 5 | core_reduction.ml + driver.ml | ~20+ |
| `ptr3/` | 8 | impl_mem.ml | ~40+ |
| `mem3/` | 8 | impl_mem.ml | ~40+ |
| `ctrl3/` | 5 | core_reduction.ml + core_eval.ml | ~15+ |
| `compound/` | 12 | translation.ml | ~20+ |
| **Total** | **56** | | **~225+** |

## Expected Results

| File | Current | Est. After Round 3 | Change |
|------|---------|-------------------|--------|
| `impl_mem.ml` | 45.90% (947) | ~52% (~1075) | +~130 pts |
| `core_eval.ml` | 56.02% (442) | ~60% (~475) | +~35 pts |
| `core_reduction.ml` | 70.09% (600) | ~74% (~635) | +~35 pts |
| `translation.ml` | 61.70% (2626) | ~62.5% (~2660) | +~35 pts |
| **Project total** | 32.57% (13,828) | ~33.5%+ (~14,200) | +~350 pts |
