# CN Test Suite Audit Report

**Date**: 2026-02-18
**Scope**: All 64 passing tests in `tests/cn/` (non-`.fail.c`, non-`.smt-fail.c`)
**Purpose**: Identify spurious passes, weak tests, and tests affected by the `*NoSMT` bug

## Executive Summary

Of 64 passing tests:
- **5 tests are trivially passing** (no CN annotations or all-trusted): they exercise zero type-checker logic
- **8 tests have weak postconditions** (no `ensures`, or ensures with only resource existence): they would pass even with incorrect value tracking
- **0 tests are affected by the `*NoSMT` SMT encoding bug**: the bug is in dead code that no current test exercises
- **~18 tests are duplicates or near-duplicates** of other tests (same feature, same complexity)
- **~33 tests are genuinely non-trivial** and exercise real type-checker features with SMT verification

The biggest concern is not spurious passes but **missing coverage**: several important CN features have zero or weak test coverage.

## The `*NoSMT` Bug Analysis

### Bug Description

In `lean/CerbLean/CN/Verification/SmtLib.lean` (lines 377-401), `mulNoSMT`, `divNoSMT`, `remNoSMT`, and `modNoSMT` are translated as actual arithmetic operations (`*`, `div`, `bvmul`, etc.) instead of uninterpreted functions.

In CN, the `*NoSMT` variants exist to prevent the SMT solver from reasoning about the arithmetic result -- they should be opaque. Translating them as actual operations makes the solver overly powerful and could cause it to prove things CN intentionally leaves unprovable.

### Impact on Current Tests: NONE

The `*NoSMT` operations are **never generated** by any current code path:

1. **CN spec parser** (`lean/CerbLean/CN/Parser.lean` lines 486-535): Only generates `.add`, `.sub`, `.mul`, `.div`, `.rem` -- never NoSMT variants.
2. **Type checker** (`lean/CerbLean/CN/TypeChecking/Pexpr.lean` lines 1261-1268): `catchExceptionalCondition` uses `.add`, `.mul`, `.div`, `.rem` -- never NoSMT variants.
3. **No code path** in the type checker or spec resolution generates NoSMT BinOp values.

The NoSMT constructors exist in the `BinOp` type only for completeness (matching CN's OCaml `binop` type). The SmtLib translation code for them is dead code -- incorrect, but unreachable.

### When This Would Matter

The bug would become live if/when:
- The `core_to_mucore` translation is implemented and generates `mulNoSMT`/`divNoSMT` for C arithmetic results (CN's `compile.ml` uses these)
- User-written CN specs could somehow generate NoSMT operations (currently impossible through the parser)

**Recommendation**: Fix the bug now (replace with uninterpreted functions) to prevent future issues. Mark with FIXME if not fixing immediately.

## Test-by-Test Analysis

### Category 1: Trivially Passing (5 tests)

These tests exercise **zero** type-checker logic and would pass with any implementation.

| Test | Why Trivial |
|------|-------------|
| `004-trusted.c` | All functions marked `trusted;` -- type checker skips verification entirely |
| `058-left-shift.c` | **No CN annotations at all** -- trivially correct (0 functions verified) |
| `065-simple-while-loop.c` | **No CN annotations at all** -- trivially correct |
| `069-enum-bitwise.c` | All functions marked `trusted;` -- type checker skips verification entirely |
| `071-shift-mixed-types.c` | **No CN annotations at all** -- trivially correct |

**Risk**: These inflate the pass count without testing anything. A completely broken type checker would pass all 5.

### Category 2: Weak Postconditions (8 tests)

These tests have no `ensures` clause (or only resource-existence ensures), so the SMT solver has nothing to verify beyond structural type checking and overflow checks.

| Test | Feature | Why Weak |
|------|---------|----------|
| `043-negation-overflow.c` | Overflow guard (`MINi32()`) | `requires -i > MINi32()` but no ensures -- only checks the overflow guard is satisfiable |
| `048-int-narrowing.c` | Integer narrowing cast | Only `requires` range constraints, no `ensures` -- just checks the cast doesn't overflow |
| `052-body-add-no-spec-arith.c` | Body arithmetic | `ensures take v2 = Owned<int>(p)` -- no value constraint on v2 |
| `062-implies.c` | `implies` keyword | Inline `assert` only -- no function-level ensures |
| `064-for-loop-invariant.c` | Loop invariant | Loop invariant `inv` clause, main is trusted, no ensures |
| `070-increments.c` | Pre/post increment on sub-int types | `ensures take C2 = RW(p); take S2 = RW(q)` -- resource existence only, no value checks |
| `074-negation-safe.c` | Negation overflow guard | Same as 043 with slightly different syntax |
| `085-unsigned-arithmetic.c` | Unsigned addition | `ensures return == x + y` -- this is actually non-trivial, but the overflow bounds are extremely loose (1000+1000 << u32 max) |

**Risk**: A type checker that correctly handles resources but ignores value constraints would pass these. However, most of these are **intentionally testing structural features** (overflow detection, resource threading) rather than value reasoning.

### Category 3: Near-Duplicates (18 tests)

These tests cover the same feature at the same complexity level as other tests. They provide some regression value but limited incremental coverage.

| Test | Duplicates | Feature |
|------|------------|---------|
| `036-add-zero.c` | 037 | Addition with constraints |
| `037-add-one-zero.c` | 036 | Addition with constraints |
| `038-write-cell.c` | 078 | Write to Owned cell |
| `039-write-two-cells.c` | 079 | Write to two Owned cells |
| `041-add-overflow.c` | 072 | Overflow-safe addition |
| `042-ternary-return.c` | 075 | Conditional return with ternary spec |
| `044-pre-post-increment.c` | -- | Same feature as 002 (increment) but tests pre/post semantics |
| `045-struct-field-frame.c` | 077 | Struct field write with frame |
| `049-return-eq-param.c` | 006 | `return == x` identity |
| `050-return-literal-spec.c` | 007 | `return == 42` literal |
| `051-spec-add-literal.c` | 031 | `return == x + 1` |
| `053-body-add-spec-constraint.c` | 002 | Increment pointer with spec |
| `072-add-overflow-safe.c` | 041 | Overflow-safe addition (same feature, near-identical code) |
| `073-add-unsigned.c` | 085 | Unsigned addition |
| `075-conditional-return.c` | 042 | Conditional return with ternary spec |
| `076-swap-rw.c` | 003 | Swap with RW instead of Owned |
| `078-write-cell.c` | 038 | Write to RW cell |
| `079-write-two-cells.c` | 039 | Write to two RW cells |

### Category 4: Genuinely Non-Trivial (33 tests)

These tests exercise real type-checker features and would fail with a trivial "always ok" type checker.

#### Simple Value Tracking (return == expr)

| Test | Feature | SMT Obligation |
|------|---------|----------------|
| `001-simple-owned.c` | Owned pointer read, return value | `return == v` where v is loaded value |
| `006-pure-constraint.c` | Pure parameter constraint | `return == x` given `x > 0` |
| `007-literal-return.c` | Literal return value | `return == 42` |
| `027-local-variable.c` | Local variable allocation | `return == 42` via local |
| `031-return-expression.c` | Return expression | `return == x + 1` |
| `033-return-from-load.c` | Return from pointer load | `return == v` from Owned<int> |
| `040-decrement-return.c` | Subtraction | `return == x - 1` |

#### Arithmetic and Overflow

| Test | Feature | SMT Obligation |
|------|---------|----------------|
| `002-increment.c` | Pointer increment with overflow guard | `v2 == v + 1` given range constraints |
| `024-multiple-constraints.c` | Multiple constraints | `return == x + y` with bounds |
| `028-two-pointers.c` | Two pointer dereferences | `return == vp + vq` |
| `035-return-two-params.c` | Multiple params | `return == a + b` |

#### Conditional Reasoning

| Test | Feature | SMT Obligation |
|------|---------|----------------|
| `020-conditional-resource.c` | Conditional branch with resource | `v == v2` in both branches |
| `032-return-conditional.c` | Conditional return, abs value | `return >= 0` in both branches |
| `086-multiple-returns.c` | Multiple return paths | `(x >= y) ? (return == x) : (return == y)` |

#### Struct Access

| Test | Feature | SMT Obligation |
|------|---------|----------------|
| `023-struct-access.c` | Struct field read | `return == v.x` |
| `087-nested-struct.c` | Nested struct access | `return == o.s.val` |
| `077-struct-field-write.c` | Struct field write + frame | `StructPre.x == StructPost.x; StructPost.y == 0` |

#### Memory Model

| Test | Feature | SMT Obligation |
|------|---------|----------------|
| `003-swap.c` | Swap two values | `va2 == vb; vb2 == va` |
| `021-conditional-write.c` | Conditional write | Resource existence in both branches |
| `022-pointer-arithmetic.c` | Array element access | `return == v` from `arr + idx` |
| `046-pointer-aliasing.c` | Pointer aliasing | `cell1 == cell2` with aliased write |
| `047-trusted-free.c` | Function call consuming resource | Resource consumed by callee |
| `066-null-to-int.c` | Null pointer to integer cast | `return == 0u64` given `ptr_eq(p, NULL)` |

#### Bitwise Operations

| Test | Feature | SMT Obligation |
|------|---------|----------------|
| `054-bitwise-or.c` | Bitwise OR | `return == x \| y` |
| `055-bitwise-xor.c` | Bitwise XOR | `return == x ^ y` |
| `056-bitwise-and.c` | Bitwise AND with assert | `assert(-1 & 0 == 0)`, `assert(y == 4)` |
| `057-bitwise-compl.c` | Bitwise complement with CN function | `assert(~0 == -1)`, function calls |

#### Type Casts

| Test | Feature | SMT Obligation |
|------|---------|----------------|
| `005-division.c` | Division with non-zero guard | `return == x / y` given `y != 0` |
| `059-mod-nonzero.c` | Modulo with non-zero guard | `return == x % y` given `y != 0` |
| `060-mod-casting.c` | Cross-type modulo | `return == x % (u32)y` with cast |
| `088-cast-signed-unsigned.c` | Signed-to-unsigned cast | `return == (u32)x` given `x >= 0` |

#### CN-Specific Features

| Test | Feature | SMT Obligation |
|------|---------|----------------|
| `063-unary-negation.c` | CN function definitions with negation | `assert(negate_paren() == 127i8)` (wrapping) |

## Potential Spurious Pass Concerns

### Concern 1: Tests with no main function verification

23 tests have no `main` function or have `main` without CN annotations. This is **not** a concern because the type checker verifies each annotated function independently. The `main` function is irrelevant for CN verification.

### Concern 2: `RW` vs `Owned` resource types

Some tests use `RW` (045, 046, 047, 070, 076, 077, 078, 079, 083, 084) and others use `Owned` (001, 002, 003, 020-024, etc.). Both should work similarly for verification. If the type checker handles `Owned` but has bugs in `RW`, the `RW` tests could be spuriously passing due to the type checker treating `RW` as `Owned`. However, since both `RW` and `Owned` tests with value constraints (like 076-swap-rw.c with `Qa == Pb; Qb == Pa`) ARE passing with correct SMT obligations, this seems fine.

### Concern 3: Weak overflow testing

Several overflow tests (041, 043, 072, 074) constrain inputs to avoid overflow but the constraints are so loose that overflow is impossible. For example, `add_safe` with `MINi32 <= sum <= MAXi32` -- this is the correct CN pattern but doesn't test edge cases. The corresponding `.fail.c` tests (081-overflow-max.c, 082-overflow-min.c) DO test that overflow is detected, which is more important.

### Concern 4: Inline assert tests without function specs

Tests 056 (bitwise-and), 057 (bitwise-compl), and 062 (implies) use inline `/*@ assert(...) @*/` rather than function-level specs. These depend on the assert-checking path in the type checker. If inline asserts were silently ignored, these would pass spuriously.

### Concern 5: Loop invariant testing is minimal

Only test 064 exercises loop invariants (`inv` clause), and the invariant is very simple (`0 <= i; i <= 10; acc <= 10`). This is a complex feature that deserves more testing.

### Concern 6: Function call verification (callee spec lookup)

Only test 047 exercises function calls where the callee has a CN spec. This is a critical feature (the `ccall` path) with minimal coverage.

## Missing Coverage

Features with zero or near-zero test coverage among passing tests:

1. **Iterated resources / arrays**: No test exercises `each` or array-style iterated resources
2. **Predicate definitions**: No test defines or uses `predicate` or `datatype`
3. **Lemmas**: No test uses `lemma`
4. **Map/list types**: No test uses CN map or list types
5. **Quantifiers**: No test uses `forall` or `exists` in specs
6. **Multiple function calls**: Only 047 has one function call; no test chains calls
7. **Recursive data structures**: No test exercises linked lists, trees, etc.
8. **Global variables**: No test exercises global variable specifications
9. **`*NoSMT` operations**: Dead code -- never generated, never tested
10. **Inline `extract`/`instantiate`**: No test exercises resource extraction patterns

## Recommendations

### High Priority

1. **Fix the `*NoSMT` SMT encoding bug** in `SmtLib.lean` (lines 377-401) before it becomes live code. Use uninterpreted functions instead of actual arithmetic.

2. **Remove or annotate the 3 no-annotation tests** (058, 065, 071): Either add CN annotations or mark them as Cerberus-only tests that shouldn't be in `tests/cn/`.

3. **Strengthen weak postcondition tests**: Add value constraints to tests 043, 048, 052, 062, 064, 070, 074.

### Medium Priority

4. **Add negative tests for inline asserts**: A test where `assert(false)` should fail, to ensure asserts are actually checked.

5. **Add more function call tests**: Tests with multiple callee specs, nested calls, and resource flow between callers/callees.

6. **Add loop tests**: More complex loop invariants, nested loops, loops with resource manipulation.

7. **Deduplicate test suite**: Consider removing near-duplicate tests (e.g., keep 078/079 and remove 038/039, or vice versa) to reduce noise.

### Low Priority

8. **Add edge-case overflow tests**: Tests where the overflow check is tight (values near INT_MIN/INT_MAX).

9. **Add predicate/lemma/datatype tests** as those features are implemented.

10. **Add quantifier tests** as forall/exists support is implemented.

## Appendix: Complete Test Classification

| # | Test | Annotations | Ensures | Feature | Trivial? | Duplicate Of | NoSMT Affected? |
|---|------|-------------|---------|---------|----------|-------------|-----------------|
| 001 | simple-owned | Owned R/W | return==v, v==v2 | Pointer read | No | -- | No |
| 002 | increment | Owned R/W | v2==v+1 | Pointer write+arith | No | 053 | No |
| 003 | swap | Owned R/W | va2==vb, vb2==va | Two-pointer swap | No | 076 | No |
| 004 | trusted | trusted | (none) | Trusted skip | **YES** | -- | No |
| 005 | division | pure | return==x/y | Division+precond | No | -- | No |
| 006 | pure-constraint | pure | return==x | Identity function | No | 049 | No |
| 007 | literal-return | pure | return==42 | Literal return | No | 050 | No |
| 020 | conditional-resource | Owned | v==v2 | Branch+resource | No | -- | No |
| 021 | conditional-write | Owned | (resource only) | Branch+write | Weak | -- | No |
| 022 | pointer-arithmetic | Owned | return==v, v==v2 | arr+idx access | No | -- | No |
| 023 | struct-access | Owned<struct> | return==v.x | Struct field read | No | -- | No |
| 024 | multiple-constraints | pure | return==x+y, bounds | Multiple ensures | No | -- | No |
| 027 | local-variable | (none) | return==42 | Local var | No | -- | No |
| 028 | two-pointers | Owned x2 | return==vp+vq | Two resources | No | -- | No |
| 031 | return-expression | pure | return==x+1 | Spec arithmetic | No | 051 | No |
| 032 | return-conditional | pure | return>=0 | Branch return | No | -- | No |
| 033 | return-from-load | Owned | return==v, v==v2 | Load return | No | 001 | No |
| 035 | return-two-params | pure | return==a+b | Multi-param | No | -- | No |
| 036 | add-zero | pure | return==x+y (x=y=0) | Trivial add | No | 037 | No |
| 037 | add-one-zero | pure | return==y (x=0) | Add with zero | No | 036 | No |
| 038 | write-cell | Owned | CellPost==7 | Write known val | No | 078 | No |
| 039 | write-two-cells | Owned x2 | C1Post==7, C2Post==8 | Two writes | No | 079 | No |
| 040 | decrement-return | pure | return==x-1 | Subtraction | No | -- | No |
| 041 | add-overflow | pure+let+cast | return==x+y | Overflow safe add | No | 072 | No |
| 042 | ternary-return | pure | return==(i==0?0:1) | Ternary in spec | No | 075 | No |
| 043 | negation-overflow | pure | (none) | MINi32() builtin | Weak | 074 | No |
| 044 | pre-post-increment | pure+let+cast | return==i+1 | ++i vs i++ | No | -- | No |
| 045 | struct-field-frame | RW<struct> | Pre.x==Post.x, Post.y==0 | Struct frame | No | 077 | No |
| 046 | pointer-aliasing | RW | Cell2Post==8, cell1==cell2 | Aliasing | No | -- | No |
| 047 | trusted-free | RW, callee spec | Ypost resource | Function call | No | -- | No |
| 048 | int-narrowing | pure | (none) | MINu8/MAXu8 builtins | Weak | -- | No |
| 049 | return-eq-param | pure | return==x | Identity | No | 006 | No |
| 050 | return-literal-spec | pure | return==42 | Literal | No | 007 | No |
| 051 | spec-add-literal | pure | return==x+1 | Spec arith | No | 031 | No |
| 052 | body-add-no-spec | Owned | (resource only) | Body arith only | Weak | -- | No |
| 053 | body-add-spec | Owned | v2==v+1 | Body+spec arith | No | 002 | No |
| 054 | bitwise-or | pure | return==x\|y | Bitwise OR | No | -- | No |
| 055 | bitwise-xor | pure | return==x^y | Bitwise XOR | No | -- | No |
| 056 | bitwise-and | assert | (inline assert) | Bitwise AND+function | No | -- | No |
| 057 | bitwise-compl | assert+function | (inline assert) | Bitwise complement | No | -- | No |
| 058 | left-shift | **NONE** | **NONE** | **Nothing** | **YES** | -- | No |
| 059 | mod-nonzero | pure | return==x%y | Modulo | No | -- | No |
| 060 | mod-casting | pure+cast | return==x%(u32)y | Cross-type mod | No | -- | No |
| 062 | implies | assert | (inline assert) | `implies` keyword | Weak | -- | No |
| 063 | unary-negation | CN function+assert | (assert) | CN function defs | No | -- | No |
| 064 | for-loop-invariant | inv clause | (none) | Loop invariant | Weak | -- | No |
| 065 | simple-while-loop | **NONE** | **NONE** | **Nothing** | **YES** | -- | No |
| 066 | null-to-int | ptr_eq+ensures | return==0u64 | Null cast | No | -- | No |
| 069 | enum-bitwise | **trusted** | **NONE** | **Nothing** | **YES** | -- | No |
| 070 | increments | RW | (resource only) | Sub-int inc/dec | Weak | -- | No |
| 071 | shift-mixed-types | **NONE** | **NONE** | **Nothing** | **YES** | -- | No |
| 072 | add-overflow-safe | pure+let+cast | return==x+y | Overflow safe add | No | 041 | No |
| 073 | add-unsigned | pure+let+cast | return==x+y | Unsigned add | No | 085 | No |
| 074 | negation-safe | pure | (none) | MINi32() builtin | Weak | 043 | No |
| 075 | conditional-return | pure | return==(i==0?0:1) | Ternary | No | 042 | No |
| 076 | swap-rw | RW | Qa==Pb, Qb==Pa | Swap with RW | No | 003 | No |
| 077 | struct-field-write | RW<struct> | Pre.x==Post.x, Post.y==0 | Struct frame | No | 045 | No |
| 078 | write-cell | RW | CellPost==7 | Write known val | No | 038 | No |
| 079 | write-two-cells | RW x2 | C1Post==7, C2Post==8 | Two writes | No | 039 | No |
| 085 | unsigned-arithmetic | pure | return==x+y | Unsigned add | No | 073 | No |
| 086 | multiple-returns | pure | (x>=y)?(ret==x):(ret==y) | Multi-return | No | -- | No |
| 087 | nested-struct | Owned<nested> | return==o.s.val, o==o2 | Nested struct | No | -- | No |
| 088 | cast-signed-unsigned | pure+cast | return==(u32)x | Type cast | No | -- | No |
