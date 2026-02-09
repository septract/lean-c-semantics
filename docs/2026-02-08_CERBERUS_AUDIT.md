# Comprehensive Cerberus Implementation Audit

**Date**: 2026-02-08
**Auditors**: 5-agent team (AST types, expression evaluation, reduction semantics, memory model, values/conversions)
**Scope**: Lean implementation vs Cerberus reference in `./cerberus/` — types, semantics, and execution. CN implementation explicitly excluded.

## Executive Summary

The Lean implementation is a **high-quality, mostly faithful** translation of Cerberus's Core semantics suitable for differential testing of sequential C programs. The core architecture (AST types, reduction semantics, memory model, race detection) is sound. However, the audit identified **~40 discrepancies** of varying severity:

- **6 Critical** — incorrect behavior that produces wrong results
- **8 High** — missing functionality or semantic differences that affect correctness
- **12 Medium** — differences that affect error reporting or edge cases
- **~14 Low/Minor** — cosmetic differences, missing features for rare cases

The most impactful issues cluster in **integer conversions** (missing `_Bool` case, division-by-zero returning 0, `OpAnd`/`OpOr` wrong on integers) and **memory model edge cases** (`allocateObject` parameter confusion, missing union member tracking, NULL pointer arithmetic behavior).

---

## Table of Contents

1. [Critical Issues](#1-critical-issues)
2. [High Priority Issues](#2-high-priority-issues)
3. [Medium Priority Issues](#3-medium-priority-issues)
4. [Low Priority Issues](#4-low-priority-issues)
5. [Deliberately Unsupported Features](#5-deliberately-unsupported-features)
6. [Detailed Audit by Area](#6-detailed-audit-by-area)
   - 6.1 Core AST Types
   - 6.2 Pure Expression Evaluation
   - 6.3 Reduction Semantics
   - 6.4 Memory Model
   - 6.5 Values and Conversions
7. [Refactoring Recommendations](#7-refactoring-recommendations)

---

## 1. Critical Issues

These produce incorrect results and should be fixed first.

### C1. Missing `_Bool` special case in `convertInt`

**Files**: `Eval.lean:635-651` vs `core_eval.lem:62-67`

Cerberus special-cases conversion to `_Bool`: any non-zero value becomes 1, zero becomes 0. The Lean implementation uses general modular wrapping to range [0,1], which gives wrong results for even non-zero values.

```
Example: converting 2 to _Bool
  Cerberus: 2 != 0, so returns 1 ✓
  Lean: 0 + (2 - 0) % 2 = 0   ✗ WRONG
```

**Fix**: Add `if ity == .bool then if iv.val == 0 then 0 else 1` at the start of `convertInt`.

### C2. `evalIntOp` treats `OpAnd`/`OpOr` as bitwise on integers

**Files**: `Eval.lean:271-281` vs `core_eval.lem:454-514`

In Cerberus, `OpAnd` and `OpOr` are **boolean-only** operators. Applying them to integer operands is an error. Lean incorrectly applies bitwise AND/OR using `Int.toNat`, which also loses negative number information (`(-1).toNat = 0` in Lean).

**Fix**: Remove the integer cases for `OpAnd`/`OpOr` in `evalBinop`. These operators should only work on `Vtrue`/`Vfalse`. Bitwise operations are handled by `CivAND`/`CivOR`/`CivXOR` constructors.

### C3. `wrapIntOp` / `catchExceptionalOp` return 0 on division by zero

**Files**: `Eval.lean:664-666` and `Eval.lean:694-696`

When the divisor is zero, these functions silently return 0 instead of propagating an error. This is a "Fail, Never Guess" violation.

```lean
-- Current (WRONG):
| .div => if i2.val != 0 then i1.val.tdiv i2.val else 0
-- Should be:
| .div => if i2.val != 0 then i1.val.tdiv i2.val else throw (.ub .ub044_divByZero)
```

**Fix**: Replace `else 0` with `else throw` an appropriate error for all div/rem-by-zero paths.

### C4. `Carray` constructor has forbidden `.unspecified .void` fallback

**Files**: `Eval.lean:477-484` vs `core_eval.lem:616-631`

When constructing an array, non-`Vloaded` values silently become `.unspecified .void` instead of failing with `Illformed_program`.

**Fix**: Replace `| _ => .unspecified .void` with `| v => throw (.illformedProgram s!"Carray: expected loaded value, got {v}")`.

### C5. `allocateObject` parameter confusion — alignment used as size

**Files**: `Concrete.lean:1091-1095` vs `impl_mem.ml:1288-1290`

The `MemoryOps.allocateObject` instance confuses parameters: it uses the alignment `IntegerValue` as the allocation size, and the `requestedAddr` `Option Nat` as alignment. Cerberus computes size internally via `sizeof ty`.

**Why tests pass**: The only callsite (`allocateErrno`) passes alignment=4 for `signed int` (sizeof=4), so the bug is masked.

**Fix**: The instance should compute `size := sizeof ty` from the type parameter, and use the `IntegerValue` parameter as alignment.

### C6. `valueFromMemValue` array fallback also uses `.unspecified .void`

**Files**: `Eval.lean:364`

Same pattern as C4 — a `| _ => .unspecified .void` catch-all when converting array element `MemValue`s back to `LoadedValue`s.

**Fix**: Same as C4, fail explicitly.

---

## 2. High Priority Issues

These affect correctness for specific programs or error detection.

### H1. Store does not update `lastUsedUnionMembers`

**Files**: `Concrete.lean` (storeImpl) vs `impl_mem.ml:1694-1700`

Cerberus tracks which union member was last written to via `last_used_union_members`. Lean does not update this field on store. This means union reconstruction on load may use the wrong member type.

**Fix**: Update `lastUsedUnionMembers` in `storeImpl` when storing through a pointer with a union member annotation.

### H2. `effArrayShiftPtrval` on NULL returns NULL instead of erroring

**Files**: `Concrete.lean:863` vs `impl_mem.ml:2248-2252`

Cerberus fails with `MerrArrayShift` when shifting a NULL pointer. Lean silently returns NULL.

**Fix**: Throw `MemError.arrayShift` for NULL pointer in `effArrayShiftPtrval`.

### H3. Kill does not remove allocation from map

**Files**: `Concrete.lean:773` vs `impl_mem.ml:1539-1542`

Cerberus removes the allocation from `allocations` and adds to `dead_allocations`. Lean only adds to `dead_allocations`. This affects error messages (different error types for use-after-free) and could cause subtle differences in allocation lookup behavior.

**Fix**: Remove the allocation from `st.allocations` in `killImpl` when marking as dead.

### H4. Kill does not validate `is_dynamic` for dynamic frees

**Files**: `Concrete.lean` vs `impl_mem.ml:1516-1523`

Cerberus checks that `free()` is only called on dynamically allocated addresses. Lean does not check this, allowing static allocations to be freed without error.

**Fix**: Check if the allocation was dynamically allocated before allowing dynamic kill.

### H5. `Erun` pushes extra stack frame

**Files**: `Step.lean:538-543` vs `core_reduction.lem:1412-1416`

Cerberus's `Erun` replaces the current arena and env without pushing a stack frame. Lean pushes a new empty continuation frame. This could cause incorrect behavior for goto-like save/run control flow within a function.

**Fix**: Replace `pushEmptyCont` with direct env/arena replacement to match Cerberus.

### H6. `PEcall` only searches `file.stdlib`, not `file.funs`

**Files**: `Eval.lean:882-909` vs `core_eval.lem:965-995`

Cerberus's `call_function` looks up both `file.stdlib` AND `file.funs` for pure function calls. Lean only searches `file.stdlib`. User-defined pure functions won't be found.

**Fix**: Add `file.funs` lookup fallback in `PEcall` evaluation.

### H7. Impl proc handling completely missing

**Files**: `Step.lean:572-576` vs `core_reduction.lem:949-1071`

All `Eproc (Impl ...)` cases throw `notImplemented`. Cerberus handles: `errno` (returns errno pointer), `exit` (terminates), `generic_ffs`, `ctz`, `bswap16/32/64` (GCC builtins).

Note: `exit` IS handled in the `Eccall` path, so C function call `exit()` works.

**Fix**: Implement at least `errno` and `exit` in the `Eproc` path. GCC builtins can remain unimplemented with explicit errors.

### H8. `PEsym` missing procedure-pointer fallback

**Files**: `Eval.lean:792-795` vs `core_eval.lem:570-586`

When a symbol is not in the environment, Cerberus checks if it's a `Proc` in `file.funs` and returns `null_ptrval(void)` as a function pointer value. Lean has no such fallback.

**Fix**: Add the `file.funs` lookup fallback returning a function pointer.

---

## 3. Medium Priority Issues

### M1. `Civmax`/`Civmin` do not call `unatomic_` on the ctype

**Files**: `Eval.lean:502-511` vs `core_eval.lem:632-639`

Cerberus calls `Ctype.unatomic_` before extracting the integer type. Lean matches `ct.ty` directly. An `atomic(int)` type would fail in Lean but succeed in Cerberus. Same issue affects `CivCOMPL`, `CivAND`, `CivOR`, `CivXOR`.

### M2. Store locking always uses `.constQualified`

**Files**: `Concrete.lean:740` vs `impl_mem.ml:1777-1784`

Cerberus derives the readonly kind from the symbol prefix (string literal, temporary lifetime, or const-qualified). Lean always uses `constQualified`. This affects which UB code is reported.

### M3. Load/Store with `Prov_none` throws wrong error type

**Files**: `Concrete.lean` vs `impl_mem.ml:1609,1716-1717`

Cerberus throws `OutOfBoundPtr`. Lean throws `noProvPtr`. Different error types but both correctly prevent the operation.

### M4. `eq_ptrval` missing function-pointer-via-funptrmap comparison

**Files**: `Concrete.lean` vs `impl_mem.ml:1839-1847`

When comparing `PVfunction(name)` with `PVconcrete(addr)`, Cerberus looks up `addr` in `funptrmap`. Lean always returns false for this case.

### M5. `diffPtrval` returns 0 for cross-allocation instead of erroring

**Files**: `Concrete.lean:835-854` vs `impl_mem.ml:1954-2063`

Cerberus fails with `MerrPtrdiff` for cross-allocation pointer subtraction. Lean returns 0.

### M6. Pointer relational comparisons don't check for null or cross-allocation UB

**Files**: `Concrete.lean:1108-1123` vs `impl_mem.ml:1886-1951`

Cerberus (with `SW_strict_pointer_relationals`) checks same allocation and fails on null. Lean just compares addresses, missing UB053.

### M7. `PEareCompatible` uses structural equality instead of `are_compatible`

**Files**: `Eval.lean:1118-1130` vs `core_eval.lem:1090-1102`

C11 6.2.7 compatibility rules are more nuanced than structural equality (e.g., compatible enum types, compatible function types).

### M8. Store/Load accept `loaded(.specified(.pointer))` values

**Files**: `Step.lean:765-773,799-804` vs `core_reduction.lem`

Lean is more permissive — it accepts loaded specified pointer values where Cerberus expects only object pointer values.

### M9. `convertInt` wrapping formula differs from Cerberus

**Files**: `Eval.lean:643-649` vs `core_eval.lem:29-47`

Cerberus uses `IntRem_f` (floored remainder). Lean uses Euclidean modulo with a double-modulo pattern. These should be equivalent for positive ranges but needs mathematical verification.

### M10. Shift operations may differ for negative numbers

**Files**: `Eval.lean:667-668` vs `core_eval.lem:89-90`

Lean `>>>` is arithmetic shift right. Cerberus `IntDiv x (2^y)` is truncated division. For negative numbers: `-7 >>> 1 = -4` (Lean) vs `-7 / 2 = -3` (Cerberus). May be masked by subsequent wrapping.

### M11. `ptrfromint` missing integer wrapping to pointer range

**Files**: `Concrete.lean:906-911` vs `impl_mem.ml:2126-2173`

Cerberus wraps the integer to `[0, 2^(8*sizeof_pointer) - 1]`. Lean does not wrap.

### M12. `evalBinop` extracts integers from `Vloaded` values

**Files**: `Eval.lean:284-288` vs `core_eval.lem`

Lean's `valueToInt` matches both `Vobject (OVinteger)` and `Vloaded (LVspecified (OVinteger))`. Cerberus only matches the former. Lean is more permissive.

---

## 4. Low Priority Issues

### L1. Pure `arrayShiftPtrval` on NULL returns NULL instead of crashing
(`Interface.lean:351` vs `impl_mem.ml:2217`)

### L2. `targetMaxAlign` is 16 vs Cerberus's 8
(`Layout.lean:39` — comment says "x86_64 compatibility")

### L3. UndefinedBehavior uses `other` catch-all for ~150 of ~200 variants
(`Undefined.lean` — works for differential testing via string comparison)

### L4. `PEisScalar` / `PEisInteger` throw `NotImpl` instead of being implemented
(`Eval.lean:1058-1059` — rarely encountered in practice)

### L5. `PEmemop` (pure memory operations) throws `NotImpl`
(`Eval.lean:1132` — `ByteFromInt`/`IntFromByte` may be needed)

### L6. `PEconstrained` throws `NotImpl` (acceptable for concrete model)

### L7. NaN/Inf floating-point arithmetic not implemented
(`Eval.lean:407-408` — throws error instead)

### L8. Missing `CivNULLcap` constructor (CHERI-specific)

### L9. `Eexcluded` takes `Paction` instead of `generic_action` (minor structural difference)

### L10. `generic_action` drops `'a` type parameter (acceptable for JSON-based execution)

### L11. `Esave` parameter structure drops `pass_by_value_or_pointer` and C-type info

### L12. `pure_memop` uses String instead of structured enum

### L13. `PEimpl` handles specific constants directly rather than looking up `file.impl`
(`Eval.lean:797-823` — works for common cases but misses rare impl constants)

### L14. `Pexpr.constrained` uses `(String, Pexpr)` instead of `(mem_iv_constraint, pexpr)`

---

## 5. Deliberately Unsupported Features

These are features we intentionally do not support. They should be documented but do not need fixes.

### Concurrency Model
- **Epar / Ewait** — Parallel execution / thread synchronization
- **LinuxFence / LinuxLoad / LinuxStore / LinuxRMW** — Linux memory model actions
- **Thread IDs** — All operations omit thread_id parameter

### Memory Models
- **PNVI-ae / PNVI-ae-udi** — No iota creation/resolution, no taint exposure tracking
- **CHERI** — No capability model, no CHERI error types, no `CivNULLcap`
- **VIP** — No VIP-specific error types
- **Device memory** — No device memory ranges

### Memory Model Switches
- **SW_strict_pointer_relationals** — No strict pointer comparison mode
- **SW_strict_reads** — No strict uninitialized read mode
- **SW_zap_dead_pointers** — No pointer zapping on deallocation
- **SW_forbid_nullptr_free** — No configurable null-free behavior
- **SW_zero_initialised** — No zero-initialization switch

### Other
- **Constrained values** — PEconstrained and pull_constrained (symbolic memory model)
- **BMC** — Bounded model checking (PEbmc_assume)
- **Filesystem operations** — printf, read, write, open, etc.
- **Most GCC builtins** — generic_ffs, ctz, bswap (not needed for test suite)
- **Sequentialisation pass** — Eunseq is handled natively instead

---

## 6. Detailed Audit by Area

### 6.1 Core AST Types

**Reference**: `core.ott` (596 lines), `core_aux.lem`, `builtins.lem`
**Lean files**: `Core/Types.lean`, `Core/Expr.lean`, `Core/Value.lean`, `Core/Ctype.lean`, `Core/IntegerType.lean`, `Core/Sym.lean`, `Core/File.lean`, `Core/Annot.lean`, `Core/Repr.lean`, `Core/Undefined.lean`

**Assessment**: Faithful translation. All major types present with correct constructors.

| Cerberus Type | Lean Type | Status |
|---|---|---|
| `core_object_type` | `ObjectType` | MATCH (all 6 constructors) |
| `core_base_type` | `BaseType` | MATCH (all 8 constructors) |
| `binop` | `Binop` | MATCH (all 13 operators) |
| `iop` | `Iop` | MATCH (all 7 variants) |
| `polarity` | `Polarity` | MATCH |
| `value` | `Value` | MATCH (all 8 constructors) |
| `ctor` | `Ctor` | Minor: missing `CivNULLcap` (CHERI) |
| `generic_pexpr` | `Pexpr` / `APexpr` | MATCH |
| `generic_expr` | `Expr` / `AExpr` | MATCH |
| `generic_action` | `Action` / `AAction` | Minor: drops `'a` param, missing Linux actions |
| `generic_file` | `File` | MATCH (all 11 fields) |
| `generic_memop` | `Memop` | MATCH |
| `generic_pattern` | `Pattern` / `APattern` | MATCH |
| `annot` | `Annot` | MATCH (all 14 constructors) |
| `dyn_annotation` | `DynAnnotation` | MATCH |

**Type parameterization**: Cerberus uses `'a`, `'bty`, `'sym` type parameters. Lean uses concrete types (`Sym`, `Option BaseType`). This works because JSON export always produces typed Core.

### 6.2 Pure Expression Evaluation

**Reference**: `core_eval.lem` (1198 lines)
**Lean files**: `Semantics/Eval.lean` (1223 lines)

**Assessment**: Covers most Pexpr cases correctly. Critical issues in integer conversions and operator handling.

Key matches: `PEval`, `PEundef`, `PEerror`, `PEcase`, `PEarray_shift`, `PEmember_shift`, `PEnot`, `PEstruct`, `PEunion`, `PEmemberof`, `PElet`, `PEif`, `PEis_signed`, `PEis_unsigned`, `PEbmc_assume`, `PEcfunction`, `Cnil`, `Ccons`, `Ctuple`, `Civsizeof`, `Civalignof`, `Cspecified`, `Cunspecified`, `Cfvfromint`, `Civfromfloat`.

Key mismatches: `convertInt` (_Bool), `OpAnd`/`OpOr` semantics, div-by-zero handling, `Carray` fallback, `PEsym` proc fallback, `PEcall` lookup scope.

### 6.3 Reduction Semantics

**Reference**: `core_reduction.lem` (1471 lines), `core_reduction_aux.lem` (310 lines)
**Lean files**: `Semantics/Step.lean` (1766 lines), `Semantics/Context.lean`, `Semantics/NDDriver.lean`, `Semantics/Race.lean`, etc.

**Assessment**: High fidelity. The architectural choice of continuations vs evaluation contexts is sound. Race detection is comprehensive and correct.

All major Expr cases implemented and matching:
- `Epure`, `Elet`, `Eif`, `Ecase` — MATCH
- `Ewseq`, `Esseq` — MATCH
- `Esave`, `Erun` — MATCH (minor stack handling difference in Erun)
- `Eproc`, `Eccall` — MATCH (impl procs unimplemented)
- `Eaction` (pos/neg) — MATCH (including neg action transformation)
- `Eunseq` — MATCH (full race detection)
- `Ebound`, `End`, `Eannot`, `Eexcluded` — MATCH
- `Ememop` — MATCH (all memory operations)
- `SeqRMW` — MATCH (all 3 subcases)

Notable: The continuation-based approach and context-based approach produce equivalent reduction sequences. The `contToContext`/`contextToContElems` bridges are correct.

### 6.4 Memory Model

**Reference**: `impl_mem.ml` (3015 lines), `mem_common.lem` (705 lines)
**Lean files**: `Memory/Concrete.lean`, `Memory/Interface.lean`, `Memory/Layout.lean`, `Memory/Types.lean`

**Assessment**: Faithful translation of concrete memory model. Data structures match. Layout (sizeof/alignof) is correct for all basic types. Main issues are in edge cases.

sizeof/alignof for all types: MATCH (including struct padding, array layout, union layout).

Key discrepancies: `allocateObject` parameter confusion (C5), missing union member tracking (H1), NULL pointer arithmetic (H2), kill not removing allocation (H3), pointer comparison edge cases (M4-M6).

### 6.5 Values and Conversions

**Reference**: `core_eval.lem`, `builtins.lem`, `implementation.lem`, `undefined.lem`
**Lean files**: `Core/Value.lean`, `Semantics/Eval.lean`, `Semantics/Step.lean`

**Assessment**: Value representation is correct. Integer arithmetic mostly correct but with critical conversion bugs.

Value hierarchy match: integer_value, pointer_value, floating_value, mem_value, object_value, loaded_value, value — all correct.

Key discrepancies: `_Bool` conversion (C1), bitwise on integers (C2), div-by-zero (C3), shift semantics (M10), wrapping formula (M9).

---

## 7. Refactoring Recommendations

### Phase 1: Critical Fixes (estimated: small, focused changes)

These can be fixed independently with targeted edits:

1. **C1**: Add `_Bool` special case to `convertInt` in `Eval.lean`
2. **C2**: Remove integer cases from `OpAnd`/`OpOr` in `evalBinop`
3. **C3**: Replace `else 0` with error throw in `wrapIntOp`/`catchExceptionalOp`
4. **C4+C6**: Replace `| _ => .unspecified .void` with explicit failures
5. **C5**: Fix `allocateObject` to compute `sizeof ty` for size

### Phase 2: High Priority Fixes (estimated: moderate effort)

6. **H1**: Add `lastUsedUnionMembers` update in `storeImpl`
7. **H2**: Error on NULL in `effArrayShiftPtrval`
8. **H3**: Remove allocation from map in `killImpl`
9. **H4**: Add `is_dynamic` validation in kill
10. **H5**: Fix `Erun` to not push extra stack frame
11. **H6**: Add `file.funs` lookup in `PEcall`
12. **H7**: Implement `errno` and `exit` in `Eproc` impl path
13. **H8**: Add procedure-pointer fallback in `PEsym`

### Phase 3: Medium Priority Fixes (estimated: moderate to significant effort)

14. **M1**: Add `unatomic_` calls in `Civmax`/`Civmin`/`CivCOMPL`/etc.
15. **M2**: Derive readonly kind from prefix in store locking
16. **M3-M6**: Fix error types in memory operations for Cerberus compatibility
17. **M7**: Implement proper `are_compatible` for type compatibility
18. **M9-M10**: Verify and potentially fix wrapping formula and shift semantics
19. **M11**: Add integer wrapping in `ptrfromint`

### Phase 4: Polish (estimated: low effort, low priority)

20. **L2**: Consider whether `targetMaxAlign=16` is correct for our use case
21. **L4**: Implement `PEis_scalar`/`PEis_integer`
22. **L5**: Implement `ByteFromInt`/`IntFromByte` pure memops
23. **L13**: Consider looking up `file.impl` for rare impl constants

### Testing Strategy

After each phase:
1. Run `make test` to verify no regressions
2. Run `make test-interp` to check differential testing match rate
3. Specific test cases should be added for each fix:
   - `_Bool` conversion: `tests/debug/conv-NN-bool-conversion.c`
   - Division by zero: `tests/debug/arith-NN-div-zero.c`
   - NULL pointer arithmetic: `tests/debug/ptr-NN-null-shift.c`
   - Union member tracking: `tests/debug/struct-NN-union-store.c`

---

## Appendix: File Correspondence Map

| Cerberus File | Lean File(s) | Purpose |
|---|---|---|
| `core.ott` | `Core/Types.lean`, `Core/Expr.lean`, `Core/Value.lean` | AST grammar |
| `core_eval.lem` | `Semantics/Eval.lean` | Pure expression evaluation |
| `core_reduction.lem` | `Semantics/Step.lean`, `Semantics/Context.lean` | Effectful reduction |
| `core_reduction_aux.lem` | `Semantics/State.lean`, `Semantics/Race.lean` | Reduction helpers |
| `impl_mem.ml` | `Memory/Concrete.lean` | Concrete memory model |
| `mem_common.lem` | `Memory/Interface.lean`, `Memory/Types.lean` | Memory interface |
| `builtins.lem` | `Semantics/Step.lean` (inline) | Builtin functions |
| `implementation.lem` | `Semantics/Eval.lean` (inline) | Impl-defined behavior |
| `undefined.lem` | `Core/Undefined.lean` | UB codes |
| `core_aux.lem` | `Semantics/Env.lean`, `Core/` (various) | Auxiliary functions |
| `annot.lem` | `Core/Annot.lean`, `Core/DynAnnot.lean` | Annotations |
| `ctype.lem` | `Core/Ctype.lean`, `Core/IntegerType.lean` | C type representation |
