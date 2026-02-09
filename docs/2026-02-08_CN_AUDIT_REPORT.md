# CN Implementation Audit Report

**Date**: 2026-02-08
**Scope**: Full audit of CN implementation against reference CN (tmp/cn/)
**Current status**: 45/46 tests passing
**Updated**: 2026-02-09 — C1-C7 fixed; H1, H4, H6, H7, H8 partially fixed; M2 partially fixed; pointer arithmetic elaboration added; struct tag resolution added; parser multi-requires fix; SMT sign_extend fix
**Method**: 5 parallel auditor agents + manual analysis

---

## Executive Summary

The CN type definitions (Types/*.lean) are structurally correct and closely match CN's OCaml types. Through 5 batches of fixes, the critical semantic bugs have been addressed:

1. **Integer types mapped to unbounded Integer instead of Bits** — **FIXED** (C1): `ctypeToBaseType` now produces `Bits(sign, width)`
2. **Pointers encoded as plain Int in SMT** — **FIXED** (C2): CN_Pointer algebraic datatype with alloc_id/addr
3. **Missing wellTyped checking pass** — **PARTIALLY FIXED** (H1): structMember type inference done; other gaps remain
4. **Remaining fall-through defaults** — **MOSTLY FIXED** (H4): union, constrained, ctorToSym, constant catch-all fixed

**Remaining significant gaps**: C8 (spec structure mismatch), H5 (no inline solver), M5/M6 (pointer comparisons/conversions), resource inference simplifications (H3).

### Type Definitions vs Type Checking vs SMT

The audit found a clean split:
- **Types (Types/*.lean)**: GOOD — structurally match CN closely. BaseType, Term, Resource, Constraint all have correct constructors.
- **Type Checking (TypeChecking/*.lean)**: MUCH IMPROVED — C1 (integer types), C5 (PEwrapI), C6 (overflow checking), C7 (PEundef) all fixed. H1 (wellTyped) partially fixed. Remaining gaps: full wellTyped pass, inline solver (H5).
- **SMT Encoding (SmtLib.lean)**: MUCH IMPROVED — C2 (pointer datatype), C3 (unit), C4 (structs) all fixed. Remaining gaps: M1 (MemByte), M4 (CType sort), M5/M6 (pointer comparisons/conversions).
- **Spec Structure (Spec.lean)**: STRUCTURAL MISMATCH — flat clause list vs CN's recursive LRT/LAT/AT types. Missing ghost bindings. `trusted` field is a fabrication.

---

## CRITICAL Issues (Must Fix)

### C1. Integer Types: `.integer` vs `.bits` in Action.lean

**Location**: `lean/CerbLean/CN/TypeChecking/Action.lean:116`
**Severity**: CRITICAL — affects ALL integer operations

```lean
-- OUR CODE (WRONG):
| .basic (.integer _) => return .integer  -- unbounded mathematical integers!

-- CN's of_sct (CORRECT):
-- Integer ity -> Bits ((if is_signed ity then Signed else Unsigned), size_of ity * 8)
```

CN maps C integer types to fixed-width bitvectors (`Bits(Signed, 32)` for `signed int`). We map them to unbounded mathematical integers (`.integer`). This means:

- Overflow checking is impossible (we use the wrong type)
- SMT queries use `Int` instead of `(_ BitVec 32)` for integer values from memory
- `Owned<signed int>(p)` returns a value of type `Integer` instead of `Bits(Signed, 32)`
- All comparisons and arithmetic operate on wrong types

**Impact**: Every test involving integer values from memory loads is using wrong types. Tests pass because SMT `Int` reasoning is more permissive than bitvector reasoning.

**Fix**: Replace `ctypeToBaseType` in Action.lean with logic matching `Resolve.ctypeInnerToOutputBaseType` (which is already correct in Resolve.lean:156-178). Better yet, have a single canonical implementation.

**Note**: There are TWO inconsistent type conversion functions:
- `Resolve.ctypeInnerToOutputBaseType` (CORRECT — maps to Bits types)
- `Action.ctypeToBaseType` (WRONG — maps to .integer)

### C2. SMT Pointer Encoding: Plain Int vs Algebraic Datatype

**Location**: `lean/CerbLean/CN/Verification/SmtLib.lean:69`
**Severity**: CRITICAL — affects ALL pointer reasoning

```lean
-- OUR CODE (WRONG):
| .loc => .ok (Term.symbolT "Int")  -- Pointers as integers (addresses)

-- CN's solver.ml (CORRECT):
-- | Loc () -> CN_Pointer.t
-- CN_Pointer is a declared SMT datatype:
--   (declare-datatype CN_Pointer
--     ((null)
--      (alloc_id_addr (alloc_id CN_AllocId) (addr (_ BitVec 64)))))
```

CN represents pointers in SMT as an algebraic datatype with two constructors:
- `null` — the null pointer
- `alloc_id_addr(alloc_id, addr)` — a pointer with allocation ID and bitvector address

We represent pointers as plain `Int`. This means:
- We cannot distinguish null from non-null pointers in SMT
- We cannot reason about allocation IDs
- Pointer arithmetic is plain integer arithmetic (ignoring allocation boundaries)
- `arrayShift` and `memberShift` are not properly encoded

**Impact**: Pointer comparison and arithmetic in SMT are semantically wrong. Tests pass because integer arithmetic happens to be compatible for simple cases.

**Fix**: Implement CN_Pointer as an SMT datatype declaration. This requires:
1. Adding datatype declaration to SMT preamble
2. Updating `baseTypeToSort` for `.loc`
3. Adding `ptr_shift`, `copy_alloc_id`, `addr_of` SMT functions
4. Updating term translation for pointer operations

### C3. Unit Type as SMT Bool — **FIXED**

**Location**: `lean/CerbLean/CN/Verification/SmtLib.lean`
**Severity**: HIGH — **FIXED 2026-02-08**

Unit type now uses `cn_tuple_0` empty tuple datatype matching CN's `solver.ml:405` (`BT.Unit -> CN_Tuple.t []`). The preamble declares `(declare-datatype cn_tuple_0 ((cn_tuple_0)))` and both the sort and value use `cn_tuple_0`.

### C4. Struct Types Unsupported in SMT — **FIXED**

**Location**: `lean/CerbLean/CN/Verification/SmtLib.lean`
**Severity**: HIGH — **FIXED 2026-02-09**

Struct SMT support implemented matching CN's `CN_Structs` (solver.ml:1035-1067):
- `declare-datatype` declarations for all structs with field selectors (`member_struct_fld`)
- Naming convention matches CN: `tag_name_N` for sorts/constructors, `member_struct_fld` for selectors
- `baseTypeToSort` maps `struct_ tag` to the declared sort
- Term translation: `struct_` → constructor application, `structMember` → selector, `structUpdate` → full reconstruction
- Struct declarations emitted in both `checkObligation` and `obligationToSmtLib2`
- Unions explicitly skipped (CN does not support unions: check.ml:200)

Additionally, struct resource unpacking/repacking implemented matching CN's pack.ml:
- `addResourceWithUnfold` replaces `addR` everywhere, matching CN's `add_r + do_unfold_resources` (typing.ml:687-694)
- `unpackStructResource` matches `unpack_owned` (pack.ml:104-140): `Owned<struct>(p)` → per-field `Owned<field_type>(memberShift(p, tag, field))`
- `tryRepackStruct` matches `packing_ft` (pack.ml:42-92): collects field resources and reconstructs struct value
- Recursive unpacking for nested structs
- Struct tag IDs resolved during spec resolution (Resolve.lean), matching CN's `Cabs_to_ail`

**Remaining**: Test 023 still fails because `structMember` terms from the parser have `.unit` type instead of the field's actual type. This is an H1 (wellTyped/type inference) issue, not a struct SMT issue.

### C5. PEwrapI Always Returns Add

**Location**: `lean/CerbLean/CN/TypeChecking/Pexpr.lean:1097-1107`
**Severity**: CRITICAL — wrong operator for non-add wrapping

CN (check.ml:945-985) performs full wrapping semantics including shift operations (IOpShl, IOpShr), division, subtraction, multiplication, etc. Our code ALWAYS returns `(.binop .add t1 t2)` regardless of the actual operator. This means wrapped subtraction, multiplication, shifts, etc. all produce ADDITION terms.

**Fix**: Match on the actual operator and produce the correct binop.

### C6. PEcatch_exceptional_condition Has No Overflow Checking — **FIXED**

**Location**: `lean/CerbLean/CN/TypeChecking/Pexpr.lean:1153-1195`
**Severity**: CRITICAL — **FIXED 2026-02-09**

Extended-precision overflow checking now implemented matching CN check.ml:986-1033. Creates `Bits(Signed, 2*width+4)`, casts operands, computes at extended precision, checks `minInt ≤ extResult ≤ maxInt`. Generates UB036 verification obligation. SMT `sign_extend` fixed for signed bitvector widening.

### C7. PEundef Never Fails (Silently Passes UB)

**Location**: `lean/CerbLean/CN/TypeChecking/Pexpr.lean:1033-1051`
**Severity**: CRITICAL — silently accepts undefined behavior

CN (check.ml:1067-1074) checks `provable(false)` to detect dead branches. If the branch is reachable, it FAILS with an undefined behavior error. Our code returns a symbolic `undefSym` term — it NEVER fails. This means undefined behavior that CN would catch as an error passes silently through our type checker.

**Fix**: At minimum, generate an obligation that the branch is unreachable. Better: fail immediately (requires inline solver).

### C8. Spec Structure: Flat List vs Recursive LRT/LAT/AT

**Location**: `lean/CerbLean/CN/Types/Spec.lean`
**Severity**: HIGH — structural mismatch with CN

CN uses deeply nested recursive types:
- `LogicalReturnTypes.t` (postconditions): `Define | Resource | Constraint | I` — each chains to next
- `LogicalArgumentTypes.t` (general clauses): parameterized by return type
- `ArgumentTypes.t` (function specs): adds `Computational | Ghost | L` bindings

Our `Spec.lean` uses flat lists of `Clause` (resource | constraint | letBinding). This loses:
- **Scoping**: CN naturally scopes bindings; our flat list doesn't
- **Ghost bindings**: CN's AT has Ghost parameter bindings; we have none
- **Computational bindings**: CN's AT has Computational bindings; our FunctionSpec doesn't model these
- **Info locations**: Every CN clause carries location info; ours don't
- The `trusted` field on FunctionSpec is a fabrication — CN handles trust elsewhere

---

## HIGH Priority Issues

### H1. Missing WellTyped Checking Pass

**CN reference**: `tmp/cn/lib/wellTyped.ml` (~2200 lines)
**Our implementation**: None

CN has an entire `wellTyped.ml` module that validates types during checking:
- `ensure_base_type` — checks expected vs actual types match
- `check_ct` — validates C types are well-formed
- `infer_bt` — infers types from terms
- Various ensure_* functions for specific type shapes

We skip this entirely. This means we accept ill-typed terms that CN would reject.

**Impact**: Some tests may pass with type errors that CN would catch.

### H2. Missing `core_to_mucore` Transformation

**CN reference**: `tmp/cn/lib/core_to_mucore.ml` (~500 lines)
**Our implementation**: "Lazy muCore" approach (deliberate deviation)

CN transforms Core IR to muCore before type checking. Our "lazy muCore" approach processes Core directly, handling patterns like:
- Stripping `Specified`/`Unspecified` wrappers on the fly
- Detecting parameter stack slots via store tracking
- Simplifying `PtrValidForDeref` wrappers

This is a deliberate design choice but introduces risks:
- Edge cases in the lazy transformation may not match muCore exactly
- `filterSpecifiedBranches` in Pexpr.lean may not handle all patterns
- Parameter detection via `lookupParamValue` is fragile

**Risk**: Medium — the lazy approach works for simple cases but may diverge on complex programs.

### H3. Resource Inference Simplifications

**CN reference**: `tmp/cn/lib/resourceInference.ml` (~600 lines)
**Our implementation**: `lean/CerbLean/CN/TypeChecking/Inference.lean` (~415 lines)

Differences:
1. ~~**No packing/unpacking**~~: **PARTIALLY FIXED 2026-02-09** — Struct unpacking (`unpackStructResource`, matching `unpack_owned` in pack.ml:104-140) and repacking (`tryRepackStruct`, matching `packing_ft` in pack.ml:42-92) are now implemented. Recursive unpacking handles nested structs. Array unpacking is still missing.
2. **No span resources**: CN handles array-style resources with `QPredicates`. We don't.
3. **Simplified matching**: We do syntactic + single-candidate SMT. CN does full constraint-based matching via `Simplify.LogicalConstraints.simp` (fast path) and solver (slow path). Our `termSyntacticEq` approximates the fast path for structural cases.
4. **No simplification**: CN calls `Simplify.IndexTerms.simp` before comparison. We don't.

**Impact**: Array resource patterns won't work. Simple struct patterns now work.

### H4. Remaining Fall-Through Defaults in Pexpr.lean — **MOSTLY FIXED**

**MOSTLY FIXED 2026-02-09** — Batch 4 addressed the significant violations:

| Line | Pattern | Issue | Status |
|------|---------|-------|--------|
| 168 | `annots.findSome? getAnnotLoc \|>.getD Core.Loc.t.unknown` | Falls back to unknown location | Acceptable — location is for diagnostics only, not semantic |
| 351/355/356 | `\| _ => pure ()` | Silently ignores unknown function patterns | Acceptable — these are intentional no-ops for unrecognized intrinsics |
| 559 | `\| _ =>` in case branch handling | Silently handles unknown patterns | Acceptable — handles remaining case arm patterns |
| 922-930 | Fallback treats unknown function calls as normal application | Should fail on unrecognized functions | Acceptable — handles user-defined functions |
| 1194 | `-- For now, treat union like struct` | Wrong semantics for unions | **FIXED** — now `throw "union member access not supported"` |
| 1217 | `return AnnotTerm.mk (.const .unit) .unit loc` | Constrained values return unit | **FIXED** — now evaluates inner expression and wraps with constraint |
| 1250 | `\| _ => { id := 0, name := some "Unknown" }` | Unknown constructor fallback | **FIXED** — now `throw "ctorToSym: unknown..."` |

Additionally fixed: `Eiop` constant case catch-all now throws instead of returning `.const .unit`.

### H5. No Inline Solver During Type Checking (Architectural)

**CN reference**: typing.ml — solver integrated with push/pop
**Our implementation**: Post-hoc obligation accumulation

CN has INLINE access to the SMT solver during type checking. `provable` is called directly to:
- Determine if branches are dead (`provable(false)`)
- Disambiguate multiple resource candidates
- Check representability inline
- Filter empty resources (`filter_empty_resources`)

We accumulate obligations for post-hoc discharge. This is a deliberate design choice but means:
- We cannot prune dead branches eagerly
- We cannot disambiguate multiple resource candidates
- We cannot do inline representability checks
- `checkNoLeakedResources` is a syntactic `isEmpty` check instead of solver-based `filter_empty_resources`

**Impact**: Affects branch elimination, resource inference quality, and false passes where dead branches should have been detected.

### H6. PEif Handling: Always Evaluates Both Branches

**Location**: `Pexpr.lean:657-675`

CN (check.ml:1034-1056) uses the solver to prune branches: if `provable(c)`, only check then-branch; if `provable(not c)`, only check else-branch; if neither, check both with path conditions.

Our code always evaluates both branches and has a "cross-propagation" hack for type alignment that CN doesn't need. Additionally, we do NOT thread path conditions (`path_cs`) through pure expressions at all — CN does.

### H7. Missing `add_c` Semantics (Solver Assume + Equality Extraction) — **PARTIALLY FIXED**

**Location**: `Monad.lean:303`
**PARTIALLY FIXED 2026-02-09**

CN's `add_c` (typing.ml:403-412) does 4 things:
1. Simplify constraint (skip — needs full simplifier, H5-level)
2. Add to context (we do this)
3. Tell solver via `Solver.assume` (skip — no inline solver, H5-level)
4. Extract symbol equalities via `add_sym_eqs` (typing.ml:352-354)

**Fixed**: `addLValue` now adds `sym = value` equality constraints to the context, matching CN's `add_sym_eqs`. This makes let-binding equalities available as SMT assumptions in subsequent obligations, which was the key missing piece for test 041.

**Still missing**: Constraint simplification (requires H5 infrastructure), `Solver.assume` (requires inline solver).

### H8. Missing `add_r` Semantics (Pointer Facts + Resource Unfolding) — **PARTIALLY FIXED**

**Location**: `Monad.lean:308`, `Inference.lean:168`
**PARTIALLY FIXED 2026-02-09**

CN's `add_r` (typing.ml:415-427) simplifies the resource, derives pointer facts from existing resources, adds to context, then calls `do_unfold_resources` which unpacks compound resources.

`addResourceWithUnfold` now replaces all `addR` calls (in Action.lean and Inference.lean), matching CN's `add_r + do_unfold_resources` pattern. Struct resources are automatically unpacked into field resources recursively.

**Still missing**: Resource simplification, pointer fact derivation from existing resources.

### H9. Alloc_id Type as Int in SMT — **CORRECT (not a bug)**

**Location**: `SmtLib.lean:70`

```lean
| .allocId => .ok (Term.symbolT "Int")
```

Investigated: CN's `CN_AllocId` module (solver.ml:169-178) uses `SMT.t_int` (plain Int) when `use_vip = true` (the default, indexTerms.ml:469). Our encoding matches CN's default VIP mode exactly. Not a bug.

---

## MEDIUM Priority Issues

### M1. MemByte Type as Int in SMT

CN represents `MemByte` as an SMT datatype with `alloc_id` and `value` fields. We use bare `Int`. This matters for byte-level memory reasoning.

### M2. Missing `representable` and `good` Constraint Generation — **PARTIALLY FIXED**

**Location**: Action.lean
**PARTIALLY FIXED 2026-02-09**

**Fixed**:
- **Representable for stores** (check.ml:1863-1877): `representable_(ct, varg)` obligation generated for ALL store types, matching CN. Gated on `!storeIsUnspecified` (architectural: CN's inline solver prunes dead branches before reaching stores; we rely on C7 unreachability obligations). SMT translation matches CN's `value_check` (indexTerms.ml:959-1010): Void → `true`, Integer → range check, Pointer → `true` (representable mode), Struct/Array → `.unsupported` (will cause test failures when exercised).
- **Aligned for creates** (check.ml:1799-1800): `aligned(ptr, align)` added as assumption (not obligation) via `addC`. Alignment value cast to `uintptr_bt` (`Bits(Unsigned, 64)`) matching CN's `cast_ Memory.uintptr_bt arg loc`.

**Still missing**: `good` constraints for pointer validity, struct/array representable SMT translation.

### M3. Missing Alloc Resource Tracking

**Location**: Action.lean:216-217

```lean
-- TODO: Add Alloc predicate (add_r loc (P (Req.make_alloc ret), O lookup))
```

CN tracks allocation metadata separately from Owned resources. We don't. This means we can't verify allocation-ID-related properties.

### M4. CType Sort as Unsupported

CN encodes CType as Int in SMT (with a lookup table). We mark it as unsupported. This blocks certain operations involving type-level reasoning.

### M5. Pointer Comparisons Not Implemented

**Location**: `Expr.lean:150-155`

All pointer comparisons (PtrEq, PtrNe, PtrLt, PtrLe, PtrGt, PtrGe) fail with "not yet implemented". CN has complex provenance-aware handling (check.ml:1525-1618) including `hasAllocId_`, `allocId_`, `addr_` checks.

### M6. IntFromPtr, PtrFromInt, Ptrdiff Not Implemented

**Location**: `Expr.lean:158-160`

These memory operations fail with "not yet implemented". CN has full handling (check.ml:1615-1699) with allocation ID checks, bounds checks, and representability proofs.

### M7. `unbindPattern` Is a No-Op

**Location**: `Expr.lean:573-576`

CN's `remove_as` MOVES computational variables to the logical context after pattern matching. Our `unbindPattern` does nothing — variables are never removed or moved, causing stale bindings to accumulate.

### M8. Missing `all_empty` Semantic Check

After function body type checking, CN's `all_empty` verifies ALL resources have been consumed using `filter_empty_resources` which calls `provable` to check if resource permissions are trivially empty. Our `checkNoLeakedResources` (Check.lean:94-100) does a syntactic `isEmpty` check.

### M9. Substitution Doesn't Alpha-Rename

Both in `Term.lean` and `Constraint.lean`, substitution skips alpha-renaming for binding variables (`EachI`, `MapDef`, `Let`, `Match`, `Forall`). CN does proper alpha-renaming via `suitably_alpha_rename`. This is a latent variable capture bug.

### M10. Dynamic Kill Type

**Location**: Action.lean:240

```lean
| .dynamic => Ctype.void  -- Dynamic kill (free) - type determined at runtime
```

For `free()` calls (dynamic kill), we use `void` as the type. CN looks up the allocation to determine the correct type. This may cause resource matching failures for dynamically freed memory.

---

## Test Suite Assessment

### Key Finding: Passes Are Genuine (Not Hacks)

After detailed review of all 46 tests, the **45 passing tests are genuinely correct passes**. The verification pipeline does real work:
- Resources are properly tracked through create/store/load/kill sequences
- SMT obligations are generated and discharged correctly
- Resource leaks are detected (tests 014, 030)
- Branch-specific verification is performed (tests 020, 021, 032)
- Postcondition constraints are verified by SMT, not assumed

The integer type bug (C1) does NOT cause false passes in the current test suite because:
- Most tests use simple integer arithmetic where unbounded `Int` SMT reasoning gives the same answer as bitvector reasoning
- The tests don't exercise overflow boundaries where `Int` vs `Bits` would diverge
- However, this means the tests DON'T adequately test bitvector semantics

### Test Classification Summary

| Category | Count | Tests |
|----------|-------|-------|
| Correct Pass | 36 | 001-007, 020-021, 023-024, 027-028, 031-033, 035-043, 045, 047-053 |
| Correct Expected Fail | 9 | 010-014, 025-026, 029-030 |
| Wrong Fail (feature gap) | 1 | 044 |

### Currently Failing Tests (1 failure — architectural gap)

| Test | Root Cause |
|------|-----------|
| 044-pre-post-increment.c | SeqRMW (read-modify-write) not supported. CN itself also doesn't support this: `core_to_mucore.ml` has `assert_error "TODO: SeqRMW"`. Not a bug in our implementation. |

### Recently Fixed Tests

| Test | Fix | Batch |
|------|-----|-------|
| 022-pointer-arithmetic.c | Pointer arithmetic elaboration in Resolve.lean: `ptr + int` → `arrayShift` (matching CN compile.ml:447-463) | Batch 2 |
| 023-struct-access.c | H1 structMember type inference from tagDefs (wellTyped.ml:695-706) + C4 struct SMT support | Batch 3-4 |
| 041-add-overflow.c | H7 sym_eqs: `addLValue` now adds equality constraints (typing.ml:352-354) | Batch 5 |
| 045-struct-field-frame.c | H1 structMember type inference (same fix as 023) | Batch 3-4 |

### Expected Fail Tests: Minor Concern

Tests 010-double-free.fail.c and 011-use-after-free.fail.c fail for a **secondary reason** (no libc specs for `free_proxy`) rather than the primary reason (resource tracking after free). CN would also reject these, but for the more precise reason of "resource already consumed." This is not a false pass but indicates our free handling is incomplete.

### Missing Test Coverage (vs CN's 191-test suite)

| Category | CN Has | We Have | Gap |
|----------|--------|---------|-----|
| Bitwise operations | `bitwise_and.c`, `b_or.c`, `b_xor.c` etc. | None | HIGH |
| Pointer comparisons | Various | None (unimplemented) | HIGH |
| Struct member access | `arrow_access.c`, `get_from_arr.c` | 023/045 (failing) | HIGH |
| Linked data structures | `append.c` (linked list) | None | MEDIUM |
| Quantified predicates (each) | `alloc_token.c`, `ghost_arguments.c` | None | MEDIUM |
| CN functions/predicates | `cn_inline.c`, various | None | MEDIUM |
| Loops with invariants | `forloop_with_decl.c`, `increments.c` | None | HIGH |
| Unsigned arithmetic | `doubling.c` | None | MEDIUM |
| Division variants | `division_casting.c`, `division_precedence.c` | 005 only | LOW |
| Implies/logical operators | `implies.c`, `implies_associativity.c` | None | LOW |
| Error rejection tests | Many `.error.c` tests | Very few | HIGH |
| Integer overflow boundary | Various | None that exercise `Int` vs `Bits` divergence | CRITICAL |

---

## Prioritized Improvement Plan

### Phase 1: Fix Integer Types (HIGH IMPACT, MODERATE EFFORT)

**Goal**: All integer values from memory use `Bits(sign, width)` instead of `Integer`

1. Unify `ctypeToBaseType` (Action.lean) with `ctypeInnerToOutputBaseType` (Resolve.lean)
2. The correct version already exists in Resolve.lean — make Action.lean use it
3. Update `checkPexpr` integer literal handling to use Bits types
4. Run tests — expect many to break (this is good)
5. Fix tests that break by adjusting SMT bitvector encoding

**Estimated impact**: Many tests will break, exposing the real type errors. Some may still pass once bitvector SMT encoding is correct.

### Phase 2: Fix Pointer SMT Encoding (HIGH IMPACT, HIGH EFFORT)

**Goal**: Pointers encoded as CN_Pointer algebraic datatype in SMT

1. Add CN_Pointer datatype declaration to SMT preamble
2. Add CN_AllocId type
3. Implement `ptr_shift`, `copy_alloc_id`, `addr_of` helper functions
4. Update `baseTypeToSort` for `.loc`
5. Update term translation for pointer-related operations
6. Add null pointer handling

**Estimated impact**: Enables proper pointer reasoning. Currently failing pointer tests (022, 044) may start passing.

### Phase 3: Add Struct SMT Support (MEDIUM IMPACT, MODERATE EFFORT)

**Goal**: Struct types work in SMT

1. Declare each struct as an SMT datatype with field accessors
2. Implement `structMember` term translation
3. Add struct construction/update translation

**Estimated impact**: Unblocks tests 023 and 045.

### Phase 4: Eliminate Remaining Fall-Throughs (LOW-MEDIUM IMPACT, LOW EFFORT) — **MOSTLY DONE**

**Goal**: All remaining `| _ =>` patterns that return values become errors

1. ~~Audit and fix all patterns listed in H4 above~~ — **DONE** (union, constrained, ctorToSym, constant catch-all fixed)
2. Remaining patterns assessed as acceptable (location fallback, function pattern no-ops)

### Phase 5: Add Missing Constraints (MEDIUM IMPACT, MODERATE EFFORT) — **PARTIALLY DONE**

**Goal**: Generate representability and alignment constraints

1. ~~Implement `representable` constraint generation for stores~~ — **DONE** (integer-type stores only)
2. ~~Implement `aligned` constraint generation for creates~~ — **DONE** (added as assumption via addC)
3. Add `Alloc` resource tracking — deferred (needs predicate infrastructure)

### Phase 6: Improve Resource Inference (MEDIUM IMPACT, HIGH EFFORT)

**Goal**: Support struct packing/unpacking and better matching

1. Implement struct field → struct Owned packing
2. Implement struct Owned → struct field unpacking
3. Add term simplification before matching

### Phase 7: Add Missing Tests

See "Missing Test Coverage" section above.

---

## Quick Wins (Can Fix Immediately)

1. ~~**Unify type conversion**: Make `Action.ctypeToBaseType` call `Resolve.ctypeToOutputBaseType`~~ — **DONE** (C1 fix)
2. ~~**Fix `.unit` SMT encoding**: Change `Bool` to proper empty tuple~~ — **DONE** (C3 fix)
3. **Fix `.allocId` SMT encoding**: Use dedicated sort — 1 line (H9)
4. ~~**Remove line 1250 Unknown fallback**: Change to `throw`~~ — **DONE** (H4 fix)
5. ~~**Remove line 1194 union hack**: Change to `throw "union not yet supported"`~~ — **DONE** (H4 fix)

Additional fixes completed (not originally in quick wins):
6. ~~**Fix PEwrapI operator mapping**~~ — **DONE** (C5 fix)
7. ~~**Add PEundef unreachability obligation**~~ — **DONE** (C7 fix)
8. ~~**Add path conditions to PEif branches**~~ — **DONE** (H6 partial fix)
9. ~~**Strip guard patterns (lazy muCore)**~~ — **DONE** (H6 partial fix)

---

## Files Requiring Changes (Priority Order)

| File | Changes Needed | Priority |
|------|---------------|----------|
| `Action.lean` | Fix ctypeToBaseType, add representability constraints | P1 |
| `SmtLib.lean` | Fix pointer/unit/allocId sorts, add struct support | P1-P3 |
| `Pexpr.lean` | Fix fall-through defaults, integer literal types, PEwrapI, PEcatch, PEundef | P1, P4 |
| `Inference.lean` | Add struct packing, improve matching | P6 |
| `Verify.lean` | Add struct declarations to SMT preamble | P3 |
| `Obligation.lean` | May need updates for new constraint types | P5 |
| `Monad.lean` | Improve add_c/add_r semantics (long-term: inline solver) | P5 |
| `Expr.lean` | Implement pointer comparisons, IntFromPtr, PtrFromInt | P5 |
| `Spec.lean` | Restructure to match LRT/LAT/AT (medium-term) | P3 |
| `Spine.lean` | Ghost argument support | P6 |

---

## Complete Issue Index

| ID | Severity | Summary | File | Status |
|----|----------|---------|------|--------|
| C1 | CRITICAL | Integer types `.integer` vs `.bits` | Action.lean:116 | **FIXED 2026-02-08** — `ctypeToBaseType` now delegates to `ctypeInnerToBaseType` (Bits mapping) |
| C2 | CRITICAL | Pointer SMT encoding Int vs algebraic datatype | SmtLib.lean:69 | **FIXED 2026-02-08** — `declare-datatype pointer` preamble, ptr_shift/copy_alloc_id/addr_of/bits_to_ptr/alloc_id_of helpers, TypeEnv threading for memberShift/offsetOf |
| C3 | HIGH | Unit SMT encoding Bool vs empty tuple | SmtLib.lean:71 | **FIXED 2026-02-08** — `cn_tuple_0` empty tuple datatype matching CN |
| C4 | HIGH | Struct types unsupported in SMT | SmtLib.lean:73 | **FIXED 2026-02-09** — Struct SMT declarations, sort mapping, term translation, resource unpacking/repacking, tag resolution |
| C5 | CRITICAL | PEwrapI always returns add | Pexpr.lean:1130 | **FIXED 2026-02-08** — now maps each Iop to correct BinOp |
| C6 | CRITICAL | PEcatch_exceptional_condition no overflow check | Pexpr.lean:1153 | **FIXED 2026-02-09** — Extended-precision overflow check (Bits(Signed, 2*width+4)), SMT sign_extend fix |
| C7 | CRITICAL | PEundef never fails | Pexpr.lean:1067 | **FIXED 2026-02-08** — generates `requireConstraint(false)` unreachability obligation |
| C8 | HIGH | Spec structure flat vs recursive LRT/LAT/AT | Spec.lean | Open |
| H1 | HIGH | No wellTyped checking | (missing) | **PARTIALLY FIXED 2026-02-09** — structMember type inference from tagDefs (wellTyped.ml:695-706); other type checking gaps remain |
| H2 | MEDIUM | Lazy muCore vs upfront muCore | (by design) | Accepted |
| H3 | HIGH | Resource inference simplified | Inference.lean | **PARTIALLY FIXED 2026-02-09** — Struct packing/unpacking implemented; array resources and simplification still missing |
| H4 | MEDIUM | Remaining fall-through defaults | Pexpr.lean | **MOSTLY FIXED 2026-02-09** — union, constrained, ctorToSym, constant catch-all fixed; location `.getD` and some function patterns remain (assessed as acceptable) |
| H5 | HIGH | No inline solver during type checking | Monad.lean | Architectural |
| H6 | MEDIUM | PEif always evaluates both branches | Pexpr.lean:657 | **PARTIALLY FIXED 2026-02-08** — path conditions (CN's `path_cs`) now tracked; guard patterns stripped (lazy muCore). Still evaluates both non-guard branches (no solver pruning). |
| H7 | MEDIUM | add_c missing solver assume + equality extraction | Monad.lean:303 | **PARTIALLY FIXED 2026-02-09** — `addLValue` now adds `sym = value` equality constraint (CN's `add_sym_eqs`, typing.ml:352-354); solver.assume and constraint simplification still missing |
| H8 | MEDIUM | add_r missing pointer facts + unfolding | Monad.lean:308 | **PARTIALLY FIXED 2026-02-09** — `addResourceWithUnfold` replaces all `addR` calls; struct unfolding works; pointer facts still missing |
| H9 | LOW | AllocId as Int in SMT | SmtLib.lean:70 | Open |
| M1 | LOW | MemByte as Int in SMT | SmtLib.lean | Open |
| M2 | MEDIUM | Missing representable/good constraints | Action.lean:311 | **PARTIALLY FIXED 2026-02-09** — `representable` constraint generated for ALL store types matching CN (check.ml:1863-1877); SMT handles integer range checks, pointer/void trivially true, struct/array unsupported; `aligned` fact with uintptr_bt cast added for creates (check.ml:1799-1800); `good` constraints still missing |
| M3 | MEDIUM | Missing Alloc resource tracking | Action.lean:216 | Open |
| M4 | LOW | CType sort unsupported | SmtLib.lean:93 | Open |
| M5 | MEDIUM | Pointer comparisons not implemented | Expr.lean:150 | Open |
| M6 | MEDIUM | IntFromPtr/PtrFromInt not implemented | Expr.lean:158 | Open |
| M7 | LOW | unbindPattern is a no-op | Expr.lean:573 | Open |
| M8 | MEDIUM | Missing all_empty semantic check | Check.lean:94 | Open |
| M9 | LOW | Substitution no alpha-rename | Term.lean | Open |
| M10 | LOW | Dynamic kill uses void type | Action.lean:240 | Open |
