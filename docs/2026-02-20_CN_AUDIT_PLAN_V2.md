# CN Comprehensive Audit & Alignment Plan — Phase 2

## Context

This is the second comprehensive audit of our Lean CN implementation against the original CN OCaml implementation. The first audit (2026-02-18) established the initial plan with Waves 0-3. Waves 0-2 are complete, Wave 3 is complete. Current state: **88/90 tests passing (97%)**.

This audit was conducted by 7 parallel agents examining:
1. `check.ml` vs Check/Expr/Action/Pexpr.lean
2. `resourceInference.ml` + `pack.ml` vs Inference.lean
3. `solver.ml` vs SmtLib/SmtSolver.lean
4. `core_to_mucore.ml` + `compile.ml` vs Resolve/Params/Parser.lean
5. CN's own test suite (191 tests) vs our 90 tests
6. JSON pipeline + type definitions
7. `simplify.ml` + `context.ml` + `typing.ml` vs supporting infrastructure

**Goal**: Close all remaining gaps to match CN's verification capability for the predicate-free fragment.

**Scope**: Built-in Owned/Block resources, function specs, loop invariants, ghost variables/statements, array ownership, pointer operations, SMT-based constraint solving. **Excluded**: User-defined predicates, logical functions, lemmas, datatypes, type synonyms, Coq export.

---

## Current Status (2026-02-20)

| Suite | Pass | Fail | Total |
|-------|------|------|-------|
| Unit tests | 19 | 0 | 19 |
| Integration (nolibc) | 88 | 2 | 90 |

**2 Failing tests**:
- `044-pre-post-increment.c`: Cerberus generates Load+Store (not SeqRMW) for `*p += 1`. The Loaded value references a consumed resource.
- `097-ghost-extract.c`: `extract` ghost statement requires QPredicate instantiation at specific index.

**15 DIVERGES-FROM-CN markers** across codebase.
**0 FIXME markers**.

---

## Audit Findings Summary

### A. Bugs Found

1. **SMT Rational Constant Encoding (SmtLib.lean:453)**: `Q(num,denom)` encoded as string literal `"num/denom"` instead of SMT `/` operator. Should be `(/ num denom)`. No current test exercises this path.

### B. Critical Gaps (Affect Correctness)

1. **`representable`/`good` incomplete** (SmtLib.lean:737-771): Only integer range checks implemented. CN expands these recursively for struct/array/pointer types via `indexTerms.ml`. Programs using `good(ct, val)` in specs for non-integer types get `.unsupported`.

2. **QPredicate handling severely simplified** (Inference.lean:522-547): Our stub does name/step/pointer matching and full consumption. CN's algorithm (resourceInference.ml:253-375) includes alpha-renaming, permission intersection analysis, partial consumption with remainder, movable indices, and individual element extraction.

3. **No `do_unfold_resources` iteration** (typing.ml:548-657): CN iterates unpacking until fixpoint. We unpack once on `addR`. Nested struct unpacking only goes one level.

4. **Alpha-renaming incomplete**: `LogicalConstraint.subst` and `LAT.subst` don't alpha-rename on variable capture. Marked DIVERGES-FROM-CN.

### C. Missing Features (In-Scope)

**Pointer operations** (check.ml:1597-1763):
- PtrLt, PtrGt, PtrLe, PtrGe — require `check_both_eq_alloc` + `check_live_alloc_bounds`
- Ptrdiff — pointer subtraction
- PtrFromInt — integer to pointer cast
- CopyAllocId — provenance transfer

**SMT encodings** (solver.ml):
- CLZ/CTZ/FFS/FLS unary ops — bit-counting recursion
- CType constants via CTypeMap
- Default values — `cn_val(cn_none(...))`
- Exp for constant exponents — `Z.pow z1 z2`
- Record terms — should desugar to tuples

**Translation pipeline** (compile.ml):
- Evaluation scopes (`@start`, `@old`, `unchanged`) — scope stacking not implemented
- `CNExpr_match` — pattern matching in annotations
- `CNExpr_deref` — pointer dereference with evaluation scope

**Simplification** (simplify.ml):
- Rational (Q) constant arithmetic
- Integer comparison algebraic simplification (`simp_int_comp`)
- Rem/Mod + LE special case (`x % n <= n-1` → `true`)

**Resource inference** (pack.ml):
- `extractable_one`/`extractable_multiple` — individual array element extraction
- `cases_to_map` — merging partial QPredicate fragments
- `resource_empty` — removing provably-empty remainders
- Padding resources in struct unpack/repack

### D. Test Coverage Gaps

- **Passing tests**: 100% coverage of CN's predicate-free passing tests
- **Error tests**: Only 31.8% coverage (21/66 in-scope error tests)
- Missing categories: ghost param validation errors (8), pointer type safety (16), bitwise type errors (3), spec format errors (6), arithmetic type errors (6)

---

## Execution Plan

### Wave 4: Bug Fixes & Critical Correctness (Parallel)

All packages touch different files. Target: fix the 2 remaining test failures and known bugs.

#### WP-4A: Fix Test 044 (Load+Store RMW Pattern)
**Files**: `CN/TypeChecking/Action.lean`, `CN/TypeChecking/Expr.lean`
**Problem**: Cerberus generates Load+Store (not SeqRMW) for `*p += 1` when compiled without optimization. The Store's value expression references the Load result, but the Load consumes the Owned resource. The subsequent Store can't find the resource.
**Fix approach**:
- In the Load handler, when the loaded value is immediately used in a Store to the same pointer, the resource should be kept available (or the Load result should be tracked as a "pending" value that the Store can consume).
- Investigate CN's handling: CN sees this as a muCore `M_CN_progs` sequence, not Load+Store. Our lazy muCore approach needs to handle this Core pattern.
- Alternative: detect the `let v = Load(p); Store(p, f(v))` pattern in Esseq and handle as atomic RMW.
**CN ref**: check.ml:1892-1898 (Load), check.ml:1847-1891 (Store)

#### WP-4B: Fix Test 097 (Ghost Extract)
**Files**: `CN/TypeChecking/GhostStatement.lean`, `CN/TypeChecking/Inference.lean`
**Problem**: `extract Owned<int>(p + i*4i64)` requires instantiating a QPredicate at a specific index, extracting the element, and producing a regular Owned resource.
**Fix approach**:
- Implement `handleExtract` in GhostStatement.lean: parse the resource expression, compute the pointer, call resource inference to find a matching QPredicate
- In Inference.lean, add `extractFromQPredicate`: given a QPredicate and a concrete index, extract the element as a regular Predicate resource and update the QPredicate's permission to exclude that index
- This is a simplified version of CN's `extractable_one` (pack.ml:155-191) + qpredicate partial consumption
**CN ref**: check.ml:2227-2246 (extract handler), pack.ml:155-191 (extractable_one)

#### WP-4C: Fix Rational Constant SMT Bug
**Files**: `CN/Verification/SmtLib.lean`
**Problem**: Line 453 encodes `Q(num, denom)` as `literalT "num/denom"` string. Should be `mkApp2 (symbolT "/") (literalT num) (literalT denom)`.
**Fix**: Single-line change.

#### WP-4D: Simplification Improvements
**Files**: `CN/TypeChecking/Simplify.lean`
**Tasks**:
1. Add Q constant arithmetic (Add, Sub, Negate for rationals)
2. Add Rem/Mod + LE special case (`x % n <= n-1` → `true` when `n > 0`)
**CN ref**: simplify.ml:232-233, 249-250, 334-343, 418

---

### Wave 5: Pointer Operations & SMT Completeness (Parallel)

#### WP-5A: Ordered Pointer Comparisons
**Files**: `CN/TypeChecking/Expr.lean`
**Tasks**: Implement PtrLt, PtrGt, PtrLe, PtrGe
**Approach**:
- Require both pointers have same allocation ID (`check_both_eq_alloc`)
- Compare addresses as bitvectors
- Generate constraint: `allocId(p1) == allocId(p2)` (same provenance)
- Result: `addr(p1) < addr(p2)` (or <=, >, >=)
**CN ref**: check.ml:1597-1614

#### WP-5B: Remaining Pointer Memops
**Files**: `CN/TypeChecking/Expr.lean`
**Tasks**:
1. `Ptrdiff` — require same alloc, compute `(addr(p1) - addr(p2)) / sizeof(elem_type)`
2. `PtrFromInt` — create fresh pointer with integer address, add representability constraint
3. `CopyAllocId` — create pointer with alloc_id from one pointer, address from another
**CN ref**: check.ml:1615-1763

#### WP-5C: SMT Term Completeness
**Files**: `CN/Verification/SmtLib.lean`
**Tasks**:
1. CLZ/CTZ as recursive bit-counting (CN: solver.ml:572-613)
2. FFS/FLS desugared to CTZ/CLZ (CN: solver.ml:636-657)
3. CType constants via integer mapping (CN: solver.ml:1194-1199)
4. Default values as `cn_val(cn_none(...))` (CN: solver.ml:553)
5. Exp for constant exponents via `Z.pow` (CN: solver.ml:711-715)
6. Record terms → desugar to tuple construction
**CN ref**: solver.ml various (see line numbers above)

#### WP-5D: Representable & Good (Full Implementation)
**Files**: `CN/Verification/SmtLib.lean`, possibly new `CN/TypeChecking/WellTyped.lean`
**Tasks**: Implement full recursive `representable` and `good` checks matching CN's `indexTerms.ml`
- Integer: range check (already done)
- Pointer: `hasAllocId` or null
- Struct: recursively check each field
- Array: recursively check each element (via EachI)
- Bool: always true
**CN ref**: indexTerms.ml representable/good_value functions (~200 lines)

---

### Wave 6: Resource Inference Hardening (Sequential — depends on Wave 5)

#### WP-6A: do_unfold_resources Iteration
**Files**: `CN/TypeChecking/Monad.lean`, `CN/TypeChecking/Inference.lean`
**Tasks**:
1. Add `unfoldResources` function that iterates: scan resources, unpack structs/arrays, repeat until stable
2. Call from `addR` or at strategic points (before resource requests)
3. Track iteration count to prevent infinite loops
**CN ref**: typing.ml:548-657

#### WP-6B: QPredicate Improvements
**Files**: `CN/TypeChecking/Inference.lean`
**Tasks**:
1. Alpha-renaming in qpredicateRequest (rename found QPredicate's quantifier variable to match requested)
2. Permission intersection analysis (check if permissions overlap via SMT)
3. Partial consumption with remainder (update QPredicate permission after extraction)
4. Individual element extraction (`extractFromQPredicate` — needed for WP-4B but can be enhanced here)
**CN ref**: resourceInference.ml:253-375

#### WP-6C: Alpha-Renaming Fix
**Files**: `CN/Types/Constraint.lean`, `CN/Types/ArgumentTypes.lean`, `CN/Types/Term.lean`
**Tasks**:
1. Fix `LogicalConstraint.subst` to alpha-rename forall-bound variable on capture
2. Fix `LAT.subst` to alpha-rename bound variables when in substitution's relevant set
3. Use existing `suitablyAlphaRename` from Term.lean
**CN ref**: logicalArgumentTypes.ml:53-57 (suitably_alpha_rename)

#### WP-6D: Padding Resources (Optional)
**Files**: `CN/TypeChecking/Inference.lean`
**Tasks**: Add padding resource generation in struct unpack/repack
- Unpack: produce `Owned<char[N]>(Uninit)` at padding offsets
- Repack: request padding resources at expected offsets
- Would close 4 DIVERGES-FROM-CN markers
**CN ref**: pack.ml:113-124 (unpack), pack.ml:66-75 (repack)
**Note**: Only needed if tests require it. Currently internally consistent.

---

### Wave 7: Test Coverage & Validation (Parallel with later waves)

#### WP-7A: Port CN Error Tests
**Files**: `tests/cn/` (new test files)
**Tasks**: Port ~20-30 error tests from CN's test suite (`tmp/cn/tests/cn/`), focusing on:

**High priority** (ghost params + pointer safety):
- `ghost_arguments_too_few.error.c`, `ghost_arguments_too_many.error.c`, `ghost_arguments_type_mismatch.error.c`
- `ptr_eq_arg_checking.error.c`, `ptr_diff.error.c`, `ptr_relop.error.c`
- `unconstrained_ptr_eq.error.c`, `copy_alloc_id.error.c`
- `int_to_ptr.error.c`

**Medium priority** (type safety):
- `bitwise_and_type_left.error.c`, `bitwise_and_type_right.error.c`, `bitwise_compl_type.error.c`
- `array_shift_void.error.c`, `array_shift_mismatch.error.c`
- `division_return_sign.error.c`, `mod_return_sign.error.c`
- `spec_accesses.error.c`, `double_spec1.error.c`

**Low priority** (niche):
- `from_bytes.error.c`, `to_bytes.error.c`
- `implies2.error.c`, `implies3.error.c`
- `unsupported_union.error.c`

Use CN test naming convention: adapt CN filenames to our `NNN-description.fail.c` format.
Tests that require features we haven't implemented should be noted but not added yet.

#### WP-7B: Port CN Passing Tests
**Files**: `tests/cn/` (new test files)
**Tasks**: Cross-reference CN's passing tests and add any missing coverage:
- Focus on tests that exercise features we've implemented but don't test
- Especially: `has_alloc_id.c`, `ownership_at_negative_index.c`, `extract_verbose.c`
- Complex ghost parameter tests, multi-field struct tests

#### WP-7C: Spurious Pass Audit
**Tasks**: Verify existing passing tests aren't passing for wrong reasons:
- Tests with no annotations (trivially pass)
- Tests marked `trusted` (skip verification)
- Tests where our type checker is more permissive than CN's

---

### Wave 8: Advanced Features (Future — depends on Waves 5-6)

These are lower-priority items that complete the predicate-free fragment but aren't needed for current test coverage.

#### WP-8A: Evaluation Scopes
**Files**: `CN/TypeChecking/Monad.lean`, `CN/TypeChecking/Expr.lean`, `CN/Parser.lean`
**Tasks**: Implement `@start`, `@old`, `unchanged` evaluation scope support
- Add `evaluationScope : Option String` to TypingState
- When entering function body, snapshot initial state as "start" scope
- `@start{expr}` evaluates `expr` in the start scope
- `unchanged(expr)` compares current and start scope values
**CN ref**: compile.ml:984-1007, 1350-1385

#### WP-8B: Integer Comparison Algebraic Simplification
**Files**: `CN/TypeChecking/Simplify.lean`
**Tasks**: Implement `simp_int_comp` — decompose comparison into linear terms and cancel
- `(x + 2) < (x + 5)` → `2 < 5` → `true`
- Extract linear combination from both sides
- Cancel common terms
- Evaluate if resulting comparison is constant
**CN ref**: simplify.ml:99-143
**Note**: Performance optimization, not correctness issue. SMT solver handles these anyway.

#### WP-8C: Movable Indices
**Files**: `CN/TypeChecking/Monad.lean`, `CN/TypeChecking/Inference.lean`
**Tasks**: Track `movable_indices : List (ResourceName × IndexTerm)` in TypingState
- Populated when `extract` ghost statement binds an array index
- Used by qpredicateRequest to extract individual elements
**CN ref**: typing.ml:15, 399-401, 662-665

---

## Remaining Known Divergences

After all waves, these intentional divergences should remain:

| Divergence | Rationale | Keep? |
|-----------|-----------|-------|
| Hybrid inline+post-hoc solver | Architecturally clean | Yes |
| Lazy muCore transformation | Simpler than two AST types | Yes |
| `Loc` type parameter dropped | Matches CN BaseTypes.Unit | Yes |
| `ResourceName.owned` has `Option Ctype` | Pre-resolution state | Yes |
| `LCSet` as List | Duplicates harmless | Yes |
| No Coq export | Replaced by Lean proofs | Yes |
| No predicates/functions/lemmas | Will use Lean proof system | Yes |
| SeqRMW type checking | Extension for Core IR compat | Yes |
| Fresh solver per obligation | Simpler than persistent | Yes |
| PtrEq simplified ambiguous case | Sound, skips rare case | Yes |

---

## Execution Order & Dependencies

```
Wave 4 (Bug fixes — parallel, immediate)
  ├─ WP-4A: Fix test 044 (Load+Store RMW)
  ├─ WP-4B: Fix test 097 (ghost extract)
  ├─ WP-4C: Fix Q constant SMT bug
  └─ WP-4D: Simplification improvements

Wave 5 (Pointer ops + SMT — parallel, after Wave 4)
  ├─ WP-5A: Ordered pointer comparisons
  ├─ WP-5B: Remaining pointer memops
  ├─ WP-5C: SMT term completeness
  └─ WP-5D: Representable/good full

Wave 6 (Resource inference — sequential parts, after Wave 5)
  ├─ WP-6A: do_unfold_resources iteration
  ├─ WP-6B: QPredicate improvements
  ├─ WP-6C: Alpha-renaming fix
  └─ WP-6D: Padding resources (optional)

Wave 7 (Tests — parallel with Waves 5-6)
  ├─ WP-7A: Port CN error tests (~20-30)
  ├─ WP-7B: Port CN passing tests
  └─ WP-7C: Spurious pass audit

Wave 8 (Advanced — future, after Waves 5-6)
  ├─ WP-8A: Evaluation scopes
  ├─ WP-8B: Algebraic simplification
  └─ WP-8C: Movable indices
```

## Verification

After each wave:
1. `make lean` — build passes
2. `make test-cn-nolibc` — no regressions, new tests pass
3. `grep -r "DIVERGES-FROM-CN" lean/` — count should decrease
4. `grep -r "FIXME" lean/` — count should remain 0

**Target**: 90/90 tests passing after Wave 4; ~100+ tests after Wave 7.

---

## Estimated Effort

| Wave | Packages | Scope | Priority |
|------|----------|-------|----------|
| Wave 4 | 4 | ~300 lines changed | **Immediate** |
| Wave 5 | 4 | ~600 lines changed | **High** |
| Wave 6 | 4 | ~500 lines changed | **Medium** |
| Wave 7 | 3 | ~30 new test files | **High** |
| Wave 8 | 3 | ~400 lines changed | **Low** |

---

## Changelog

- **2026-02-20**: Phase 2 audit plan created. 7-agent parallel audit completed. Supersedes 2026-02-18 plan.
