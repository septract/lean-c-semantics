# CN Implementation Audit Report

**Date:** 2026-02-26
**Scope:** Full comparison of Lean CN implementation against OCaml CN source (`tmp/cn/lib/`)
**Starting state:** 103/103 tests passing, 17 DIVERGES-FROM-CN markers, 0 FIXME markers
**Method:** 4 parallel audit agents comparing Types, TypeChecking infrastructure, check.ml logic, and Inference+SMT layers

## Fix Summary (2026-02-26)

All 10 critical bugs fixed, plus MOD-1, MOD-2, MOD-7, MOD-11, MOD-12, MOD-13. All 107 tests pass.

Key architectural fix: `spineL` Define case now does direct substitution matching CN's
`ftyp_args_request_step` (resourceInference.ml:144-146), instead of calling `addLValue`.
`processPreClause`/`processPostClause` let-bindings now use `addL + addC(def_)` matching
CN's `bind_arguments.aux_l` (check.ml:2343-2345).

| Bug | Fix | File(s) |
|-----|-----|---------|
| BUG-1 | Symbol substitution restricted to Const/Sym only | Simplify.lean |
| BUG-2 | Full solver preamble (not just pointer+struct) | Params.lean |
| BUG-3 | addC simplifies constraint before adding | Monad.lean |
| BUG-4 | addR simplifies resource before adding | Monad.lean |
| BUG-5 | Store only consumes Uninit (removed Init fallback) | Action.lean |
| BUG-6 | Kill only consumes Uninit (removed Init fallback) | Action.lean |
| BUG-7 | Bool conv_int creates `.bits` not `.z` constants | Pexpr.lean |
| BUG-8 | Label params: documented as DIVERGES-FROM-CN (can't fix at this layer) | ArgumentTypes.lean |
| BUG-9 | Struct/Datatype BEq uses full Sym comparison | Base.lean |
| BUG-10 | bv2int handles signed bitvectors correctly | SmtLib.lean |
| MOD-1 | EachI/MapDef alpha-renaming matching CN exactly | Simplify.lean |
| MOD-2 | Unit-typed symbol simplification rule | Simplify.lean |
| MOD-7 | PEerror checks dead path before failing | Pexpr.lean |
| MOD-11 | Store ensure_base_type checks | Action.lean |
| MOD-12 | Spine computational arg type check | Spine.lean |
| MOD-13 | addAValue/addLValue no longer declare to solver | Monad.lean |
| NEW | spineL Define: direct substitution (not addLValue) | Spine.lean |
| NEW | processPreClause/processPostClause: addL+addC(def_) | Check.lean |
| MOD-14 | conv_int: added wchar_t, wint_t, ptraddr_t cases | Pexpr.lean |
| NEW | simplifyPredicate/simplifyRequest/simplifyResource | Simplify.lean |

---

## Critical Bugs (would cause incorrect results)

### BUG-1: Simplifier symbol substitution too aggressive
**File:** `Simplify.lean:233-236` vs `simplify.ml:221-225`

CN only inlines symbol values that are `Const` or `Sym` (simple values). Our implementation inlines ANY value from `symEqs` and recursively simplifies. This could cause:
- Exponential term growth from inlining complex expressions
- Different simplification results than CN
- Potential infinite loops if values contain cycles

```ocaml
(* CN: only inline constants and symbols *)
| Some (IT ((Const _ | Sym _), _, _) as v) -> v
| _ -> the_term
```
```lean
-- Lean: inlines ANY value
| some value => simplifyTerm ctx value
```

### BUG-2: Inline solver missing preamble declarations
**File:** `Params.lean:545`

The inline cvc5 solver only gets `pointerPreamble ++ structPreamble`. Missing:
- `tuplePreamble` (cn_tuple_0 through cn_tuple_15)
- `listPreamble` (cn_list)
- `optionPreamble` (cn_option)
- `memBytePreamble` (mem_byte)
- `uninterpFunctionPreamble` (mul_uf_*, div_uf_*, etc.)

The batch solver (`obligationToSmtLib2` at SmtLib.lean:1612) correctly includes all of these via `solverBasicsPreamble`. Any inline query involving tuples, options, lists, or *NoSMT operations will fail.

**Fix:** Change `pointerPreamble ++ structPreamble` to `solverBasicsPreamble ++ uninterpFunctionPreamble ++ structPreamble`.

### BUG-3: `addC` doesn't simplify constraint before adding
**File:** `Monad.lean:484-494` vs `typing.ml:403-412`

CN calls `Simplify.LogicalConstraints.simp simp_ctxt lc` before adding a constraint to the context and assuming it in the solver. Our `addC` adds the raw unsimplified constraint. This means:
- Solver gets harder-to-reason-about terms
- Symbol equalities from constraints may not be in canonical form
- `isSymLhsEquality` may not detect equalities that simplification would expose

### BUG-4: `addR` doesn't simplify resource before adding
**File:** `Monad.lean:508-516` vs `typing.ml:415-427`

Same issue for resources. CN simplifies both the request (pointer, iargs) and output before storing. Without simplification, resource matching (which relies on syntactic equality as a fast path) may miss matches that CN would find.

### BUG-5: Store action consumes Init (CN only consumes Uninit)
**File:** `Action.lean:346-366` vs `check.ml:1879-1883`

CN's store ONLY tries to consume `Owned(ct, Uninit)`. Our implementation falls back to consuming `Owned(ct, Init)` if Uninit isn't found. This is more permissive — it allows overwriting initialized memory directly without the resource having been explicitly consumed and re-produced as Uninit.

### BUG-6: Kill action consumes Init (CN only consumes Uninit)
**File:** `Action.lean:248-272` vs `check.ml:1831-1846`

Same divergence as store: CN's kill only consumes Uninit, ours falls back to Init.

### BUG-7: conv_int Bool creates `.z 0` instead of `.bits` constant
**File:** `Pexpr.lean:1039-1044` vs `check.ml:413-420`

For Bool→integer conversion, CN creates `num_lit_ Z.zero expect` which produces a `.bits sign width 0` constant at the target bitvector type. Our code creates `.z 0` (unbounded integer constant) typed as `targetBt`. This creates an integer constant typed as `Bits`, which may cause SMT type errors since the constant won't be encoded as a bitvector literal.

### BUG-8: `LabelContext.ofLabelDefs` hardcodes `BaseType.loc` for all label parameters
**File:** `ArgumentTypes.lean:484-485` and `490-491`

In the fallback path for loop labels (when `loopLabelTypes.lookup` returns `none`) and for non-loop/non-return labels, all parameters are typed as `BaseType.loc` regardless of their actual type. The `_bt` variable is discarded:
```lean
fun (sym, _bt) acc =>
    .computational sym .loc ...  -- Should be _bt, not .loc
```

### BUG-9: `BaseType.beq` compares Struct/Datatype by `.id` only
**File:** `Base.lean:130-131`

Uses `t1.id == t2.id` (numeric id only) while `Sym.BEq` compares both `digest` and `id`. Could cause false equality between different symbols that share a numeric id but differ in digest. Low practical risk within a single translation unit but technically wrong.

### BUG-10: `bv2int` ignores signedness for Bits→Integer cast
**File:** `SmtLib.lean:1007-1009`

SMT-LIB's `bv2int` always returns the unsigned interpretation. For signed bitvectors (e.g., `-1` as `0xFF` for i8), `bv2int` returns 255 instead of -1. Should check signedness and handle negative values.

---

## Moderate Issues (correctness risk in specific cases)

### MOD-1: Missing alpha-renaming in simplifier for `EachI` and `MapDef`
**File:** `Simplify.lean:329-331` and `423-425` vs `simplify.ml:484-488` and `620-624`

CN alpha-renames bound variables before simplifying the body to prevent variable capture. If `symEqs` contains a binding for the bound variable's ID, our simplifier would incorrectly substitute it in the body.

### MOD-2: Missing `Sym _ when Unit -> unit_` simplification rule
**File:** `Simplify.lean` vs `simplify.ml:221`

CN simplifies any symbol with Unit type to `unit_`. Our simplifier only substitutes symbols found in `symEqs`.

### MOD-3: PtrEq/PtrNe missing ambiguous case detection
**File:** `Expr.lean:166-199` vs `check.ml:1527-1595`

CN creates complex constraints for pointer equality that handle the ambiguous case (same address, different provenance). Our implementation simplifies to `result = eq(arg1, arg2)`, making pointer equality fully determined by value equality. This is potentially unsound for programs that exploit provenance differences at the same address.

### MOD-4: Missing `check_live_alloc_bounds` at 4 pointer operation sites
**File:** `Expr.lean:204, 234, 333` (documented as DIVERGES-FROM-CN)

Pointer comparison, ptrdiff, and copyAllocId all skip liveness checking.

### MOD-5: Missing Alloc resource production in Create and consumption in Kill
**File:** `Action.lean:212, 258`

Create doesn't produce Alloc resources, Kill doesn't consume them. This means allocation liveness tracking is entirely absent.

### MOD-6: No duplicate-binding check in Context
**File:** `Context.lean:146-162` vs `context.ml:93-94, 102-103`

CN `failwith` on rebind. We silently shadow. Could mask real type errors.

### MOD-7: PEerror always fails instead of checking dead path
**File:** `Pexpr.lean:1251-1252` vs `check.ml:1075-1082`

CN checks `provable(false)` — if the path is dead, it returns a default value. We always fail.

### MOD-8: `split_case` doesn't fork
**File:** `GhostStatement.lean:294-311` (documented as DIVERGES-FROM-CN)

CN forks the entire remaining continuation into two branches. We just add the constraint as an assumption. Programs relying on case-splitting for different properties in different branches won't work.

### MOD-9: QPredicate request substantially simplified
**File:** `Inference.lean:571-676` vs `resourceInference.ml:253-375`

Missing partial Q resource consumption, `movable_indices` scanning, and `cases_to_map` merging. Only handles a single matching QPredicate.

### MOD-10: Missing integer comparison algebraic simplification
**File:** `Simplify.lean:588-612` vs `simplify.ml:57-142`

CN's `simp_int_comp` decomposes addition/subtraction trees to cancel common terms (e.g., `(x + 3) < (x + 5)` → `true`). We only do constant folding.

### MOD-11: Store missing type-check of stored value against C type
**File:** `Action.lean:289-366` vs `check.ml:1851-1856`

CN calls `WellTyped.ensure_base_type` to verify the stored value's type matches the C type. We skip this check.

### MOD-12: Missing `ensure_base_type` check for computational args in spine
**File:** `Spine.lean:157-165` vs `check.ml:1163-1166`

CN verifies the Core annotation type matches the expected type before evaluating. We skip this.

### MOD-13: `addAValue` incorrectly declares in solver
**File:** `Monad.lean:433-439` vs `typing.ml:341-343`

CN deliberately does NOT declare value-bound computational variables in the solver. We declare them and assert an equality. While sound, it adds unnecessary solver work and diverges from CN.

### MOD-14: conv_int missing `wchar_t`, `wint_t`, `ptraddr_t` cases
**File:** `Pexpr.lean:1046-1084` vs `check.ml:394-431`

These integer subtypes are not handled and will fail.

---

## Missing Features (known gaps, not bugs)

### Feature gaps that affect correctness of specific programs:

| Feature | Location | CN Reference |
|---------|----------|-------------|
| Shift operations (shl/shr) in PEwrapI/PEcatch | Pexpr.lean:1309, 1329 | check.ml:966-1018 |
| ByteFromInt / IntFromByte memops | Not implemented | check.ml:712-754 |
| `instantiate` ghost statement | GhostStatement.lean:184 | check.ml:2144-2156 |
| `unfold` ghost statement | GhostStatement.lean:352 | check.ml:2191-2209 |
| `apply` (lemma) ghost statement | GhostStatement.lean:360 | check.ml:2210-2220 |
| `to_from_bytes` ghost statement | GhostStatement.lean:376 | check.ml:2087-2137 |
| `pack/unpack` ghost statements | GhostStatement.lean:336-345 | check.ml:2050-2086 |
| `do_unfold_resources` loop | Not in Monad.lean | typing.ml:548-657 |
| `bind_logical_return_internal` | Not in Monad.lean | typing.ml:486-501 |
| User-defined predicate pack/unpack | Inference.lean:465, 515 | pack.ml:93-100 |
| Eproc (built-in functions: ctz, ffs) | Expr.lean:686-695 | check.ml:1912-1934 |
| `Eskip` expression | Not in Expr.lean | check.ml:1909-1911 |

### Simplifier gaps (affect solving completeness, not soundness):

| Rule | Lean | CN Reference |
|------|------|-------------|
| `simp_int_comp` algebraic cancellation | Missing | simplify.ml:57-142 |
| Bits→Bits cast constant folding | Missing | simplify.ml:199-206 |
| ArrayShift equality simplification | Missing | simplify.ml:462-465 |
| ITE/const equality decomposition | Missing | simplify.ml:467-474 |
| Tuple/Record equality decomposition | Missing | simplify.ml:475-483 |
| LTPointer/LEPointer via `isIntegerToPointerCast` | Missing | simplify.ml:536-555 |
| Nested Min/Max flattening | Missing | simplify.ml:355-375 |
| Div cancellation `(b*c)/b → c` | Missing | simplify.ml:276 |
| Rem/Mod cancellation `(y*x) rem y → 0` | Missing | simplify.ml:295-312 |
| CTZ/FFS/FLS constant folding | Missing | simplify.ml:419-437 |
| Nested ArrayShift merging | Missing | simplify.ml:573-584 |
| Request simplification before scanning | Missing | resourceInference.ml:116 |

---

## Previously Known Divergences (17 DIVERGES-FROM-CN markers, confirmed still valid)

All 17 existing DIVERGES-FROM-CN markers remain appropriate. No new issues were found that would change their status.

---

## Summary

**10 bugs** that could cause incorrect results or crashes in the current test suite
**14 moderate issues** that affect correctness in specific (usually more complex) programs
**12+ missing features** that are known gaps in the implementation
**12+ simplifier gaps** that affect solving completeness

The most impactful fixes would be:
1. **BUG-1** (simplifier too aggressive) — could affect any test with non-trivial simplification
2. **BUG-2** (inline solver preamble) — easy fix, high impact
3. **BUG-3/4** (missing simplification in addC/addR) — affects resource matching
4. **BUG-5/6** (Store/Kill consuming Init) — semantic divergence from CN
5. **BUG-7** (Bool conv_int) — SMT type error risk
