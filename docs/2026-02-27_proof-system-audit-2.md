# Proof System Audit #2: Post-Fix Assessment

*Created: 2026-02-27*
*Auditors: slprop-auditor, hastype-auditor, models-auditor*
*Files audited: SLProp.lean, HasType.lean, Models.lean, Convert.lean, Examples/{ReturnLiteral,LoadStore}.lean*
*Compared against: docs/2026-02-27_core-proof-system-plan.md*

## Executive Summary

| Stage | Status | Assessment |
|-------|--------|------------|
| **Stage 1** (SLProp + Convert) | **95%** | All 8 constructors correct; `letBinding` FIXME, `block` unreachable from Convert |
| **Stage 2** (HasType) | **75%** | 13/14 plan rules implemented; 3 critical soundness holes in action/proc rules |
| **Stage 3** (Models) | **70%** | Structure correct; `evalConstraint` unsound (degrades to True), `evalIndexTerm` too limited |
| **Stage 4** (Soundness) | **0%** | As planned — blocked by bridge infrastructure |

**Overall: The structure is right, but several rules are too permissive to prove anything meaningful. The 3 critical soundness holes (proc, load return type, store value) would let you "prove" false statements.**

---

## Critical Soundness Holes (must fix — these allow proving false statements)

### S1: `proc` rule is vacuous [HasType:291]
The `proc` rule looks up a spec from context but:
- `preSL`/`postSL` are unconstrained implicits — never connected to `spec.requires`/`spec.ensures`
- `args` are never connected to spec parameters
- Return type `τ` is unconstrained

**Impact**: You can "prove" any post-condition for any function call. The rule should have premises: `preSL = SLProp.ofPrecondition spec.requires`, `postSL = SLProp.ofPostcondition spec.ensures`.

### S2: `action_load` has unconstrained return type [HasType:241]
`τ : CNBaseType` is universally quantified with no relation to `ct` (the Ctype being loaded). A load from `int*` could claim to return type `bool`.

**Fix**: Add a premise `cTypeToBaseType ct = τ` (or similar) relating the C type to the CN base type.

### S3: `action_store` has unconstrained `valNew` [HasType:250]
`valNew : IndexTerm` appears only in the postcondition but has no connection to `valPe` (the value being stored). The rule can claim any value was stored.

**Fix**: Add a premise connecting `valNew` to the evaluation/typing of `valPe`.

### S4: `evalConstraint` degrades to `True` [Models:100]
When `evalIndexTerm` returns `none` for a constraint term, `evalConstraint` returns `True`. Since `evalIndexTerm` can't handle binary ops, this means constraints like `x + y > 0` are vacuously true.

**Impact**: `models ρ (.pure c) h` holds for most non-trivial constraints regardless of whether they're actually satisfied. This makes soundness proofs meaningless.

**Fix**: Change the degraded case to `False` (sound/conservative) or propagate `Option`.

---

## Significant Issues (don't cause unsoundness but block real proofs)

### I1: `consequence` uses equality, not entailment [HasType:318]
Premises are `H₁' = H₁` and `H₂ = H₂'`, making the rule only useful when SLProps are syntactically identical. Blocks any resource rearrangement (star commutativity, existential instantiation).

### I2: `case_` doesn't track pattern bindings [HasType:224]
Branch bodies type in bare `Γ` — variables bound by pattern matching aren't in scope. Blocks any case expression that destructures values (e.g., `Specified v` → use `v`).

### I3: `if_` else branch missing negated path condition [HasType:219]
True branch gets `Γ.addPathCond (.t condTerm)` but else branch uses bare `Γ`. Also, `condTerm` is an unconstrained implicit not connected to `cond`.

### I4: `action_create` has unconstrained `ct` and `ptr` [HasType:261]
`ct` not connected to size/align expressions. `ptr` should be existentially quantified in the postcondition rather than a free implicit.

### I5: `SLProp.block` unreachable from Convert [Convert:26-41]
CN represents `Block<T>` as `Owned<T>(uninit)`. `ofResource` maps this to `SLProp.owned ct .uninit ptr val`, never to `SLProp.block`. But HasType rules reference `.block` (create, kill_block). No bridge between the two representations.

### I6: `letBinding` drops bindings [Convert:61-65]
`ofClausesScoped` silently discards `letBinding` clauses. Any CN spec using `let x = expr;` loses that binding.

### I7: `equiv` vs structural equality mismatch [Models:134 vs Interpretation]
`models` star case uses `h.equiv (h1 ++ h2)` (lookup-based) while `interpResources` uses `h = h1 ++ h2` (structural). Makes `models_ofResources_iff` harder to prove than expected.

### I8: `PureHasType.op` doesn't constrain result type [HasType:121-125]
Result type `τ` has no relation to input types or operator. `3 + 5` could be typed as `.bool`.

---

## Gaps (plan items not yet implemented)

### G1: `save`/`run` rules — MISSING
Plan rule #12. `LabelInv` is defined but unused by any HasType constructor. Blocks loop verification.

### G2: `PureHasType` coverage — 4 of ~25 `Pexpr` constructors
Missing critical cases: `ctor` (needed for `Specified(v)`), `arrayShift`, `memberShift`, `memberof`, `struct_`, `union_`, `call`, `let_`, `case_`, `not_`, `convInt`, `wrapI`.

### G3: `memop` rule — MISSING
`Expr.memop` covers pointer comparison, `intFromPtr`, `ptrFromInt`, `ptrArrayShift`, `ptrMemberShift`. No typing rule exists.

### G4: `evalIndexTerm` missing binary ops [Models:59-78]
Only handles 6 term forms. Missing: all binary operations (20+ in `BinOp`), `memberShift`, `arrayShift`, `negate`, `not_`, `cast`, `ite`, field projection. Without binary ops, most CN constraints are unevaluable.

### G5: `annot`/`ccall` rules — MISSING
`Expr.annot` should be transparent (like `bound`). `Expr.ccall` needed for function pointer calls.

### G6: Ghost params/accesses not converted [Convert]
`FunctionSpec.ghostParams` and `resolvedAccesses` are ignored by `ofSpec`. Ghost params should produce existential quantifiers; accesses should produce `Owned` resources for globals.

### G7: Stage 4 infrastructure — NOT STARTED (as planned)
`stateModels`, `ctxModels`, `heapFragmentOf`, per-rule soundness lemmas all missing.

---

## What's Correct

- **SLProp**: All 8 constructors match plan exactly. `starAll`/`flatten` correct.
- **Convert**: `ofResource` maps all 3 request variants correctly. `ofClausesScoped` telescope scoping correct. `owned none` → `pure(false)` correct.
- **HasType**: Heap threading (`H₁→H₂→H₃`) in sseq/wseq correct. Variable bindings in context correct. Frame rule correctly stated. Kill rules (owned/block split) correct. `bound` rule correct.
- **Models**: All 8 SLProp cases handled. `interpOwned` reuse correct. `models_emp`/`models_pure` proved. `pred`/`each` returning `False` is sound (conservative). `SLProp.entails` correctly defined.
- **Examples**: ReturnLiteral and LoadStore both type-check. LoadStore exercises load/store/sseq/pure.
- **valueHasType**: Correct for integer/pointer/unit/bool/ctype. Catch-all `False` is sound.

---

## Remaining Sorrys

| Sorry | Location | Difficulty | Assessment |
|-------|----------|------------|------------|
| `union_lookup_comm` | Models:162 | Easy (~20 lines) | Provable — standard List.find? lemma |
| `models_star_assoc_forward` | Models:180 | Medium (~40 lines) | Provable given union_lookup_comm |
| `models_ofResources_iff` | Models:189 | Hard | Complicated by equiv-vs-equality mismatch (I7) |

---

## Priority Action Items

### P0: Fix soundness holes (before any further work)
1. **S1**: Connect `proc` rule to spec (add `preSL = ofPrecondition spec.requires` premise)
2. **S2**: Constrain `action_load` return type (add `cTypeToBaseType ct = τ` or similar)
3. **S3**: Connect `action_store` valNew to valPe
4. **S4**: Change `evalConstraint` fallback from `True` to `False`

### P1: Fix significant issues (for meaningful proofs)
5. **I1**: Upgrade `consequence` to use `SLProp.entails`
6. **I2**: Track pattern bindings in `case_`
7. **I5**: Reconcile `SLProp.block` vs `Owned(uninit)` in Convert
8. **I8**: Add operator typing to `PureHasType.op`

### P2: Close gaps (for CN proof support)
9. **G1**: Add `save`/`run` rules
10. **G2**: Extend `PureHasType` (especially `ctor`, `memberShift`, `arrayShift`)
11. **G4**: Extend `evalIndexTerm` with binary ops, memberShift, arrayShift
12. **G3**: Add `memop` rule
13. **I6**: Fix `letBinding` in Convert
14. **G6**: Convert ghost params and accesses in `ofSpec`

### P3: Soundness infrastructure (Stage 4)
15. **I7**: Align equiv vs equality in `models` star case
16. Prove the 3 remaining sorrys
17. **G7**: Build `stateModels`, `ctxModels`, interpreter bridge
18. Per-rule soundness lemmas

---

## Distance Assessment: "Can we support CN proofs?"

**Current state**: We can type-check `return 0` and `*p = *p + 1` — expressions using pure values, load, store, and sequencing. The typing derivations compile but are not yet meaningful for soundness because the action rules are too permissive (S1-S3).

**After P0 fixes**: The proof system would be sound for the subset it covers. You could make true statements about load/store/create/kill sequences, but only for programs that don't use loops, function calls with specs, pattern matching, or complex constraints.

**After P0+P1**: The proof system would support real resource rearrangement (via entailment), pattern matching, and operator typing. This covers most straight-line code.

**After P0+P1+P2**: The proof system would support loops (save/run), function calls with specs, struct access, array access, and most CN specifications. This is the point where you could connect CN's output to generate HasType derivation trees.

**After P0+P1+P2+P3**: Full soundness — well-typed programs provably don't cause UB. This is the end goal.
