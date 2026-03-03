# Soundness Audit: ProofSystem Type System

**Date**: 2026-03-03
**Scope**: `lean/CerbLean/ProofSystem/` — all files
**Goal**: Audit the separation-logic type system (HasType) for soundness w.r.t.
the interpreter defined in `CerbLean/Semantics/`.

## Summary

The type system is **structurally well-designed** — the Hoare-triple embedding,
resource threading, frame rule, consequence rule, and substitution-based
save/run interaction are all sound in principle. However, the audit found
**1 true soundness bug** (where the theorem can be falsified by a valid HasType
derivation), **1 major provability gap** (where the proof technique breaks down),
and several minor issues.

**Update 2026-03-03**: Issue 1 (action_create freshness) and Issue 3 (EnvCompat bridge)
have been fixed. Issue 2 reclassified from BUG to DESIGN — Core's `IntegerValue`
carries no `IntegerType` annotation, so `valueHasType` permissiveness is correct.

### Severity Classification

| # | Severity | Issue | Location | Status |
|---|----------|-------|----------|--------|
| 1 | **BUG** | `action_create` missing freshness on `ptrSym` | HasType.lean:684 | **FIXED** |
| 2 | DESIGN | `valueHasType` loaded integers accept any `.bits` type | HasType.lean:228 | Correct (see note) |
| 3 | **PROVABILITY** | `EnvCompat` `∀ τ'` bridge unprovable for integers | Defs.lean:62 | **FIXED** |
| 4 | DESIGN | `evalIndexTerm` incomplete: can't evaluate complex terms | Models.lean:103 | |
| 5 | DESIGN | `.ex` ignores type annotation | Models.lean:257 | |
| 6 | DESIGN | `evalIndexTerm` binop uses left operand's IntegerType | Models.lean:89 | |
| 7 | COMPLETENESS | Missing rules for seqRmw, createReadonly, alloc, catchExceptional | HasType.lean | |
| 8 | COMPLETENESS | Only `.na` memory order and non-locking stores | HasType.lean:634,655 | |

---

## Issue 1 [BUG] [FIXED]: `action_create` missing freshness premise on `ptrSym`

**Location**: HasType.lean:684-691

**Rule**:
```lean
| action_create : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots} {locAnn : Loc}
    {ct : Ctype} {ptrSym : Sym} {alignPe sizePe : APexpr} {prefix_ : SymPrefix},
  sizePe.expr = .val (.ctype ct) →
  HasType Γ H
    ⟨annots, .action ⟨.pos, ⟨locAnn, .create alignPe sizePe prefix_⟩⟩⟩
    .loc
    (.star (.block ct ⟨.sym ptrSym, .loc, default⟩) H)
```

**Problem**: `ptrSym` is an unconstrained implicit argument. There is no premise
requiring it to be fresh w.r.t. `Γ.vars`, `H`, or the current valuation `ρ`.

**Why this is unsound**: The soundness theorem requires:
```
∃ ρ', ValuationExtends ρ ρ' ∧ stateModels typeEnv st' ρ' H₂
```
where `H₂ = .star (.block ct ⟨.sym ptrSym, .loc, default⟩) H`.

For the Block resource, we need `ρ'.lookup ptrSym = some (.pointer (some allocatedLoc))`.
For ValuationExtends, we need `∀ s hv, ρ.lookup s = some hv → ρ'.lookup s = some hv`.

If `ptrSym` is already bound in `ρ` to a different value, these two requirements
contradict. The interpreter's `allocateImpl` succeeds (returns `.ok`), but no valid
`ρ'` exists, making the soundness theorem **FALSE** for this derivation.

**Exploit sketch**: Pick `ptrSym` = some variable already in scope. The derivation
is well-formed (HasType accepts it). The interpreter allocates successfully. But
the postcondition is unsatisfiable under any ρ' extending ρ.

**Fix**: Add freshness premises:
```lean
| action_create : ...
  sizePe.expr = .val (.ctype ct) →
  ptrSym ∉ Γ.vars.map Prod.fst →     -- not in typing context
  -- Optionally: ptrSym not free in H (prevents postcondition issues)
  HasType Γ H (create ...) .loc (.star (.block ct ⟨.sym ptrSym, .loc, default⟩) H)
```

Alternative (more standard in sep logic): wrap the postcondition in an existential:
```lean
HasType Γ H (create ...) .loc
  (.ex ptrSym .loc (.star (.block ct ⟨.sym ptrSym, .loc, default⟩) H))
```

---

## Issue 2 [DESIGN]: `valueHasType` loaded/object integers accept any `.bits` type

**Location**: HasType.lean:228, 243

**Reclassified 2026-03-03**: Originally classified as BUG. Reclassified to DESIGN
after discovering that Core's `IntegerValue = {val: Int, prov: Provenance}` carries
NO `IntegerType` annotation. The permissiveness correctly reflects Core's untyped
integer representation — there is no type information available to check against.
The real fix is in `EnvCompat` (Issue 3), not in `valueHasType`.

**Current definition**:
```lean
| .loaded (.specified (.integer _)), .bits _ _ => True  -- line 228
| .object (.integer _), .bits _ _ => True               -- line 243
```

**Observation**: These accept ANY integer value as ANY `.bits sign width` type,
ignoring the actual sign and width of the integer. This is unavoidable because
Core's `IntegerValue` only contains `{val: Int, prov: Provenance}` — there is
no `IntegerType` to check. The sign/width information exists in the CN type system
(`heapValueHasType` via `HeapValue.integer : IntegerType → Int → HeapValue`) but
not in Core values.

**Interaction with EnvCompat (Issue 3)**: This permissiveness made the old
`EnvCompat` (with `∀ τ', valueHasType v τ' → heapValueHasType hv τ'`) unprovable
for integer-containing environments. Fixed by simplifying EnvCompat to use the
declared type directly: `heapValueHasType hv τ`.

**Note**: The LoadStore example (line 184) relies on this permissiveness:
`PureHasType.val trivial` works because the loaded integer `⟨1, .none⟩` has
`valueHasType (.loaded (.specified (.integer ⟨1, .none⟩))) (.bits .signed 32) = True`
without checking that the value actually fits the type. This is correct behavior.

---

## Issue 3 [PROVABILITY] [FIXED]: `EnvCompat` bridge condition unprovable for integers

**Location**: Defs.lean:57-62

**Current definition**:
```lean
def EnvCompat ... : Prop :=
  ∀ s τ, (s, τ) ∈ vars →
    ∃ v, envLookup env s = some v ∧ valueHasType v τ ∧
    ∃ hv, ρ.lookup s = some hv ∧
      (∀ τ', valueHasType v τ' → heapValueHasType hv τ')
```

**Problem**: The `∀ τ'` quantifier requires the heap value to match EVERY type
that the core value satisfies. Due to Issue 2, loaded/object integers satisfy
`valueHasType _ (.bits sign width)` for all sign and width. This means we'd
need `heapValueHasType hv (.bits sign width)` for all sign and width, which
is impossible since `heapValueHasType` checks sign+width exactly.

**Effect**: EnvCompat is **unprovable** for any environment containing integer
values. Since EnvCompat is a hypothesis of the soundness theorem, the theorem
becomes vacuously true for integer programs — meaning it proves nothing useful.

The same issue affects `PureEnvCompat` (Defs.lean:205-210).

**Fix** (either approach works):

**Option A**: Fix Issue 2 (tighten valueHasType). This makes the `∀ τ'`
quantifier satisfiable because integers would only satisfy their actual type.

**Option B**: Replace `∀ τ'` with the declared type:
```lean
def EnvCompat ... : Prop :=
  ∀ s τ, (s, τ) ∈ vars →
    ∃ v, envLookup env s = some v ∧ valueHasType v τ ∧
    ∃ hv, ρ.lookup s = some hv ∧ heapValueHasType hv τ
```
This only requires the heap value to have the *declared* type, not all types.
Simpler and sufficient for soundness.

**Recommendation**: Do both — tighten valueHasType AND simplify EnvCompat.
The `∀ τ'` bridge was trying to capture "value and heap value agree on all types"
but this is unnecessary. We only need agreement on the declared type.

---

## Issue 4 [DESIGN]: `evalIndexTerm` can't evaluate complex term forms

**Location**: Models.lean:63-103

**Problem**: `evalIndexTerm` handles only:
- `.sym`, `.const (.pointer|.null|.z|.bits|.bool)`, `.binop`, `.unop .not`

It returns `none` for: `.structMember`, `.arrayShift`, `.memberShift`, `.cast`,
`.ite`, `.apply`, `.let_`, `.struct_`, and all other Term constructors.

**Effect**: Any SLProp that references a complex term in an Owned value position
becomes unsatisfiable, because `evalIndexTerm ρ val = none` makes
`evalIndexTerm ρ val = some v` False.

**Mitigating factor**: In practice, CN produces Owned resources where the output
value is always a fresh existential symbol (bound by `.ex`). Complex terms only
appear in pure constraints. So this is unlikely to cause issues in real usage.

**Fix**: Either extend `evalIndexTerm` with more cases, or document this as an
intentional restriction. The current "returns none" behavior is sound (it makes
the proposition harder to satisfy, never easier).

---

## Issue 5 [DESIGN]: `.ex` ignores type annotation in `models`

**Location**: Models.lean:256-257

```lean
| .ex var _ty body =>
    ∃ v, models ((var, v) :: ρ) body h
```

**Problem**: The existential witness `v` is quantified over ALL `HeapValue`,
ignoring the declared type `_ty`. A witness of the wrong type could satisfy
the body through structural coincidence.

**Mitigating factor**: In practice, the body always contains constraints that
force the witness to have the correct type (e.g., Owned resources with
`heapValueHasType` checks). So the type annotation is redundant.

**Fix**: Add a type check:
```lean
| .ex var ty body =>
    ∃ v, heapValueHasType v ty ∧ models ((var, v) :: ρ) body h
```

This is more principled but may complicate proofs unnecessarily since the
body already constrains the type.

---

## Issue 6 [DESIGN]: `evalIndexTerm` binop uses left operand's IntegerType

**Location**: Models.lean:89

```lean
| .add => some (.integer ity1 (v1 + v2))
```

The result uses `ity1` (left operand's type). In C, integer arithmetic applies
promotion rules, so the result type depends on both operand types.

**Mitigating factor**: CN's index terms are already in promoted form (both
operands have the same type after promotion). And for Owned resources, the
output value is typically a symbol (looked up from the valuation), not a
computed arithmetic expression.

**Risk**: If a soundness proof depends on the result IntegerType matching
a specific type (e.g., via `heapValueHasType`), the left-operand-inherits
rule could produce a mismatch.

**Fix**: Either (a) propagate the promoted type, or (b) document the
assumption that both operands always have the same type.

---

## Issue 7 [COMPLETENESS]: Missing typing rules

The following interpreter expression forms have no HasType rule:

| Expression | Interpreter | Status |
|-----------|-------------|--------|
| `seqRmw` | Step.lean:971-1050 | Missing — read-modify-write operations |
| `createReadonly` | Step.lean:838-861 | Missing — string literals, const globals |
| `alloc` | Step.lean:866-876 | Missing — malloc/dynamic allocation |
| `catchExceptionalCondition` | Eval.lean:733-759 | Missing — signed overflow check |
| `Eunseq` | Step.lean:534-732 | Missing — parallel evaluation (out of scope) |

Programs using these constructs cannot be verified. This limits the class of
programs the type system can handle but doesn't affect soundness.

---

## Issue 8 [COMPLETENESS]: Hardcoded memory order and locking

**Location**: HasType.lean:634 (load), 655 (store)

Both `action_load` and `action_store` hardcode `.na` (non-atomic) memory
order and `false` (non-locking) store mode. This is correct for sequential
semantics but means atomic operations and locking stores can't be typed.

Not a soundness issue — just limits coverage.

---

## Verified Correct Aspects

The following aspects were audited and found sound:

1. **Consequence rule direction** (HasType.lean:912-916): Precondition
   strengthening and postcondition weakening directions are correct.
   `entails H₁' H₁` means H₁' is stronger (correct for pre-strengthening).
   `entails H₂ H₂'` means H₂ implies H₂' (correct for post-weakening).

2. **Frame rule structure** (HasType.lean:903-906): Standard separation
   logic frame rule. Soundness relies on each memory operation having
   bounded footprint (single allocation), which the concrete memory model
   with allocation-ID isolation provides.

3. **Load rule** (HasType.lean:628-636): Correctly preserves the Owned
   resource (read-only). Return type `val.bt` matches the value stored
   at the pointer. Pre-heap requires `.init` (loading uninitialized = UB).

4. **Store rule** (HasType.lean:645-657): Correctly updates the Owned
   value from `valOld` to `valNew`. Premise `valNew.bt = τ` connects the
   value's type annotation. `PexprMatchesTerm` bridges Core and SLProp.

5. **Kill rules** (HasType.lean:695-711): Correctly consume resources.
   Both Owned and Block forms handled.

6. **If rule path conditions** (HasType.lean:578-585): Correctly adds
   `condTerm` to the then-branch and `negateIndexTerm condTerm` to the
   else-branch. The `condTermOfPexpr` bridge ensures the path condition
   actually corresponds to the condition expression.

7. **Save/Run interaction** (HasType.lean:860-895): The substitution-based
   loop invariant mechanism is structurally sound. `save` establishes
   the invariant with initial values; `run` re-establishes it with new
   values. The `∀ fuel` quantification in the soundness theorem breaks
   the circularity. The unconstrained τ/H₂ in `run` is correct (run
   transfers control, doesn't return).

8. **Proc/Ccall** (HasType.lean:721-763): Modular specification via
   `FunSpecsCorrect`. The `PexprMatchesTerm` premises and substitution
   σ correctly instantiate specs with actual arguments.

9. **Excluded rule** (HasType.lean:613-616): Treats `Eexcluded` as
   transparent (same typing as inner action). Sound because `Eexcluded`
   only affects annotations for race detection, not memory effects.

10. **models relation** (Models.lean:222-271): Lookup-based semantics
    for all SLProp constructors. Star commutativity, associativity, and
    unit laws proved. Equiv-invariance proved. emp/pure/owned/block/each
    cases all sound.

11. **heapValueHasType** (Models.lean:143-153): Tight — checks sign+width
    for integers, tag for structs. No blanket catchalls.

12. **PureHasType type predicates** (HasType.lean:457-481): Correctly
    require `.ctype` input. The interpreter's `isScalar`/`isInteger`/etc.
    branches throw on non-ctype values, matching the type system's
    requirement.

13. **Block ↔ Owned(.uninit) equivalence** (Models.lean:600-623):
    Correctly proved. Programs needing to store to Owned(.uninit) can
    use consequence to weaken to Block, then use `action_store_block`.

---

## Recommendations (Priority Order)

### P0: Fix soundness bugs — DONE

1. ~~Add freshness premise to `action_create` (Issue 1)~~ — **FIXED**: added
   `ptrSym ∉ Γ.vars.map Prod.fst` premise
2. ~~Tighten `valueHasType` integer cases (Issue 2)~~ — **Reclassified**: not a bug.
   Core's `IntegerValue` has no `IntegerType` annotation; permissiveness is correct.

### P1: Fix provability — DONE

3. ~~Simplify `EnvCompat` bridge condition (Issue 3)~~ — **FIXED**: replaced
   `∀ τ', valueHasType v τ' → heapValueHasType hv τ'` with `heapValueHasType hv τ`
   in both `EnvCompat` and `PureEnvCompat`
4. LoadStore example verified — still compiles (doesn't reference EnvCompat)

### P2: Strengthen the model

5. Add type check to `.ex` in `models` (Issue 5) — optional but principled
6. Document `evalIndexTerm` limitation (Issue 4) — OK as-is if CN always
   uses symbols for Owned output values

### P3: Extend coverage

7. Add typing rules for `seqRmw`, `createReadonly`, `alloc` (Issue 7)
8. Add `catchExceptionalCondition` rule (Issue 7)
