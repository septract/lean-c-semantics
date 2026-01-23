# SMT Discharge Plan: Bridging CN Constraints to Pure Arithmetic

## Key Insight: Separation of Concerns

CN's design separates two kinds of verification:

1. **Heap/Resource obligations**: Ownership, disjointness, pointer validity
   - Handled by **type checker** via syntactic resource matching
   - Separation logic guarantees come from the matching algorithm
   - NO SMT needed

2. **Arithmetic obligations**: Bounds checks, integer constraints, comparisons
   - These are what **SMT should handle**
   - Examples: `x > 0`, `x + y < 100`, `array_len > idx`

This plan focuses exclusively on (2) - extracting pure arithmetic from CN constraints so SMT can discharge them.

## The Problem

We want to discharge arithmetic `Obligation.toProp`:
```lean
def Obligation.toProp (ob : Obligation) : Prop :=
  ∀ ρ : Valuation, constraintSetToProp ρ ob.assumptions → constraintToProp ρ ob.constraint
```

Where:
```lean
def constraintToProp (ρ : Valuation) : LogicalConstraint → Prop
  | .t it => match denoteAnnotTerm ρ it with
             | some v => heapValueIsTrue v
             | none => False

def heapValueIsTrue : HeapValue → Prop
  | .integer _ n => n ≠ 0
  | _ => False

-- Valuation maps symbols to HeapValues
abbrev Valuation := List (Sym × HeapValue)
```

**Why SMT can't handle this directly**: After unfolding, SMT sees:
```
∀ ρ : Valuation, ... → heapValueIsTrue (denoteTerm ρ term)
```

SMT doesn't understand `HeapValue`, `denoteTerm`, or `heapValueIsTrue`. It only understands pure arithmetic: `Int`, `Bool`, `<`, `≤`, `=`, `+`, `*`, etc.

## The Solution: Pure Interpretation Layer

Create a parallel interpretation that maps terms directly to pure Lean types, bypassing `HeapValue`.

### Key Types

```lean
/-- Pure valuation: maps symbols directly to integers -/
abbrev PureIntVal := Sym → Int

/-- Pure boolean valuation for bool-typed symbols -/
abbrev PureBoolVal := Sym → Bool
```

### Key Functions

```lean
/-- Interpret an integer-typed term as an Int -/
def termToInt (σ : PureIntVal) : Term → Option Int
  | .const (.z n) => some n
  | .sym s => some (σ s)
  | .binop .add l r => do return (← termToInt σ l.term) + (← termToInt σ r.term)
  | .binop .sub l r => do return (← termToInt σ l.term) - (← termToInt σ r.term)
  | .binop .mul l r => do return (← termToInt σ l.term) * (← termToInt σ r.term)
  | _ => none  -- Non-integer or unsupported

/-- Interpret a boolean-typed term as a Prop (comparison results) -/
def termToProp (σ : PureIntVal) : Term → Option Prop
  | .const (.bool true) => some True
  | .const (.bool false) => some False
  | .binop .lt l r => do return (← termToInt σ l.term) < (← termToInt σ r.term)
  | .binop .le l r => do return (← termToInt σ l.term) ≤ (← termToInt σ r.term)
  | .binop .eq l r => do return (← termToInt σ l.term) = (← termToInt σ r.term)
  | _ => none

/-- Interpret a LogicalConstraint in pure form -/
def constraintToPureProp (σ : PureIntVal) : LogicalConstraint → Option Prop
  | .t it => termToProp σ it.term
  | .forall_ _ _ => none  -- Handle separately
```

### Soundness Bridge

The key insight: for arithmetic constraints, we can work entirely in the pure domain.

**Step 1**: Define when a pure valuation corresponds to a HeapValue valuation:

```lean
/-- A pure valuation is compatible with a HeapValue valuation if they agree on integers -/
def valuationCompatible (ρ : Valuation) (σ : PureIntVal) : Prop :=
  ∀ s : Sym, match ρ.lookup s with
    | some (.integer _ n) => σ s = n
    | _ => True  -- Non-integer symbols don't matter for integer constraints
```

**Step 2**: The key soundness theorem (stated as an implication for SMT use):

```lean
/-- For arithmetic constraints: if pure version holds, original holds -/
theorem arith_constraint_sound
    (σ : PureIntVal) (lc : LogicalConstraint)
    (h_arith : lc.isArithmetic)  -- Only arithmetic terms
    (h_pure : pureConstraintHolds σ lc)  -- Pure version holds
    : ∀ ρ : Valuation, valuationCompatible ρ σ → constraintToProp ρ lc
```

**Why this direction?** We want: SMT proves pure → we get constraintToProp.
The implication goes from pure to full, not biconditional, because that's what we need.

### The Discharge Strategy

For an obligation with only integer arithmetic:

1. **Unfold** `Obligation.toProp` to get:
   ```
   ∀ ρ : Valuation, constraintSetToProp ρ assumptions → constraintToProp ρ constraint
   ```

2. **Transform** using soundness lemma:
   ```
   ∀ σ : PureIntVal, pureConstraintSetToProp σ assumptions → pureConstraintToProp σ constraint
   ```

3. **Unfold** pure interpretations to get pure arithmetic:
   ```
   ∀ σ : Sym → Int, (σ x > 0 ∧ σ y > 0) → σ x + σ y > 0
   ```

4. **Call SMT** on the pure arithmetic goal.

## Current Infrastructure Assessment

**What we have (aligned with plan):**

| Component | File | Status |
|-----------|------|--------|
| `denoteTerm` | `Denote.lean` | ✓ Terminating |
| `constraintToProp` | `Denote.lean` | ✓ Works |
| `evalConstraint` | `Denote.lean` | ✓ Decidable Bool |
| `Obligation.toProp` | `Obligation.lean` | ✓ Correct |
| Ground discharge tests | `Test/Discharge.lean` | ✓ `native_decide` works |

**Key insight:** `denoteBinOp` already computes with `Int` internally:
```lean
| .lt => do
    let HeapValue.integer _ n1 := v1 | none  -- unwrap
    let HeapValue.integer _ n2 := v2 | none  -- unwrap
    return boolToHeapValue (n1 < n2)         -- wrap
```

The pure interpretation skips wrapping - soundness proof shows this is equivalent.

**What's missing:**

| Component | Purpose |
|-----------|---------|
| `termToInt`, `termToProp` | Pure interpretation (no HeapValue) |
| Soundness theorem | Bridge pure ↔ HeapValue |
| `cn_to_pure` tactic | Transform goals before SMT |

## Implementation Plan

### Phase 1: Pure Interpretation Functions

Create `CN/Semantics/PureDenote.lean`:

1. Define `PureIntVal`, `PureBoolVal`
2. Implement `termToInt`, `termToProp`, `constraintToPureProp`
3. Keep these terminating (well-founded recursion on term size - we already did this!)

### Phase 2: Soundness Theorems

Create `CN/Semantics/DenoteSoundness.lean`:

1. Define `valuationCompatible`
2. Prove `termToInt_sound`: relates `termToInt` to `denoteTerm` for integer terms
3. Prove `termToProp_sound`: relates `termToProp` to `constraintToProp`
4. Prove `constraintToPureProp_sound`: the main bridge theorem

### Phase 3: Transformation Tactic

Enhance `CN/Verification/Discharge.lean`:

1. Add `cn_to_pure` tactic that:
   - Recognizes `constraintToProp` goals
   - Applies soundness theorems to transform to pure form
   - Unfolds pure interpretation to bare arithmetic

2. Modify `cn_discharge` to:
   - Try `cn_to_pure` followed by `smt [*]`
   - Fall back to other strategies

### Phase 4: Testing

Add tests to `Test/Discharge.lean`:

1. Symbolic integer constraints: `x > 0 → x > 0`
2. Arithmetic derivations: `x > 0, y > 0 → x + y > 0`
3. Mixed with constants: `x > 5 → x > 0`

## Concerns and Mitigations

### Concern 1: What if `termToInt` returns `none`?

**Issue**: Term might not be a pure integer expression (e.g., pointer, struct, unsupported op).

**Mitigation**:
- The soundness theorem only applies when `constraintToPureProp` succeeds
- For non-arithmetic constraints, fall back to other strategies (assumption, manual)
- Type checker can flag when constraints are outside the supported fragment

### Concern 2: Valuation quantifier

**Issue**: `∀ ρ : Valuation` is over an infinite domain.

**Solution**: Transform to `∀ σ : PureIntVal` which is `∀ σ : Sym → Int`. This is exactly what SMT handles well - it instantiates with fresh symbolic integers.

### Concern 3: Partiality of `denoteTerm`

**Issue**: `denoteTerm` returns `Option HeapValue`, can fail.

**Solution**: The soundness theorem has precondition that pure interpretation succeeds. If `denoteTerm` fails, `constraintToProp` is `False`, which is actually easier to prove (anything implies False is... wait, that's wrong).

Actually: If `denoteTerm` returns `none`, then `constraintToProp ρ lc = False`. An obligation saying `... → False` is only provable if assumptions are contradictory. This is a well-formedness issue - properly type-checked programs shouldn't have unevaluable constraints.

**Mitigation**: Add well-formedness precondition to soundness theorem, or prove type checker ensures evaluability.

### Concern 4: Assumptions also need transformation

**Issue**: Both the assumptions AND constraint need pure interpretation.

**Solution**:
```lean
def pureConstraintSetToProp (σ : PureIntVal) (lcs : LCSet) : Option Prop :=
  lcs.foldlM (fun acc lc => do
    let p ← constraintToPureProp σ lc
    return acc ∧ p) True
```

Soundness:
```lean
theorem constraintSetToProp_pure_sound (ρ σ lcs h_compat) (h_pure : pureConstraintSetToProp σ lcs = some P) :
    constraintSetToProp ρ lcs ↔ P
```

### Concern 5: Proving soundness theorems

**Issue**: Need to prove that pure interpretation matches HeapValue interpretation.

**Approach**: Induction on term structure. Key lemmas:
- `denoteConst_z`: `denoteConst (.z n) = some (.integer _ n)`
- `denoteBinOp_add`: relates `denoteBinOp .add` to `+` on integers
- Similar for other operations

These are straightforward since `denoteTerm` is now terminating!

## Success Criteria

1. Can prove `example : (∀ x : Int, x > 0 → x > 0) := by smt [*]` (sanity check)
2. Can prove symbolic obligation `x > 0 ⊢ x > 0` using `cn_discharge`
3. Can prove derived obligation `x > 0, y > 0 ⊢ x + y > 0` using `cn_discharge`
4. Soundness theorems proven without sorry

## Estimated Effort

- Phase 1 (Pure interpretation): ~1 hour (straightforward, similar to `denoteTerm`)
- Phase 2 (Soundness theorems): ~2-4 hours (inductive proofs, main effort)
- Phase 3 (Tactic): ~1-2 hours (metaprogramming)
- Phase 4 (Testing): ~1 hour

Total: ~5-8 hours of focused work.

## Alternative Considered: Reflection

Instead of transforming goals, we could:
1. Prove `evalConstraint ρ lc = true → constraintToProp ρ lc`
2. Use `native_decide` on the Bool side

**Why pure interpretation is better**:
- `native_decide` only works for ground terms (concrete `ρ`)
- For symbolic `ρ`, we need SMT, which requires pure arithmetic goals
- Pure interpretation gives us exactly that
