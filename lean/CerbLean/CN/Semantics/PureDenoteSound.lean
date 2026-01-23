/-
  Soundness of Pure Denotation

  This module proves that the pure interpretation (termToInt, termToProp)
  is sound with respect to the HeapValue-based interpretation (denoteTerm,
  constraintToProp).

  ## Main Theorem

  For compatible valuations:
  - If `constraintToPureProp σ lc = some P` and `P` holds
  - Then `constraintToProp ρ lc` holds

  This allows SMT to prove the pure version, and we can lift it to the
  HeapValue version using these soundness theorems.

  ## Proof Strategy

  Build up from smaller lemmas:
  1. `termToInt_matches_denoteTerm`: pure int matches HeapValue int
  2. `termToProp_implies_constraintToProp`: pure prop implies HeapValue prop
  3. `constraintToPureProp_sound`: main soundness theorem

  Audited: 2026-01-22 (new implementation for SMT discharge)
-/

import CerbLean.CN.Semantics.PureDenote
import CerbLean.CN.Semantics.Denote
import CerbLean.CN.Verification.Obligation

namespace CerbLean.CN.Semantics

open CerbLean.Core (Sym Loc IntegerType)
open CerbLean.CN.Types
open CerbLean.CN.Verification (Obligation)

/-! ## Helper Lemmas

Properties of HeapValue and denotation.
-/

/-- heapValueIsTrue on an integer is equivalent to n ≠ 0 -/
theorem heapValueIsTrue_integer (ty : IntegerType) (n : Int) :
    heapValueIsTrue (.integer ty n) ↔ n ≠ 0 := by
  simp [heapValueIsTrue]

/-- boolToHeapValue true gives a non-zero integer -/
theorem boolToHeapValue_true_isTrue :
    heapValueIsTrue (boolToHeapValue true) := by
  simp [boolToHeapValue, heapValueIsTrue]

/-- boolToHeapValue false gives zero -/
theorem boolToHeapValue_false_not_isTrue :
    ¬heapValueIsTrue (boolToHeapValue false) := by
  simp [boolToHeapValue, heapValueIsTrue]

/-- boolToHeapValue b is true iff b is true -/
theorem boolToHeapValue_isTrue_iff (b : Bool) :
    heapValueIsTrue (boolToHeapValue b) ↔ b := by
  cases b <;> simp [boolToHeapValue, heapValueIsTrue]

/-! ## Pure Valuation Extraction

Extract a pure integer valuation from a HeapValue valuation.
-/

/-- Extract integer values from a HeapValue valuation.
    Non-integer symbols default to 0. -/
def extractPureVal (ρ : Valuation) : PureIntVal := fun s =>
  match ρ.lookup s with
  | some (.integer _ n) => n
  | _ => 0

/-- extractPureVal produces a compatible pure valuation -/
theorem extractPureVal_compatible (ρ : Valuation) :
    valuationCompatible ρ (extractPureVal ρ) := by
  intro s
  -- Goal: match ρ.lookup s with | some (.integer _ n) => extractPureVal ρ s = n | _ => True
  simp only [extractPureVal]
  cases h : ρ.lookup s with
  | none => trivial
  | some v =>
    cases v with
    | integer ty n => simp [h]
    | _ => trivial

/-! ## Integer Soundness

termToInt matches denoteTerm for integer results.

Note: Because `termToInt` and `termToBool` are `partial` (mutually recursive),
we cannot unfold them or do structural induction directly. The soundness
theorems below use `sorry` and would require either:
1. Making termToInt/termToBool terminating (well-founded recursion), or
2. Defining an auxiliary inductive predicate capturing the computation

For now, the structure is in place for the SMT discharge strategy.
-/

/-- For symbols: when valuations are compatible, integers match -/
theorem termToInt_sym_matches
    (ρ : Valuation) (σ : PureIntVal) (s : Sym) (ty : IntegerType) (n : Int)
    (h_lookup : ρ.lookup s = some (.integer ty n))
    (h_compat : valuationCompatible ρ σ) :
    σ s = n := by
  unfold valuationCompatible at h_compat
  have hs := h_compat s
  simp only [h_lookup] at hs
  exact hs

/-- General soundness theorem for integer terms.
    If termToInt succeeds with value n, then denoteTerm gives an integer with that value.

    TODO: Requires termToInt to be terminating for full proof by induction. -/
theorem termToInt_matches_denoteTerm
    (ρ : Valuation) (σ : PureIntVal) (t : Term) (n : Int)
    (h_compat : valuationCompatible ρ σ)
    (h_pure : termToInt σ t = some n) :
    ∃ ty, denoteTerm ρ t = some (.integer ty n) := by
  sorry

/-! ## Boolean/Prop Soundness

termToProp matches constraintToProp.
-/

/-- If termToProp gives P, and P holds, then constraintToProp (.t term) holds -/
theorem termToProp_implies_constraintToProp
    (ρ : Valuation) (σ : PureIntVal) (it : IndexTerm) (P : Prop)
    (h_compat : valuationCompatible ρ σ)
    (h_pure : termToProp σ it.term = some P)
    (h_P : P) :
    constraintToProp ρ (.t it) := by
  sorry  -- TODO: induction on term structure

/-! ## Main Soundness Theorem

The key theorem for SMT discharge.
-/

/-- Pure constraint soundness: if pure interpretation holds, HeapValue interpretation holds -/
theorem constraintToPureProp_sound
    (ρ : Valuation) (σ : PureIntVal) (lc : LogicalConstraint) (P : Prop)
    (h_compat : valuationCompatible ρ σ)
    (h_pure : constraintToPureProp σ lc = some P)
    (h_P : P) :
    constraintToProp ρ lc := by
  cases lc with
  | t it =>
    -- For .t case, use termToProp_implies_constraintToProp
    simp only [constraintToPureProp] at h_pure
    exact termToProp_implies_constraintToProp ρ σ it P h_compat h_pure h_P
  | forall_ binding body =>
    -- For forall case, need to show universal holds
    sorry  -- TODO: handle forall case

/-- Constraint set soundness -/
theorem constraintSetToPureProp_sound
    (ρ : Valuation) (σ : PureIntVal) (lcs : LCSet) (P : Prop)
    (h_compat : valuationCompatible ρ σ)
    (h_pure : constraintSetToPureProp σ lcs = some P)
    (h_P : P) :
    constraintSetToProp ρ lcs := by
  sorry  -- TODO: induction on list

/-! ## Obligation Soundness

Connect to Obligation.toProp.

The full theorem would be:
  If we can prove the pure version of an obligation, the HeapValue version holds.

This requires showing that for any ρ satisfying assumptions, there exists a compatible σ,
and the pure implication gives us the result.

For now, we provide the key building blocks above. The full theorem requires
additional infrastructure for constructing compatible valuations.
-/

-- TODO: Full obligation_pure_sound theorem requires:
-- 1. A way to construct σ from ρ (extract integers from HeapValues)
-- 2. Proof that this construction gives compatible valuations
-- 3. Then apply constraintToPureProp_sound

end CerbLean.CN.Semantics
