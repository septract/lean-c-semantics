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
    | integer ty n => simp
    | _ => trivial

/-! ## Integer Soundness

termToInt matches denoteTerm for integer results.

Note: The `termToInt`, `termToBool`, and `termToProp` functions are now
terminating (well-founded recursion on sizeOf). The soundness theorems
below still use `sorry` because proving the correspondence between pure
interpretation and HeapValue interpretation requires careful induction
on the term structure.
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
    If termToInt succeeds with value n, AND denoteTerm succeeds,
    then denoteTerm gives an integer with that value.

    The precondition h_defined is necessary because termToInt can succeed
    even when denoteTerm fails (e.g., for symbols not bound in ρ but with
    values in σ).

    TODO: Proof by induction on term structure. -/
theorem termToInt_matches_denoteTerm
    (ρ : Valuation) (σ : PureIntVal) (t : Term) (n : Int)
    (h_compat : valuationCompatible ρ σ)
    (h_pure : termToInt σ t = some n)
    (h_defined : ∃ v, denoteTerm ρ t = some v) :
    ∃ ty, denoteTerm ρ t = some (.integer ty n) := by
  sorry

/-! ## Boolean/Prop Soundness

termToProp matches constraintToProp.
-/

/-- If termToProp gives P, and P holds, AND the HeapValue denotation succeeds,
    then constraintToProp (.t term) holds.

    The precondition h_defined is necessary because termToProp can succeed
    even when denoteAnnotTerm fails (e.g., for terms with symbols not bound in ρ).
    In practice, this precondition is satisfied when we have assumptions about
    the symbols appearing in the term. -/
theorem termToProp_implies_constraintToProp
    (ρ : Valuation) (σ : PureIntVal) (it : IndexTerm) (P : Prop)
    (h_compat : valuationCompatible ρ σ)
    (h_pure : termToProp σ it.term = some P)
    (h_P : P)
    (h_defined : ∃ v, denoteAnnotTerm ρ it = some v) :
    constraintToProp ρ (.t it) := by
  sorry  -- TODO: induction on term structure

/-! ## Main Soundness Theorem

The key theorem for SMT discharge.
-/

/-- Predicate: a constraint's HeapValue denotation is well-defined.
    For .t constraints: the term can be evaluated.
    For forall_ constraints: all instantiations can be evaluated. -/
def constraintDefined (ρ : Valuation) : LogicalConstraint → Prop
  | .t it => ∃ v, denoteAnnotTerm ρ it = some v
  | .forall_ (x, _) body =>
    ∀ v : HeapValue, ∃ hv, denoteAnnotTerm ((x, v) :: ρ) body = some hv

/-- Pure constraint soundness: if pure interpretation holds, HeapValue interpretation holds.

    The precondition h_defined ensures that the HeapValue denotation succeeds.
    This is necessary because the pure interpretation can succeed even when
    the HeapValue interpretation fails (due to unbound symbols). -/
theorem constraintToPureProp_sound
    (ρ : Valuation) (σ : PureIntVal) (lc : LogicalConstraint) (P : Prop)
    (h_compat : valuationCompatible ρ σ)
    (h_pure : constraintToPureProp σ lc = some P)
    (h_P : P)
    (h_defined : constraintDefined ρ lc) :
    constraintToProp ρ lc := by
  cases lc with
  | t it =>
    -- For .t case, use termToProp_implies_constraintToProp
    simp only [constraintToPureProp] at h_pure
    exact termToProp_implies_constraintToProp ρ σ it P h_compat h_pure h_P h_defined
  | forall_ binding body =>
    -- For forall case, need to show universal holds
    sorry  -- TODO: handle forall case

/-- Predicate: all constraints in a set are well-defined -/
def constraintSetDefined (ρ : Valuation) (lcs : LCSet) : Prop :=
  ∀ lc ∈ lcs, constraintDefined ρ lc

/-- Constraint set soundness -/
theorem constraintSetToPureProp_sound
    (ρ : Valuation) (σ : PureIntVal) (lcs : LCSet) (P : Prop)
    (h_compat : valuationCompatible ρ σ)
    (h_pure : constraintSetToPureProp σ lcs = some P)
    (h_P : P)
    (h_defined : constraintSetDefined ρ lcs) :
    constraintSetToProp ρ lcs := by
  sorry  -- TODO: induction on list

/-! ## Constraint Set Decomposition

Lemmas for extracting individual constraints from a constraint set.
-/

/-- Extract head constraint from a non-empty set -/
theorem constraintSetToProp_cons (ρ : Valuation) (lc : LogicalConstraint) (rest : LCSet)
    (h : constraintSetToProp ρ (lc :: rest)) :
    constraintToProp ρ lc ∧ constraintSetToProp ρ rest := by
  unfold constraintSetToProp at h
  simp at h
  exact h

/-- Get head constraint -/
theorem constraintSetToProp_head (ρ : Valuation) (lc : LogicalConstraint) (rest : LCSet)
    (h : constraintSetToProp ρ (lc :: rest)) :
    constraintToProp ρ lc :=
  (constraintSetToProp_cons ρ lc rest h).1

/-- Get tail constraints -/
theorem constraintSetToProp_tail (ρ : Valuation) (lc : LogicalConstraint) (rest : LCSet)
    (h : constraintSetToProp ρ (lc :: rest)) :
    constraintSetToProp ρ rest :=
  (constraintSetToProp_cons ρ lc rest h).2

/-! ## Completeness Direction (constraintToProp → pure)

For extracting pure assumptions from HeapValue assumptions.
This is the reverse direction of soundness.
-/

/-- Completeness: if HeapValue constraint holds, and pure interpretation succeeds,
    then the pure prop holds.

    Note: This requires the constraint to be "well-formed" (evaluates successfully). -/
theorem constraintToProp_implies_pure
    (ρ : Valuation) (σ : PureIntVal) (lc : LogicalConstraint) (P : Prop)
    (h_compat : valuationCompatible ρ σ)
    (h_pure : constraintToPureProp σ lc = some P)
    (h_constraint : constraintToProp ρ lc) :
    P := by
  sorry  -- TODO: requires showing pure interp matches HeapValue interp

/-! ## Obligation Soundness

Connect to Obligation.pureToProp and Obligation.toProp.

The key theorem: If we can prove the pure version of an obligation (which SMT can handle),
then the HeapValue version holds.
-/

/-- Key soundness theorem: pure version implies HeapValue version.

    This is the bridge that allows SMT to prove obligations:
    1. SMT proves ob.pureToProp (pure arithmetic over Sym → Int)
    2. We apply this theorem to get ob.toProp (HeapValue semantics)

    The proof strategy:
    1. Given any ρ : Valuation and h_assumptions : constraintSetToProp ρ assumptions
    2. Extract σ = extractPureVal ρ (compatible pure valuation)
    3. Use completeness to show pure assumptions hold for σ
    4. Apply h_pure with σ to get pure constraint holds
    5. Use soundness to get HeapValue constraint holds

    Note: This theorem has a sorry because the underlying soundness/completeness
    theorems (constraintToPureProp_sound, constraintToProp_implies_pure) have sorries.
    The proof structure is correct; completing this requires completing those. -/
theorem Obligation.toProp_of_pureToProp (ob : Obligation)
    (h_pure : ob.pureToProp) : ob.toProp := by
  intro ρ h_assumptions
  -- Extract the pure valuation from ρ
  let σ := extractPureVal ρ
  have h_compat := extractPureVal_compatible ρ
  -- Apply the pure implication
  have h_pure_applied := h_pure σ
  -- We need to show: constraintToProp ρ ob.constraint
  -- From h_pure_applied, if we can show the pure assumptions hold, we get pure constraint
  -- Then we use soundness to get HeapValue constraint
  --
  -- The key steps:
  -- 1. h_assumptions gives us: constraintSetToProp ρ ob.assumptions
  -- 2. Use completeness to get: match constraintSetToPureProp σ ob.assumptions with some P => P
  -- 3. Apply h_pure_applied to get: match constraintToPureProp σ ob.constraint with some Q => Q
  -- 4. Use soundness to get: constraintToProp ρ ob.constraint
  sorry  -- Requires completing the soundness/completeness proofs

end CerbLean.CN.Semantics
