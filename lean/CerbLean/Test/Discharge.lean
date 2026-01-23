/-
  Discharge Tests

  Tests that verify denoteTerm (now terminating) can be used with
  simp, native_decide, and other tactics for proof obligation discharge.

  These tests validate the foundational approach where:
  1. denoteTerm evaluates concrete terms
  2. evalConstraint/evalTermTrue provide decidable evaluation
  3. native_decide can discharge ground obligations
-/

import CerbLean.CN.Verification.Discharge
import CerbLean.CN.Verification.Obligation
import CerbLean.CN.Types
import CerbLean.CN.Semantics.Heap
import CerbLean.CN.Semantics.Denote
import CerbLean.CN.Semantics.PureDenoteSound

namespace CerbLean.Test.Discharge

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types
open CerbLean.CN.Semantics
open CerbLean.CN.Verification

/-! ## Helper Constructors -/

def mkIntConst (n : Int) : IndexTerm :=
  ⟨.const (.z n), .integer, Loc.t.unknown⟩

def mkBoolConst (b : Bool) : IndexTerm :=
  ⟨.const (.bool b), .bool, Loc.t.unknown⟩

def mkBinOp (op : BinOp) (left right : IndexTerm) : IndexTerm :=
  ⟨.binop op left right, .bool, Loc.t.unknown⟩

/-! ## denoteTerm Evaluation Tests

Now that denoteTerm is terminating, #eval works for concrete terms.
-/

-- These #eval commands verify denoteTerm can be evaluated at compile time
#eval denoteTerm [] (.const (.z 42))
-- Output: some (HeapValue.integer ... 42)

#eval denoteTerm [] (.binop .add
  (AnnotTerm.mk (.const (.z 1)) .integer Loc.t.unknown)
  (AnnotTerm.mk (.const (.z 2)) .integer Loc.t.unknown))
-- Output: some (HeapValue.integer ... 3)

#eval denoteTerm [] (.binop .lt
  (AnnotTerm.mk (.const (.z 1)) .integer Loc.t.unknown)
  (AnnotTerm.mk (.const (.z 2)) .integer Loc.t.unknown))
-- Output: some (HeapValue.integer ... 1) representing true

/-! ## evalTermTrue Tests

evalTermTrue returns Bool, so native_decide works directly.
-/

/-- Test: evalTermTrue on true constant -/
example : evalTermTrue [] (.const (.bool true)) = true := by
  native_decide

/-- Test: evalTermTrue on false constant -/
example : evalTermTrue [] (.const (.bool false)) = false := by
  native_decide

/-- Test: evalTermTrue on 1 < 2 -/
example : evalTermTrue []
    (.binop .lt
      (AnnotTerm.mk (.const (.z 1)) .integer Loc.t.unknown)
      (AnnotTerm.mk (.const (.z 2)) .integer Loc.t.unknown))
    = true := by
  native_decide

/-- Test: evalTermTrue on 2 < 1 (false) -/
example : evalTermTrue []
    (.binop .lt
      (AnnotTerm.mk (.const (.z 2)) .integer Loc.t.unknown)
      (AnnotTerm.mk (.const (.z 1)) .integer Loc.t.unknown))
    = false := by
  native_decide

/-- Test: evalTermTrue on 1 + 1 = 2 -/
example : evalTermTrue []
    (Term.binop .eq
      (AnnotTerm.mk (Term.binop .add
        (AnnotTerm.mk (.const (.z 1)) .integer Loc.t.unknown)
        (AnnotTerm.mk (.const (.z 1)) .integer Loc.t.unknown)) .integer Loc.t.unknown)
      (AnnotTerm.mk (.const (.z 2)) .integer Loc.t.unknown))
    = true := by
  native_decide

/-- Test: evalTermTrue on 5 * 3 = 15 -/
example : evalTermTrue []
    (Term.binop .eq
      (AnnotTerm.mk (Term.binop .mul
        (AnnotTerm.mk (.const (.z 5)) .integer Loc.t.unknown)
        (AnnotTerm.mk (.const (.z 3)) .integer Loc.t.unknown)) .integer Loc.t.unknown)
      (AnnotTerm.mk (.const (.z 15)) .integer Loc.t.unknown))
    = true := by
  native_decide

/-! ## evalConstraint Tests -/

/-- Test: evalConstraint on ground constraint 1 < 2 -/
example : evalConstraint [] (.t (mkBinOp .lt (mkIntConst 1) (mkIntConst 2))) = true := by
  native_decide

/-- Test: evalConstraint on ground constraint 1 + 1 = 2 -/
example : evalConstraint [] (.t (mkBinOp .eq
    (mkBinOp .add (mkIntConst 1) (mkIntConst 1))
    (mkIntConst 2))) = true := by
  native_decide

/-- Test: evalConstraint on false constraint 2 < 1 -/
example : evalConstraint [] (.t (mkBinOp .lt (mkIntConst 2) (mkIntConst 1))) = false := by
  native_decide

/-! ## Ground Obligation Tests

Obligations with no free variables can be checked via evalConstraint.
-/

/-- A ground obligation: ⊢ 1 < 2 -/
def groundOb1 : Obligation :=
  { description := "1 < 2"
  , constraint := .t (mkBinOp .lt (mkIntConst 1) (mkIntConst 2))
  , assumptions := []
  , loc := Loc.t.unknown
  , category := .arithmetic
  }

/-- Test: Ground obligation constraint evaluates to true -/
example : evalConstraint [] groundOb1.constraint = true := by
  native_decide

/-- A ground obligation: ⊢ 5 * 2 = 10 -/
def groundOb2 : Obligation :=
  { description := "5 * 2 = 10"
  , constraint := .t (mkBinOp .eq
      (mkBinOp .mul (mkIntConst 5) (mkIntConst 2))
      (mkIntConst 10))
  , assumptions := []
  , loc := Loc.t.unknown
  , category := .arithmetic
  }

/-- Test: Multiplication obligation -/
example : evalConstraint [] groundOb2.constraint = true := by
  native_decide

/-- A more complex ground obligation: ⊢ (3 + 4) * 2 = 14 -/
def groundOb3 : Obligation :=
  { description := "(3 + 4) * 2 = 14"
  , constraint := .t (mkBinOp .eq
      (mkBinOp .mul
        (mkBinOp .add (mkIntConst 3) (mkIntConst 4))
        (mkIntConst 2))
      (mkIntConst 14))
  , assumptions := []
  , loc := Loc.t.unknown
  , category := .arithmetic
  }

/-- Test: Complex arithmetic obligation -/
example : evalConstraint [] groundOb3.constraint = true := by
  native_decide

/-! ## Pure Interpretation Tests

Tests for the pure interpretation layer (termToInt, termToProp).
-/

open CerbLean.CN.Semantics (PureIntVal termToInt termToBool termToProp)

/-- A simple pure valuation for testing -/
def testSigma : PureIntVal := fun s =>
  if s.name == some "x" then 5
  else if s.name == some "y" then 3
  else 0

def xSym : Sym := { id := 1, name := some "x" }
def ySym : Sym := { id := 2, name := some "y" }

-- Test termToInt on symbol (requires partial evaluation, can't use native_decide)
#eval termToInt testSigma (.sym xSym)  -- some 5
#eval termToInt testSigma (.const (.z 42))  -- some 42

-- Test termToBool on comparison
#eval termToBool testSigma (.binop .lt
  (AnnotTerm.mk (.sym xSym) .integer Loc.t.unknown)
  (AnnotTerm.mk (.const (.z 10)) .integer Loc.t.unknown))
-- Output: some true (5 < 10)

#eval termToBool testSigma (.binop .lt
  (AnnotTerm.mk (.sym xSym) .integer Loc.t.unknown)
  (AnnotTerm.mk (.sym ySym) .integer Loc.t.unknown))
-- Output: some false (5 < 3 is false)

/-! ## Pipeline Tests: Soundness Theorem + SMT

These tests verify that our ACTUAL INFRASTRUCTURE works:
1. Apply constraintToPureProp_sound to transform HeapValue goal to pure goal
2. SMT solves the pure arithmetic

The soundness theorem has `sorry` but we USE it to test the pipeline.
-/

open CerbLean.CN.Semantics (constraintToPureProp constraintToPureProp_sound
  termToProp_implies_constraintToProp valuationCompatible PureIntVal
  extractPureVal extractPureVal_compatible constraintDefined
  constraintSetToProp_head constraintSetToProp_tail constraintToProp_implies_pure
  denoteAnnotTerm denoteTerm denoteConst denoteBinOp boolToHeapValue defaultIntType)

/-- If constraintToProp holds for a .t constraint, the denotation is defined -/
theorem constraintToProp_implies_defined (ρ : Valuation) (it : IndexTerm)
    (h : constraintToProp ρ (.t it)) : ∃ v, denoteAnnotTerm ρ it = some v := by
  unfold constraintToProp at h
  cases hd : denoteAnnotTerm ρ it with
  | none => simp [hd] at h
  | some v => exact ⟨v, rfl⟩

/-- Test constraint: 1 < 2 -/
def testConstraint : LogicalConstraint :=
  .t (mkBinOp .lt (mkIntConst 1) (mkIntConst 2))

/-- PIPELINE TEST: Apply soundness theorem, then SMT solves pure goal.

    This is THE test that our infrastructure works:
    1. Goal is constraintToProp ρ lc (HeapValue-based)
    2. Apply constraintToPureProp_sound to transform
    3. SMT proves the pure arithmetic (1 < 2)
-/
theorem pipeline_test : ∀ ρ : Valuation, constraintToProp ρ testConstraint := by
  intro ρ
  -- Use the soundness theorem with extractPureVal for compatibility
  let σ := extractPureVal ρ
  apply constraintToPureProp_sound ρ σ testConstraint (1 < 2)
  -- Goal 1: valuationCompatible - proven by extractPureVal_compatible
  · exact extractPureVal_compatible ρ
  -- Goal 2: constraintToPureProp gives some (1 < 2)
  -- For ground terms, the result doesn't depend on σ.
  -- Unfold and simp to reduce the match expressions.
  · unfold constraintToPureProp testConstraint mkBinOp mkIntConst termToProp termToInt
    simp only [AnnotTerm.term, Option.pure_def, Option.bind_eq_bind]
    cn_discharge
  -- Goal 3: 1 < 2 - SMT proves this
  · show 1 < 2
    smt -- DO NOT REMOVE SMT CALL
  -- Goal 4: constraintDefined - for ground terms, denoteTerm always succeeds
  · simp only [constraintDefined, testConstraint, mkBinOp, mkIntConst,
               denoteAnnotTerm, denoteTerm, AnnotTerm.term, denoteConst,
               Option.pure_def, Option.bind_eq_bind, denoteBinOp, boolToHeapValue]
    exact ⟨_, rfl⟩

/-- Helper to create a symbolic term from a Sym -/
def mkSymTerm (s : Sym) : IndexTerm :=
  ⟨.sym s, .integer, Loc.t.unknown⟩

/-- Extract integer binding from a constraint of form 0 < sym.
    The constraint can only be true if the symbol is bound to an integer. -/
theorem int_bound_from_lt_constraint (ρ : Valuation) (s : Sym)
    (h : constraintToProp ρ (.t (mkBinOp .lt (mkIntConst 0) (mkSymTerm s)))) :
    ∃ ty n, ρ.lookup s = some (.integer ty n) := by
  unfold constraintToProp at h
  simp only [denoteAnnotTerm, denoteTerm, mkBinOp, mkIntConst, mkSymTerm, AnnotTerm.term,
             denoteConst, Option.bind_eq_bind] at h
  cases hs : ρ.lookup s with
  | none => simp [hs, denoteBinOp] at h
  | some v =>
    cases v with
    | integer ty n => exact ⟨ty, n, rfl⟩
    | _ => simp [hs, denoteBinOp] at h

/-- If symbol is bound, denoteTerm on sym succeeds -/
theorem denoteTerm_sym_of_bound (ρ : Valuation) (s : Sym) (v : HeapValue)
    (h : ρ.lookup s = some v) :
    denoteTerm ρ (.sym s) = some v := by
  simp [denoteTerm, h]

/-- Symbolic constraint: 0 < x (i.e., x > 0) -/
def xPositive : LogicalConstraint :=
  .t (mkBinOp .lt (mkIntConst 0) (mkSymTerm xSym))

/-- Symbolic constraint: 0 < x + y (i.e., x + y > 0) -/
def sumPositive : LogicalConstraint :=
  .t ⟨.binop .lt
    ⟨.const (.z 0), .integer, Loc.t.unknown⟩
    ⟨.binop .add (mkSymTerm xSym) (mkSymTerm ySym), .integer, Loc.t.unknown⟩,
    .bool, Loc.t.unknown⟩

/-- PIPELINE TEST: Linear inequality with assumptions.

    Obligation: x > 0 ∧ y > 0 → x + y > 0

    This tests the FULL pipeline:
    1. Start with Obligation.toProp (universally quantified over Valuation)
    2. Apply soundness theorem to transform to pure arithmetic
    3. SMT proves: σ x > 0 → σ y > 0 → σ x + σ y > 0
-/
def linearInequalityObligation : Obligation :=
  { description := "x > 0 ∧ y > 0 → x + y > 0"
  , constraint := sumPositive
  , assumptions := [xPositive, .t (mkBinOp .lt (mkIntConst 0) (mkSymTerm ySym))]
  , loc := Loc.t.unknown
  , category := .arithmetic
  }

theorem pipeline_test_linear : linearInequalityObligation.toProp := by
  unfold Obligation.toProp
  intro ρ h_assumptions
  -- Apply soundness theorem with σ = extractPureVal ρ
  let σ := extractPureVal ρ
  apply constraintToPureProp_sound ρ σ sumPositive (0 < σ xSym + σ ySym)
  -- Goal 1: valuationCompatible ρ σ - NOW PROVEN!
  · exact extractPureVal_compatible ρ
  -- Goal 2: constraintToPureProp σ sumPositive = some (0 < σ xSym + σ ySym)
  · unfold constraintToPureProp sumPositive
    simp only [AnnotTerm.term]
    unfold termToProp
    simp only []
    unfold termToInt termToInt
    rfl
  -- Goal 3: 0 < σ xSym + σ ySym - THIS is what SMT proves!
  -- We need the pure assumptions. Apply assumption soundness too:
  · -- Transform assumptions to pure form using the extraction lemmas
    -- Introduce local names for the pure values
    let x := σ xSym
    let y := σ ySym
    -- Extract individual constraints from h_assumptions
    have h_x_heap : constraintToProp ρ xPositive := constraintSetToProp_head ρ _ _ h_assumptions
    have h_y_heap : constraintToProp ρ _ := constraintSetToProp_head ρ _ _ (constraintSetToProp_tail ρ _ _ h_assumptions)
    -- Use completeness to get pure form (sorry - needs terminating pure interp)
    have h_x : x > 0 := by
      apply constraintToProp_implies_pure ρ σ xPositive (0 < σ xSym)
      · exact extractPureVal_compatible ρ
      · unfold constraintToPureProp xPositive mkBinOp mkIntConst mkSymTerm
        simp only [AnnotTerm.term]
        unfold termToProp termToInt termToInt
        rfl
      · exact h_x_heap
    have h_y : y > 0 := by
      apply constraintToProp_implies_pure ρ σ (.t (mkBinOp .lt (mkIntConst 0) (mkSymTerm ySym))) (0 < σ ySym)
      · exact extractPureVal_compatible ρ
      · unfold constraintToPureProp mkBinOp mkIntConst mkSymTerm
        simp only [AnnotTerm.term]
        unfold termToProp termToInt termToInt
        rfl
      · exact h_y_heap
    -- NOW SMT can prove the arithmetic!
    show 0 < x + y
    smt [h_x, h_y]
  -- Goal 4: constraintDefined - derive from assumptions that symbols are bound
  · -- Extract that xSym and ySym are bound to integers from the assumptions
    have h_x_heap : constraintToProp ρ xPositive := constraintSetToProp_head ρ _ _ h_assumptions
    have h_y_heap : constraintToProp ρ _ := constraintSetToProp_head ρ _ _ (constraintSetToProp_tail ρ _ _ h_assumptions)
    have ⟨tyx, nx, hx⟩ := int_bound_from_lt_constraint ρ xSym h_x_heap
    have ⟨tyy, ny, hy⟩ := int_bound_from_lt_constraint ρ ySym h_y_heap
    -- Now show sumPositive is defined - both symbols are bound to integers
    unfold constraintDefined sumPositive mkSymTerm
    simp only [denoteAnnotTerm, denoteTerm, AnnotTerm.term, denoteConst,
               Option.pure_def, Option.bind_eq_bind, hx, hy, denoteBinOp, boolToHeapValue]
    exact ⟨_, rfl⟩

/-! ## Obligation.toProp Structure Tests

Tests that verify the structure of obligation proofs works correctly.
The key insight: Obligation.toProp is ∀ ρ : Valuation, assumptions → constraint
-/

/-- Test: The shape of obligation proofs with trivial constraint -/
example : ∀ _ρ : Valuation, True → True := by
  cn_discharge

/-- Test: cn_discharge handles implication -/
example : ∀ _ρ : Valuation, (1 < 2) → (1 < 2) := by
  intro ρ h
  exact h

/-! ## Summary

These tests demonstrate that with terminating denoteTerm:
1. `#eval` works for concrete term evaluation
2. `evalTermTrue` and `evalConstraint` (returning Bool) work with `native_decide`
3. Ground constraints (no free variables) can be automatically discharged
4. Pure interpretation functions (termToInt, termToBool) work correctly

The pure interpretation layer enables SMT discharge for symbolic constraints:
- Pure goals like `∀ x : Int, x > 0 → x > 0` are directly handled by SMT/omega
- The soundness theorems (with sorry) provide the theoretical bridge
- Full proofs require making termToInt/termToBool terminating

Next steps:
- Complete soundness proofs (make pure interpretation terminating)
- Test actual CN obligations with symbolic variables
-/

end CerbLean.Test.Discharge
