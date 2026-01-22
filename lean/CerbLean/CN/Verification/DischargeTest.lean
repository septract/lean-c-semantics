/-
  Discharge Test Module

  This module documents the challenges with discharging CN proof obligations
  and establishes what approaches work.

  ## Key Finding: `denoteTerm` is Partial

  The function `denoteTerm` is declared `partial` because it's recursive on
  deeply nested terms. This has important consequences:

  1. `simp` cannot unfold `denoteTerm`
  2. `native_decide` cannot evaluate expressions involving `denoteTerm`
  3. `decide` requires the goal to be a closed decidable term

  ## Approaches That Work

  1. **Assumption-based proofs**: When the constraint matches an assumption,
     we can use the assumption directly without evaluating `denoteTerm`.

  2. **Reflection lemmas**: We can prove lemmas of the form
     `evalConstraint ρ lc = true → constraintToProp ρ lc`
     and use them to bridge decidable evaluation to Props.

  3. **Manual unfolding**: For specific concrete terms, we can write
     lemmas that expand the definition manually.

  ## What Needs More Work

  For automatic discharge with `native_decide` or SMT, we would need:
  - Either: Make `denoteTerm` terminating (well-founded recursion)
  - Or: Use reflection/metaprogramming to generate proofs

  For now, the soundness proof will use assumption-based reasoning and
  manual lemmas for specific constraint patterns.
-/

import CerbLean.CN.Verification.Discharge
import CerbLean.CN.Verification.Obligation
import CerbLean.CN.Types
import CerbLean.CN.Semantics.Heap
import CerbLean.CN.Semantics.Denote

namespace CerbLean.CN.Verification.DischargeTest

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types
open CerbLean.CN.Semantics
open CerbLean.CN.Verification

/-! ## Building Concrete Terms -/

def mkSym (name : String) (id : Nat := 0) : Sym :=
  { id := id, name := some name }

def mkIntConst (n : Int) : IndexTerm :=
  ⟨.const (.z n), .integer, Loc.t.unknown⟩

def mkBoolConst (b : Bool) : IndexTerm :=
  ⟨.const (.bool b), .bool, Loc.t.unknown⟩

def mkSymTerm (s : Sym) (bt : BaseType := .integer) : IndexTerm :=
  ⟨.sym s, bt, Loc.t.unknown⟩

def mkBinOp (op : BinOp) (left right : IndexTerm) : IndexTerm :=
  ⟨.binop op left right, .bool, Loc.t.unknown⟩

def mkEq (left right : IndexTerm) : IndexTerm :=
  mkBinOp .eq left right

def mkGt (left right : IndexTerm) : IndexTerm :=
  mkBinOp .lt right left

/-! ## Symbolic Constraint Tests

These tests show that assumption-based proofs work correctly.
-/

def xSym : Sym := mkSym "x" 1
def ySym : Sym := mkSym "y" 2

/-- Obligation with assumption: x > 0 ⊢ x > 0 -/
def obWithAssumption : Obligation :=
  { description := "x > 0 implies x > 0"
  , constraint := .t (mkGt (mkSymTerm xSym) (mkIntConst 0))
  , assumptions := [.t (mkGt (mkSymTerm xSym) (mkIntConst 0))]
  , loc := Loc.t.unknown
  , category := .arithmetic
  }

/-- Test: When constraint matches assumption, proof is direct -/
theorem obWithAssumption_holds : obWithAssumption.toProp := by
  unfold Obligation.toProp constraintSetToProp obWithAssumption
  intro ρ h_assumptions
  -- The assumption gives us exactly what we need
  exact h_assumptions _ (List.mem_singleton.mpr rfl)

/-- Obligation with multiple assumptions: x > 0, y > 0 ⊢ x > 0 -/
def obMultipleAssumptions : Obligation :=
  { description := "x > 0, y > 0 implies x > 0"
  , constraint := .t (mkGt (mkSymTerm xSym) (mkIntConst 0))
  , assumptions := [.t (mkGt (mkSymTerm xSym) (mkIntConst 0)),
                    .t (mkGt (mkSymTerm ySym) (mkIntConst 0))]
  , loc := Loc.t.unknown
  , category := .arithmetic
  }

/-- Test: Can select the right assumption from a list -/
theorem obMultipleAssumptions_holds : obMultipleAssumptions.toProp := by
  unfold Obligation.toProp constraintSetToProp obMultipleAssumptions
  intro ρ h_assumptions
  apply h_assumptions
  simp only [List.mem_cons]
  left
  trivial

/-! ## cn_discharge Tests

Test that the tactic handles these patterns.
-/

/-- cn_discharge works for trivial True -/
theorem test_cn_discharge_trivial : True := by
  cn_discharge

/-- cn_discharge works for reflexive equality -/
theorem test_cn_discharge_rfl : (42 : Int) = 42 := by
  cn_discharge

/-- cn_discharge works when goal matches assumption -/
theorem test_cn_discharge_assumption (P : Prop) (h : P) : P := by
  cn_discharge

/-! ## Key Insight: Obligation Discharge Strategy

For the soundness proof, obligations fall into two categories:

1. **Identity obligations**: constraint matches an assumption
   - Discharge: Use the assumption directly
   - Example: x > 0 ⊢ x > 0

2. **Derivable obligations**: constraint follows from assumptions
   - Discharge: Need SMT or manual proof
   - Example: x > 0, y > 0 ⊢ x + y > 0

The current `cn_discharge` handles category 1 via `assumption`.
Category 2 would benefit from SMT, but requires bridging the
`denoteTerm` evaluation to arithmetic constraints.
-/

/-! ## Future Work

To enable automatic SMT discharge:

1. **Terminating denoteTerm**: Rewrite `denoteTerm` with well-founded recursion
   so it can be unfolded by simp/native_decide.

2. **Reflection**: Create a reflection framework that:
   - Quotes the constraint to a decidable form
   - Evaluates it
   - Reflects the result back to a proof

3. **SMT-friendly representation**: Instead of `Obligation.toProp` which
   quantifies over `Valuation`, create an SMT-friendly form that extracts
   just the arithmetic constraints.

For now, the soundness proof will proceed with manual proofs for
specific constraint patterns.
-/

end CerbLean.CN.Verification.DischargeTest
