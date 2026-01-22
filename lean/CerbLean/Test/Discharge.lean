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

/-! ## Summary

These tests demonstrate that with terminating denoteTerm:
1. `#eval` works for concrete term evaluation
2. `evalTermTrue` and `evalConstraint` (returning Bool) work with `native_decide`
3. Ground constraints (no free variables) can be automatically discharged

Note: `native_decide` on `denoteTerm ... = some v` requires `DecidableEq HeapValue`,
which isn't derived due to the recursive structure. Use `evalTermTrue`/`evalConstraint`
for decidable checking instead.

TODO: For symbolic constraints, we need reflection lemmas that bridge
`evalConstraint ρ lc = true` to `constraintToProp ρ lc`, enabling SMT integration.
-/

end CerbLean.Test.Discharge
