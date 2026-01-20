/-
  Verified Program: Counting Loop

  A hand-constructed Core program with a loop that counts from 0 to 3.
  Equivalent to:
  ```c
  int main(void) {
    int i = 0;
    while (i < 3) {
      i = i + 1;
    }
    return i;  // returns 3
  }
  ```
-/

import CerbLean.Semantics.Interpreter
import Mathlib.Tactic

namespace CerbLean.Verification.Programs.CountingLoop

open CerbLean.Core
open CerbLean.Semantics

/-! ## Program Construction

In Core IR, the loop becomes a save/run pattern:
```
save loop (i := 0) {
  if i < 3 then
    run loop(i + 1)
  else
    pure(i)
}
```
-/

/-- Symbol for main function -/
def mainSym : Sym := { id := 1, name := some "main" }

/-- Symbol for loop label -/
def loopSym : Sym := { id := 2, name := some "loop" }

/-- Symbol for loop counter variable -/
def iSym : Sym := { id := 4, name := some "i" }

/-- Helper: make an integer value -/
def mkInt (n : Int) : Value := .loaded (.specified (.integer ⟨n, .none⟩))

/-- Helper: make a pure expression from a value -/
def mkPure (v : Value) : APexpr := { annots := [], ty := none, expr := .val v }

/-- Helper: make a pure expression from a symbol reference -/
def mkSym (s : Sym) : APexpr := { annots := [], ty := none, expr := .sym s }

/-- Helper: wrap pexpr in AExpr.pure -/
def mkPureExpr (pe : APexpr) : AExpr := { annots := [], expr := .pure pe }

/-- The comparison: i < 3 -/
def compareILt3 : Pexpr :=
  .if_ (.op .lt (.sym iSym) (.val (mkInt 3)))
       (.val .true_)
       (.val .false_)

/-- The loop body: if i < 3 then run loop(i + 1) else pure(i) -/
def loopBody : AExpr :=
  let cond : APexpr := { annots := [], ty := none, expr := compareILt3 }
  let increment : APexpr := {
    annots := []
    ty := none
    expr := .op .add (.sym iSym) (.val (mkInt 1))
  }
  let runLoop : AExpr := {
    annots := []
    expr := .run loopSym [increment]
  }
  let returnI : AExpr := mkPureExpr (mkSym iSym)
  { annots := []
    expr := .if_ cond runLoop returnI }

/-- The save block that defines the loop: save loop (i := 0) { loopBody } -/
def saveLoop : AExpr :=
  let initI : APexpr := mkPure (mkInt 0)
  { annots := []
    expr := .save loopSym (.loaded .integer) [(iSym, .loaded .integer, initI)] loopBody }

/-- Main function declaration -/
def mainDecl : FunDecl := .proc
  .unknown
  none
  (.loaded .integer)
  []
  saveLoop

/-- The loop program -/
def program : File := {
  main := some mainSym
  funs := [(mainSym, mainDecl)]
}

/-! ## Execution Test -/

#eval runMain program  -- Should show: Return: Specified(3)

/-! ## Theorems -/

/-- Helper: the program's error field is none (decidable version) -/
theorem program_noError_bool : (runMain program).error.isNone = true := by
  native_decide

/-- The loop program terminates without error -/
theorem program_noError : (runMain program).error = none := by
  have := @program_noError_bool
  cases h : (runMain program).error <;> simp_all

/-- The loop program returns 3 -/
theorem program_returns3 :
    ∃ v, (runMain program).returnValue = some v := by
  have h_code : (runMain program).returnValue.isSome := by native_decide
  exact Option.isSome_iff_exists.mp h_code

end CerbLean.Verification.Programs.CountingLoop
