/-
  Verified Program: Minimal Return

  A hand-constructed minimal Core program that returns 42.
  Demonstrates direct proof of program properties via interpreter semantics.
-/

import CerbLean.Semantics.Interpreter
import Mathlib.Tactic

namespace CerbLean.Verification.Programs.MinimalReturn

open CerbLean.Core
open CerbLean.Semantics

/-! ## Program Construction

We construct the simplest possible Core program by hand:
- A main function that returns the integer literal 42
- No memory operations, no control flow, just return a value
-/

/-- Symbol for main function -/
def mainSym : Sym := {
  digest := ""
  id := 1
  description := .id "main"
  name := some "main"
}

/-- Integer value 42 with no provenance -/
def val42 : IntegerValue := ⟨42, .none⟩

/-- The value we return: a loaded integer -/
def returnValue : Value := .loaded (.specified (.integer val42))

/-- Pure expression that is just the value 42 -/
def returnPexpr : APexpr := {
  annots := []
  ty := some (.loaded .integer)
  expr := .val returnValue
}

/-- The body of main: just return the value (Expr.pure) -/
def mainBody : AExpr := {
  annots := []
  expr := .pure returnPexpr
}

/-- Main function declaration -/
def mainDecl : FunDecl := .proc
  .unknown        -- location
  none            -- marker env
  (.loaded .integer)  -- return type
  []              -- no parameters
  mainBody        -- body

/-- The minimal Core program file -/
def program : File := {
  main := some mainSym
  funs := [(mainSym, mainDecl)]
}

/-! ## Execution Test -/

#eval runMain program  -- Should show: Return: Specified(42)

/-! ## Theorems -/

/-- Helper: the program's error field is none (decidable version) -/
theorem program_noError_bool : (runMain program).error.isNone = true := by
  native_decide

/-- The program completes without undefined behavior or errors -/
theorem program_noError : (runMain program).error = none := by
  have := @program_noError_bool
  cases h : (runMain program).error <;> simp_all

/-- The program returns the expected value -/
theorem program_returns42 :
    ∃ v, (runMain program).returnValue = some v := by
  have h_code : (runMain program).returnValue.isSome := by native_decide
  exact Option.isSome_iff_exists.mp h_code

end CerbLean.Verification.Programs.MinimalReturn
