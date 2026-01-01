/-
  Top-level interpreter entry point
  Based on cerberus/frontend/model/core_run.lem
-/

import CToLean.Semantics.Exec
import CToLean.Memory.Layout

namespace CToLean.Semantics

open CToLean.Core
open CToLean.Memory

/-! ## Interpreter Result -/

/-- Result of running a program -/
structure InterpResult where
  /-- Return value (None if crashed/UB) -/
  returnValue : Option Int
  /-- Captured stdout -/
  stdout : String
  /-- Captured stderr -/
  stderr : String
  /-- Error if any -/
  error : Option InterpError
  deriving Inhabited

instance : ToString InterpResult where
  toString r :=
    match r.error with
    | some e => s!"Error: {e}"
    | none =>
      match r.returnValue with
      | some v => s!"Return: {v}"
      | none => "No return value"

/-! ## Running Main -/

/-- Extract integer return value from Value -/
def extractReturnInt (v : Value) : Option Int :=
  match v with
  | .object (.integer iv) => some iv.val
  | .loaded (.specified (.integer iv)) => some iv.val
  | _ => none

/-- Run the main function of a Core file -/
def runMain (file : File) : InterpResult :=
  match file.main with
  | none =>
    { returnValue := none
      stdout := ""
      stderr := ""
      error := some (.illformedProgram "no main function") }
  | some mainSym =>
    let typeEnv := TypeEnv.fromFile file
    let result := runInterpM file typeEnv do
      -- Find main function
      let mainDecl := file.funs.find? fun (s, _) => s == mainSym
      match mainDecl with
      | some (_, .proc _loc _retTy _params body) =>
        -- Pre-collect labeled continuations and execute main body
        let env := EvalEnv.empty.withConts body
        execExpr env body
      | some (_, .fun_ _retTy _params body) =>
        -- Pure main (unusual but possible)
        evalPexpr EvalEnv.empty body
      | _ =>
        InterpM.throwIllformed s!"main is not a procedure: {mainSym.name}"

    match result with
    | .ok (v, state) =>
      { returnValue := extractReturnInt v
        stdout := state.stdout
        stderr := state.stderr
        error := none }
    | .error (.returnFromSave _label args) =>
      -- Return via save/run mechanism - extract return value from args
      let retVal := match args with
        | [v] => extractReturnInt v
        | _ => none
      { returnValue := retVal
        stdout := ""
        stderr := ""
        error := none }
    | .error e =>
      { returnValue := none
        stdout := ""
        stderr := ""
        error := some e }

/-! ## Differential Testing Support -/

/-- Batch execution result (matches Cerberus --batch output) -/
structure BatchResult where
  /-- Exit code (return value or signal) -/
  exitCode : Int
  /-- Whether undefined behavior was detected -/
  isUB : Bool
  /-- UB description if any -/
  ubDescription : Option String
  deriving Repr, Inhabited

/-- Convert interpreter result to batch result -/
def toBatchResult (r : InterpResult) : BatchResult :=
  match r.error with
  | some (.undefinedBehavior ub _) =>
    { exitCode := -1
      isUB := true
      ubDescription := some (toString ub) }
  | some _ =>
    { exitCode := -1
      isUB := false
      ubDescription := none }
  | none =>
    { exitCode := r.returnValue.getD 0
      isUB := false
      ubDescription := none }

instance : ToString BatchResult where
  toString r :=
    if r.isUB then
      s!"UB: {r.ubDescription.getD "unknown"}"
    else
      s!"exit {r.exitCode}"

end CToLean.Semantics
