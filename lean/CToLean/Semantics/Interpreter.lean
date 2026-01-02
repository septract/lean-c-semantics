/-
  Top-level interpreter entry point
  Corresponds to: cerberus/frontend/model/core_run.lem (run_main setup)

  This file provides the high-level entry point that:
  1. Initializes thread state (initThreadState)
  2. Pre-collects labeled continuations (collectLabeledContinuations)
  3. Runs the step loop (runUntilDone)
-/

import CToLean.Semantics.Step
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

/-- Run the main function of a Core file.
    Corresponds to: driver_globals + driver_main in driver.lem
    Audited: 2026-01-01
    Deviations: Combined global init and main execution

    Steps (matching Cerberus driver.lem):
    1. Initialize global variables (initGlobals) - driver.lem:1541-1618
    2. Initialize thread state with main's body (initThreadState)
    3. Pre-collect labeled continuations (collectLabeledContinuations)
    4. Run step loop until done (runUntilDone) -/
def runMain (file : File) : InterpResult :=
  let typeEnv := TypeEnv.fromFile file
  -- Run initialization and execution in InterpM monad
  let result := runInterpM file typeEnv do
    -- Initialize global variables first
    -- Corresponds to: driver_globals in driver.lem:1541-1618
    let globalEnv ← initGlobals file
    -- Initialize thread state with globals
    match initThreadState file globalEnv with
    | .error e => throw e
    | .ok st =>
      -- Pre-collect labeled continuations from main body
      let labeledConts := collectLabeledContinuations st.arena
      -- Run step loop until done
      runUntilDone st file labeledConts
  match result with
  | .ok (v, state) =>
    { returnValue := extractReturnInt v
      stdout := state.stdout
      stderr := state.stderr
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
