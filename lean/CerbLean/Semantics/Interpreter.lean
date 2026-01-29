/-
  Top-level interpreter entry point
  Corresponds to: cerberus/frontend/model/core_run.lem (run_main setup)

  This file provides the high-level entry point that:
  1. Initializes thread state (initThreadState)
  2. Pre-collects labeled continuations (collectLabeledContinuations)
  3. Runs the step loop (runUntilDone)
-/

import CerbLean.Semantics.Step
import CerbLean.Semantics.Env
import CerbLean.Memory.Layout
import CerbLean.PrettyPrint

namespace CerbLean.Semantics

open CerbLean.Core
open CerbLean.Memory
open CerbLean.PrettyPrint

/-! ## Interpreter Result -/

/-- Result of running a program -/
structure InterpResult where
  /-- Return value (None if crashed/UB) -/
  returnValue : Option Value
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
      | some v => s!"Return: {ppValue v}"
      | none => "No return value"

/-! ## Running Main -/

/-- Extract integer return value from Value -/
def extractReturnInt (v : Value) : Option Int :=
  match v with
  | .object (.integer iv) => some iv.val
  | .loaded (.specified (.integer iv)) => some iv.val
  | _ => none

/-- Check if value is an unspecified loaded value -/
def isUnspecified (v : Value) : Option Ctype :=
  match v with
  | .loaded (.unspecified ty) => some ty
  | _ => none

/-- Allocate errno global variable.
    Corresponds to: driver.lem:1837-1839
    ```lem
    Mem.bind (Mem.allocate_object tid0 (Symbol.PrefOther "errno")
              (Mem.alignof_ival Ctype.signed_int) Ctype.signed_int Nothing Nothing)
    ```
    This happens AFTER global allocation to match Cerberus's memory layout. -/
def allocateErrno : InterpM Unit := do
  let signedInt : Ctype := { ty := .basic (.integer (.signed .int_)) }
  let alignIval := alignofIval (← InterpM.getTypeEnv) signedInt
  let _ ← InterpM.liftMem (MemoryOps.allocateObject "errno" alignIval signedInt none none)
  pure ()

/-- Run the main function of a Core file.
    Corresponds to: driver_globals + driver_main in driver.lem
    Audited: 2026-01-01
    Deviations: Combined global init and main execution

    Steps (matching Cerberus driver.lem):
    1. Initialize global variables (initGlobals) - driver.lem:1541-1618
    2. Allocate errno (allocateErrno) - driver.lem:1837-1839
    3. Initialize thread state with main's body (initThreadState)
    4. Pre-collect labeled continuations (collectLabeledContinuations)
    5. Run step loop until done (runUntilDone)

    The `args` parameter corresponds to the command line arguments passed to the C program.
    Cerberus prepends "cmdname" to args (pipeline.ml:621,625), so we do the same by default. -/
def runMain (file : File) (args : List String := ["cmdname"]) : InterpResult :=
  let typeEnv := TypeEnv.fromFile file
  -- Run initialization and execution in InterpM monad
  let result := runInterpM file typeEnv do
    dbg_trace "INIT: starting globals"
    -- Initialize global variables
    -- Corresponds to: driver_globals in driver.lem:1541-1618
    let globalEnv ← initGlobals file
    dbg_trace "INIT: globals done"
    -- Allocate errno (after globals, before main)
    -- Corresponds to: driver.lem:1837-1839
    allocateErrno
    dbg_trace "INIT: errno allocated"
    -- Initialize thread state with globals (now in InterpM to support argc/argv allocation)
    -- Corresponds to: pipeline.ml:621,625 - "cmdname" :: args
    let st ← initThreadState file globalEnv args
    dbg_trace "INIT: thread state ready"
    -- Pre-collect labeled continuations for all procedures
    -- Corresponds to: collect_labeled_continuations_NEW in core_aux.lem:2379-2395
    let allLabeledConts := collectAllLabeledContinuations file
    dbg_trace s!"INIT: labeled conts collected ({allLabeledConts.size} procs)"
    -- Run step loop until done
    dbg_trace "INIT: starting main loop"
    runUntilDone st file allLabeledConts
  match result with
  | .ok (v, state) =>
    { returnValue := some v
      stdout := state.stdout
      stderr := state.stderr
      error := none }
  | .error e =>
    { returnValue := none
      stdout := ""
      stderr := ""
      error := some e }

/-! ## Differential Testing Support -/

/-- Value status for batch result -/
inductive ValueStatus where
  | specified (v : Int)
  | unspecified (ty : Ctype)
  | other (desc : String)
  deriving Repr, Inhabited

/-- Batch execution result (matches Cerberus --batch output) -/
structure BatchResult where
  /-- Value status (specified int, unspecified, or other) -/
  valueStatus : Option ValueStatus
  /-- Whether undefined behavior was detected -/
  isUB : Bool
  /-- UB description if any -/
  ubDescription : Option String
  deriving Repr, Inhabited

/-- Convert interpreter result to batch result -/
def toBatchResult (r : InterpResult) : BatchResult :=
  match r.error with
  | some (.undefinedBehavior ub _) =>
    { valueStatus := none
      isUB := true
      ubDescription := some (toString ub) }
  | some (.memoryError err) =>
    -- Memory errors are UB in C semantics
    { valueStatus := none
      isUB := true
      ubDescription := some (toString err) }
  | some _ =>
    { valueStatus := none
      isUB := false
      ubDescription := none }
  | none =>
    match r.returnValue with
    | some v =>
      let status := match v with
        | .object (.integer iv) => ValueStatus.specified iv.val
        | .loaded (.specified (.integer iv)) => ValueStatus.specified iv.val
        | .loaded (.unspecified ty) => ValueStatus.unspecified ty
        | _ => ValueStatus.other "non-integer"
      { valueStatus := some status
        isUB := false
        ubDescription := none }
    | none =>
      { valueStatus := none
        isUB := false
        ubDescription := none }

instance : ToString BatchResult where
  toString r :=
    if r.isUB then
      s!"UB: {r.ubDescription.getD "unknown"}"
    else
      match r.valueStatus with
      | some (.specified v) => s!"exit {v}"
      | some (.unspecified _) => "UNSPECIFIED"
      | some (.other _) => "other"
      | none => "void"

end CerbLean.Semantics
