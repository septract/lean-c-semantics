/-
  Interpreter test executable
-/

import CerbLean.Parser
import CerbLean.Semantics
import CerbLean.Memory
import CerbLean.PrettyPrint

open CerbLean.Core
open CerbLean.Parser
open CerbLean.Semantics
open CerbLean.Memory
open CerbLean.PrettyPrint

/-- Convert UndefinedBehavior to its canonical code string (matching Cerberus).
    Delegates to UndefinedBehavior.toString which has the canonical bimap strings. -/
def ubToCode (ub : UndefinedBehavior) : String := ub.toString

/-- Convert memory errors to UB codes (matching Cerberus UB categories) -/
def memErrorToUBCode : MemError → String
  | .access .nullPtr _ => "UB043_indirection_invalid_value"  -- null pointer deref
  | .access .functionPtr _ => "UB043_indirection_invalid_value"
  | .access .deadPtr _ => "UB010_pointer_to_dead_object"
  | .access .outOfBoundPtr _ => "UB_CERB002a_out_of_bound_load"
  | .access .noProvPtr _ => "UB043_indirection_invalid_value"
  | .access .atomicMemberof _ => "UB042_access_atomic_structUnion_member"
  | .free .nonMatching => "UB179a_non_matching_allocation_free"
  | .free .deadAllocation => "UB179b_dead_allocation_free"
  | .free .outOfBound => "UB_CERB002c_out_of_bound_free"
  | .memcpy .overlap => "UB_memcpy_overlap"
  | .memcpy .nonObject => "UB_memcpy_non_object"
  | .memcpy .deadObject => "UB010_pointer_to_dead_object"
  | .memcpy .outOfBound => "UB_CERB002a_out_of_bound_load"
  | .readonlyWrite .stringLiteral => "UB033_modifying_string_literal"
  | .readonlyWrite .temporaryLifetime => "UB_modifying_temporary_lifetime"
  | .readonlyWrite .constQualified => "UB064_modifying_const"
  | .uninitRead _ => "UB011_use_indeterminate_automatic"
  | .trapRepresentation .read => "UB012_lvalue_read_trap_representation"
  | .trapRepresentation .write => "UB013_lvalue_sideeffect_trap"
  | .outsideLifetime _ => "UB009_outside_lifetime"
  | .typeError _ => "UB_internal_type_error"
  | .ptrArithOverflow => "UB046_array_pointer_outside"
  | .alignmentError _ _ => "UB025_misaligned_pointer_conversion"
  | .ptrdiff => "UB050_pointers_subtraction_not_representable"
  | .ptrdiffDisjoint => "UB048_disjoint_array_pointers_subtraction"
  | .intFromPtr => "UB024_out_of_range_pointer_to_integer_conversion"
  | .arrayShift => "UB046_array_pointer_outside"
  | .ptrComparison => "UB053_pointer_comparison"
  | .other msg => s!"UB_other({msg})"

/-- Parse a space-separated args string into a list, prepending "cmdname".
    Matches Cerberus behavior in pipeline.ml:621,625:
    D.drive core_file ("cmdname" :: args) ... -/
def parseArgs (argsStr : Option String) : List String :=
  match argsStr with
  | none => ["cmdname"]
  | some s =>
    let parts := s.splitOn " " |>.filter (· != "")
    "cmdname" :: parts

/-- Execution mode for the interpreter -/
inductive ExecMode where
  | deterministic  -- Default: pick first branch at each choice point
  | exhaustive     -- Explore all interleavings, report any race
  deriving Repr, DecidableEq

/-- Parse JSON file and run interpreter -/
def runFile (jsonPath : String) (batch : Bool) (mode : ExecMode) (progArgs : List String) : IO Unit := do
  let contents ← IO.FS.readFile jsonPath
  match parseFileFromString contents with
  | .ok file =>
    let result := match mode with
      | .deterministic => runMain file progArgs
      | .exhaustive => runMainExhaustive file progArgs
    if batch then
      -- Batch mode: output simple parseable format
      match result.error with
      | some (.undefinedBehavior ub _) =>
        IO.println s!"Undefined \{ub: \"{ubToCode ub}\"}"
      | some (.memoryError err) =>
        -- Memory errors are UB in C semantics
        IO.println s!"Undefined \{ub: \"{memErrorToUBCode err}\"}"
      | some e =>
        IO.println s!"Error \{msg: \"{e}\"}"
      | none =>
        match result.returnValue with
        | some v =>
          -- Check for unspecified value
          match v with
          | .loaded (.unspecified ty) =>
            IO.println s!"Defined \{value: \"Unspecified('{ppCtype ty}')\"}"
          | .object (.integer iv) =>
            IO.println s!"Defined \{value: \"Specified({iv.val})\"}"
          | .loaded (.specified (.integer iv)) =>
            IO.println s!"Defined \{value: \"Specified({iv.val})\"}"
          | _ =>
            IO.println s!"Defined \{value: \"{ppValue v}\"}"
        | none => IO.println "Defined {value: \"void\"}"
    else
      -- Verbose mode: concise human-readable output
      match result.error with
      | some e => IO.println s!"Error: {e}"
      | none =>
        match result.returnValue with
        | some v => IO.println s!"Return: {ppValue v}"
        | none => IO.println "Return: void"
      if result.stdout != "" then
        IO.println s!"stdout: {result.stdout}"
      if result.stderr != "" then
        IO.println s!"stderr: {result.stderr}"
  | .error e =>
    IO.println s!"Parse error: {e}"

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  -- Parse command line: [--batch] [--mode=exhaustive] [--args "arg1 arg2 ..."] <json-file>
  let mut batch := false
  let mut mode : ExecMode := .deterministic
  let mut progArgs : Option String := none
  let mut jsonPath : Option String := none
  let mut i := 0
  while i < args.length do
    match args[i]? with
    | some "--batch" => batch := true
    | some "--mode=exhaustive" => mode := .exhaustive
    | some "--mode=deterministic" => mode := .deterministic
    | some "--args" =>
      i := i + 1
      progArgs := args[i]?
    | some path =>
      if !path.startsWith "--" then
        jsonPath := some path
    | none => pure ()
    i := i + 1

  match jsonPath with
  | some path =>
    runFile path batch mode (parseArgs progArgs)
    pure 0
  | none =>
    IO.println "Usage: cerblean_interp [--batch] [--mode=exhaustive|deterministic] [--args \"arg1 arg2 ...\"] <json-file>"
    pure 1
