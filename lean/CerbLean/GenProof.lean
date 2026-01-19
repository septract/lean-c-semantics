/-
  Generate standalone Lean proof files from Core JSON

  This tool parses a Core JSON file and generates a self-contained Lean file
  that defines the program AST and states theorems about it.
-/

import CerbLean.Parser
import CerbLean.Core.Repr
import CerbLean.Semantics.Interpreter

open CerbLean.Parser
open CerbLean.Core
open CerbLean.Semantics

/-- Generate a standalone Lean file for proving properties of a Core program -/
def generateProofFile (file : File) (moduleName : String) : String :=
  -- Use very large width to force single-line output (avoids Lean parser issues with multi-line structure literals)
  let programRepr := Std.Format.pretty (repr file) (width := 1000000)
  s!"/-
  Auto-generated proof file for {moduleName}

  This file contains:
  1. The Core program AST (parsed from JSON)
  2. A test that verifies the program runs
  3. Theorem stubs for UB-freedom and functional correctness
-/

import CerbLean.Semantics.Interpreter
import CerbLean.Core.Repr
import Mathlib.Tactic

namespace {moduleName}

open CerbLean.Core
open CerbLean.Semantics

/-! ## Program Definition -/

/-- The Core program AST -/
def program : File := {programRepr}

/-! ## Execution Test -/

#eval runMain program

/-! ## Theorems -/

/-- The program terminates without undefined behavior -/
theorem program_noError : (runMain program).error = none := by
  sorry

/-- The program returns the expected value (fill in expected value) -/
theorem program_returns_expected :
    ∃ v, (runMain program).returnValue = some v := by
  sorry

end {moduleName}
"

def main (args : List String) : IO UInt32 := do
  match args with
  | [inputPath] =>
    let outputPath := inputPath.replace ".json" "_proof.lean"
    main' inputPath outputPath
  | [inputPath, outputPath] =>
    main' inputPath outputPath
  | _ =>
    IO.eprintln "Usage: genproof <input.json> [output.lean]"
    return 1
where
  main' (inputPath outputPath : String) : IO UInt32 := do
    -- Parse JSON
    let json ← IO.FS.readFile inputPath
    match Lean.Json.parse json with
    | .error e =>
      IO.eprintln s!"JSON parse error: {e}"
      return 1
    | .ok j =>
      match parseFile j with
      | .error e =>
        IO.eprintln s!"Core parse error: {e}"
        return 1
      | .ok file =>
        -- Generate module name from output path
        -- Filter out non-alphanumeric chars and ensure it starts with a letter
        let rawName := outputPath
          |>.replace ".lean" ""
          |>.split (· == '/')
          |>.getLast!
        let cleanName := rawName.toList
          |>.filter (fun c => c.isAlpha || c.isDigit || c == '_')
          |> String.mk
        -- Split on underscores and capitalize
        let parts := cleanName.split (· == '_') |>.map String.capitalize
        let moduleName := String.intercalate "" parts
        -- Ensure starts with letter (prefix with "M" if starts with digit)
        let moduleName := if moduleName.isEmpty then "Generated"
          else if moduleName.get! 0 |>.isDigit then "M" ++ moduleName
          else moduleName

        -- Generate and write output
        let output := generateProofFile file moduleName
        IO.FS.writeFile outputPath output
        IO.println s!"Generated {outputPath}"
        return 0
