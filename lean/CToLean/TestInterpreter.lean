/-
  Interpreter test executable
-/

import CToLean.Parser
import CToLean.Semantics

open CToLean.Core
open CToLean.Parser
open CToLean.Semantics

/-- Parse JSON file and run interpreter -/
def runFile (jsonPath : String) : IO Unit := do
  let contents ← IO.FS.readFile jsonPath
  match parseFileFromString contents with
  | .ok file =>
    let result := runMain file
    IO.println s!"Result: {result}"
    match result.returnValue with
    | some v => IO.println s!"Return value: {v}"
    | none => IO.println "No return value"
    if result.stdout != "" then
      IO.println s!"stdout: {result.stdout}"
    match result.error with
    | some e => IO.println s!"Error: {e}"
    | none => pure ()
  | .error e =>
    IO.println s!"Parse error: {e}"

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [jsonPath] =>
    runFile jsonPath
    pure 0
  | _ =>
    IO.println "Usage: ctolean_interp <json-file>"
    pure 1
