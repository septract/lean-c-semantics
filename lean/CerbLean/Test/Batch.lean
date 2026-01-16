/-
  Batch test utilities
  Support for running tests on multiple files from command line.
-/

import CerbLean.Parser

namespace CerbLean.Test.Batch

open CerbLean.Parser
open CerbLean.Core

/-- Test result for a single file -/
inductive TestResult
  | success (functions : Nat) (tags : Nat) (globs : Nat)
  | failure (error : String)
  deriving Repr

/-- Test parsing a single JSON file -/
def testFile (path : String) : IO TestResult := do
  let contents ← IO.FS.readFile path
  match parseFileFromString contents with
  | .ok file =>
    return .success file.funs.length file.tagDefs.length file.globs.length
  | .error e =>
    return .failure e

/-- Print test result for a file -/
def printResult (path : String) (result : TestResult) : IO Unit := do
  match result with
  | .success funs tags globs =>
    IO.println s!"✓ {path}: functions={funs}, tags={tags}, globs={globs}"
  | .failure e =>
    IO.println s!"✗ {path}: {e}"

/-- Run batch tests on multiple files -/
def runBatch (paths : List String) : IO (Nat × Nat) := do
  let mut passed := 0
  let mut failed := 0
  for path in paths do
    let result ← testFile path
    printResult path result
    match result with
    | .success .. => passed := passed + 1
    | .failure .. => failed := failed + 1
  return (passed, failed)

end CerbLean.Test.Batch
