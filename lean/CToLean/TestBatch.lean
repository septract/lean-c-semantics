/-
  Batch test for the parser
-/

import CToLean.Parser

open CToLean.Parser
open CToLean.Core

def testFile (path : String) : IO Unit := do
  let contents ← IO.FS.readFile path
  match parseFileFromString contents with
  | .ok file =>
    IO.println s!"✓ {path}: functions={file.funs.length}, tags={file.tagDefs.size}, globs={file.globs.length}"
  | .error e =>
    IO.println s!"✗ {path}: {e}"

def main (args : List String) : IO Unit := do
  for path in args do
    testFile path
