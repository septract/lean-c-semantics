/-
  Batch parser test CLI
  Used by scripts/test_parser.sh to test parsing multiple JSON files.
-/

import CToLean.Test.Batch

open CToLean.Test.Batch

def main (args : List String) : IO Unit := do
  let (passed, failed) ← runBatch args
  if failed > 0 then
    IO.println s!"\nSummary: {passed} passed, {failed} failed"
  else if passed > 0 then
    IO.println s!"\nAll {passed} files parsed successfully"
