/-
  Pretty-printer comparison CLI
  Used by scripts/test_pp.sh to compare Lean output against Cerberus.
-/

import CToLean.Test.PrettyPrint

open CToLean.Test.PrettyPrint

def main (args : List String) : IO UInt32 := do
  if args.length < 1 then
    IO.eprintln "Usage: ctolean_pp <json_file> [--compare <expected_output>]"
    return 1

  let jsonPath := args[0]!

  -- Check if we're in comparison mode
  if args.length >= 3 && args[1]! == "--compare" then
    runComparison jsonPath (some args[2]!)
  else
    runComparison jsonPath none
