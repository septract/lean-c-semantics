/-
  Unified test module
  Imports all test modules and provides a unified test runner.
-/

import CerbLean.Test.Memory
import CerbLean.Test.Parser
import CerbLean.Test.PrettyPrint
import CerbLean.Test.Batch

namespace CerbLean.Test

/-- Run all unit tests (parser + memory) -/
def runAll : IO Unit := do
  IO.println "Running all unit tests..."
  IO.println ""

  Parser.runAll
  IO.println ""

  Memory.runAll
  IO.println ""

  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "All unit tests passed!"

end CerbLean.Test

/-- Main entry point for cerblean_test executable -/
def main : IO Unit := CerbLean.Test.runAll
