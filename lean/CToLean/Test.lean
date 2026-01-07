/-
  Unified test module
  Imports all test modules and provides a unified test runner.
-/

import CToLean.Test.Memory
import CToLean.Test.Parser
import CToLean.Test.PrettyPrint
import CToLean.Test.Batch
import CToLean.Test.RealAST

namespace CToLean.Test

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

end CToLean.Test

/-- Main entry point for ctolean_test executable -/
def main : IO Unit := CToLean.Test.runAll
