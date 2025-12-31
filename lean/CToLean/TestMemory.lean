/-
  Memory model test runner
-/

import CToLean.Memory.Test

def main : IO Unit := do
  CToLean.Memory.Test.runAllTests
