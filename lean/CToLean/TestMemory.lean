/-
  Memory model test CLI
  Standalone runner for memory model unit tests.
-/

import CToLean.Test.Memory

def main : IO Unit := CToLean.Test.Memory.runAll
