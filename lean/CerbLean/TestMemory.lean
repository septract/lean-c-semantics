/-
  Memory model test CLI
  Standalone runner for memory model unit tests.
-/

import CerbLean.Test.Memory

def main : IO Unit := CerbLean.Test.Memory.runAll
