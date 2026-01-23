/-
  CN test CLI
  Standalone runner for CN parser and pretty-printer tests.
-/

import CerbLean.Test.CN

def main (args : List String) : IO UInt32 := CerbLean.Test.CN.main args
