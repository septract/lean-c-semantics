/-
  Pretty-printer test utilities
  Provides comparison functions for validating pretty-printer output.
-/

import CToLean.Parser
import CToLean.PrettyPrint

namespace CToLean.Test.PrettyPrint

open CToLean.Core
open CToLean.Parser
open CToLean.PrettyPrint

/-! ## Normalization Utilities -/

/-- Strip Core section header comments from a string.
    These are: "-- Aggregates", "-- Globals", "-- Fun map"
    In compact mode they can appear mid-line, so we remove them as substrings. -/
def stripSectionComments (s : String) : String :=
  s.replace "-- Aggregates" ""
   |>.replace "-- Globals" ""
   |>.replace "-- Fun map" ""

/-- Normalize whitespace for comparison: collapse all whitespace to single spaces -/
def normalizeWhitespace (s : String) : String :=
  -- First strip section comments, then normalize whitespace
  let noComments := stripSectionComments s
  let chars := noComments.toList
  let rec go (acc : List Char) (inWs : Bool) : List Char → List Char
    | [] => acc.reverse
    | c :: rest =>
      if c.isWhitespace then
        if inWs then go acc true rest
        else go (' ' :: acc) true rest
      else
        go (c :: acc) false rest
  String.ofList (go [] false chars) |>.trim

/-! ## Comparison Functions -/

/-- Compare two strings ignoring whitespace differences -/
def compareIgnoringWhitespace (s1 s2 : String) : Bool :=
  normalizeWhitespace s1 == normalizeWhitespace s2

/-- Find first difference between normalized strings -/
def findFirstDiff (s1 s2 : String) : Option (Nat × String × String) :=
  let n1 := normalizeWhitespace s1
  let n2 := normalizeWhitespace s2
  let chars1 := n1.toList
  let chars2 := n2.toList
  let rec go (idx : Nat) : List Char → List Char → Option (Nat × String × String)
    | [], [] => none
    | [], c2 :: _ => some (idx, "<end>", s!"{c2}...")
    | c1 :: _, [] => some (idx, s!"{c1}...", "<end>")
    | c1 :: r1, c2 :: r2 =>
      if c1 == c2 then go (idx + 1) r1 r2
      else
        let ctx1 := String.ofList (r1.take 20)
        let ctx2 := String.ofList (r2.take 20)
        some (idx, s!"{c1}{ctx1}", s!"{c2}{ctx2}")
  go 0 chars1 chars2

/-! ## Comparison Result Type -/

/-- Result of comparing pretty-printer output -/
inductive CompareResult
  | match_
  | mismatch (position : Nat) (leanContext : String) (expectedContext : String)
  deriving Repr

/-- Compare Lean pretty-printer output against expected output -/
def compareOutput (leanOutput expected : String) : CompareResult :=
  if compareIgnoringWhitespace leanOutput expected then
    .match_
  else
    match findFirstDiff leanOutput expected with
    | some (pos, leanCtx, expCtx) => .mismatch pos leanCtx expCtx
    | none => .match_  -- Shouldn't happen if compareIgnoringWhitespace returned false

/-! ## CLI Support -/

/-- Parse JSON and pretty-print, optionally comparing to expected output -/
def runComparison (jsonPath : String) (expectedPath : Option String) : IO UInt32 := do
  let jsonContent ← IO.FS.readFile jsonPath

  match parseFileFromString jsonContent with
  | .error e =>
    IO.eprintln s!"Parse error: {e}"
    return 1
  | .ok file =>
    let leanOutput := ppFile file

    match expectedPath with
    | none =>
      -- Just print Lean output
      IO.println leanOutput
      return 0
    | some path =>
      let expectedOutput ← IO.FS.readFile path
      match compareOutput leanOutput expectedOutput with
      | .match_ =>
        IO.println "✓ Outputs match (ignoring whitespace)"
        return 0
      | .mismatch pos leanCtx expCtx =>
        IO.eprintln "✗ Outputs differ"
        let n1 := normalizeWhitespace leanOutput
        let n2 := normalizeWhitespace expectedOutput
        IO.eprintln s!"Normalized lengths: Lean={n1.length}, Expected={n2.length}"
        IO.eprintln s!"First difference at position {pos}:"
        IO.eprintln s!"  Lean:     '{leanCtx}'"
        IO.eprintln s!"  Expected: '{expCtx}'"
        -- Show more context around the difference
        let startIdx := if pos > 20 then pos - 20 else 0
        IO.eprintln s!"  Lean context:     '{String.ofList (n1.toList.drop startIdx |>.take 50)}'"
        IO.eprintln s!"  Expected context: '{String.ofList (n2.toList.drop startIdx |>.take 50)}'"
        IO.eprintln "\n=== Lean output ==="
        IO.println leanOutput
        IO.eprintln "\n=== Expected output ==="
        IO.println expectedOutput
        return 1

end CToLean.Test.PrettyPrint
