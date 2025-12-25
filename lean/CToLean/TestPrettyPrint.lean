/-
  Test for pretty-printer round-trip
-/

import CToLean.Parser
import CToLean.PrettyPrint

open CToLean.Core
open CToLean.Parser
open CToLean.PrettyPrint

/-- Normalize whitespace for comparison: collapse all whitespace to single spaces -/
def normalizeWhitespace (s : String) : String :=
  let chars := s.toList
  let rec go (acc : List Char) (inWs : Bool) : List Char → List Char
    | [] => acc.reverse
    | c :: rest =>
      if c.isWhitespace then
        if inWs then go acc true rest
        else go (' ' :: acc) true rest
      else
        go (c :: acc) false rest
  String.ofList (go [] false chars) |>.trim

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

def main (args : List String) : IO UInt32 := do
  if args.length < 1 then
    IO.eprintln "Usage: ctolean_pp <json_file> [--compare <cerberus_output>]"
    return 1

  let jsonPath := args[0]!
  let jsonContent ← IO.FS.readFile jsonPath

  match parseFileFromString jsonContent with
  | .error e =>
    IO.eprintln s!"Parse error: {e}"
    return 1
  | .ok file =>
    let leanOutput := ppFile file

    -- Check if we're in comparison mode
    if args.length >= 3 && args[1]! == "--compare" then
      let cerberusPath := args[2]!
      let cerberusOutput ← IO.FS.readFile cerberusPath

      if compareIgnoringWhitespace leanOutput cerberusOutput then
        IO.println "✓ Outputs match (ignoring whitespace)"
        return 0
      else
        IO.eprintln "✗ Outputs differ"
        let n1 := normalizeWhitespace leanOutput
        let n2 := normalizeWhitespace cerberusOutput
        IO.eprintln s!"Normalized lengths: Lean={n1.length}, Cerberus={n2.length}"
        match findFirstDiff leanOutput cerberusOutput with
        | some (idx, ctx1, ctx2) =>
          IO.eprintln s!"First difference at position {idx}:"
          IO.eprintln s!"  Lean:     '{ctx1}'"
          IO.eprintln s!"  Cerberus: '{ctx2}'"
          -- Show more context around the difference
          let startIdx := if idx > 20 then idx - 20 else 0
          IO.eprintln s!"  Lean context:     '{String.ofList (n1.toList.drop startIdx |>.take 50)}'"
          IO.eprintln s!"  Cerberus context: '{String.ofList (n2.toList.drop startIdx |>.take 50)}'"
        | none => pure ()
        IO.eprintln "\n=== Lean output ==="
        IO.println leanOutput
        IO.eprintln "\n=== Cerberus output ==="
        IO.println cerberusOutput
        return 1
    else
      -- Just print Lean output
      IO.println leanOutput
      return 0
