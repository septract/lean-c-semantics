/-
  Test that CN magic strings are correctly extracted from JSON
-/
import CerbLean.Parser
import CerbLean.Core

open CerbLean.Parser
open CerbLean.Core

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: test_cn_magic <json_file>"
    return 1
  let jsonPath := args.head!
  let content ← IO.FS.readFile jsonPath
  match parseFileFromString content with
  | .error e =>
    IO.eprintln s!"Parse error: {e}"
    return 1
  | .ok file =>
    IO.println "=== CN Magic Annotations ==="
    IO.println ""
    let mut count := 0
    for (sym, funInfo) in file.funinfo.toList do
      if !funInfo.cnMagic.isEmpty then
        count := count + 1
        IO.println s!"Function: {sym.name.getD "<unnamed>"}"
        for ann in funInfo.cnMagic do
          IO.println "--- Annotation ---"
          IO.println ann.text
          IO.println "--- End ---"
        IO.println ""
    if count == 0 then
      IO.println "(No CN annotations found)"
      IO.println "Note: Use --switches=at_magic_comments when running Cerberus"
    else
      IO.println s!"Total: {count} function(s) with CN annotations"
    return 0
