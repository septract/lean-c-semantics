/-
  CN specification tests
  Tests the CN parser and pretty-printer.

  Usage:
    test_cn                 Run unit tests
    test_cn <json_file>     Test CN annotations from Cerberus JSON output
-/

import CerbLean.Parser
import CerbLean.Core
import CerbLean.CN.Parser
import CerbLean.CN.PrettyPrint

namespace CerbLean.Test.CN

open CerbLean.Parser
open CerbLean.Core
open CerbLean.CN.Parser
open CerbLean.CN.PrettyPrint

/-! ## Unit Test Cases -/

def unitTestCases : List (String × String) := [
  -- Simple requires/ensures
  ("simple owned",
   " requires take v = Owned<int>(p);
     ensures take v2 = Owned<int>(p);
             v == v2;
             return == v; "),

  -- Just requires
  ("requires only",
   "requires take x = Owned<int>(ptr);"),

  -- Just ensures
  ("ensures only",
   "ensures take y = Owned<int>(q); y > 0;"),

  -- Constraint with binary ops
  ("binary ops",
   "requires x > 0; x < 100;"),

  -- Function call in expression
  ("function call",
   "ensures return == foo(x, y);"),

  -- Member access
  ("member access",
   "requires p->field == 42;"),

  -- Trusted function
  ("trusted",
   "trusted;"),

  -- Not equal
  ("not equal",
   "requires y != 0;"),

  -- Empty spec
  ("empty", "")
]

/-! ## Unit Tests -/

/-- Run unit tests on the CN parser -/
def runUnitTests : IO UInt32 := do
  IO.println "=== CN Parser Unit Tests ==="
  IO.println ""

  let mut passed := 0
  let mut failed := 0

  for (name, input) in unitTestCases do
    IO.print s!"Test '{name}': "
    match parseFunctionSpec input with
    | .ok spec =>
      IO.println "PASS"
      IO.println s!"  requires: {spec.requires.clauses.length} clauses"
      IO.println s!"  ensures: {spec.ensures.clauses.length} clauses"
      IO.println s!"  trusted: {spec.trusted}"
      IO.println s!"  pretty: {ppFunctionSpec spec}"
      passed := passed + 1
    | .error e =>
      IO.println s!"FAIL: {e}"
      failed := failed + 1
    IO.println ""

  IO.println "=== Summary ==="
  IO.println s!"Passed: {passed}"
  IO.println s!"Failed: {failed}"

  return if failed > 0 then 1 else 0

/-! ## JSON Integration Tests -/

/-- Test CN annotations from a Cerberus JSON file -/
def runJsonTest (jsonPath : String) : IO UInt32 := do
  let content ← IO.FS.readFile jsonPath
  match parseFileFromString content with
  | .error e =>
    IO.eprintln s!"Parse error: {e}"
    return 1
  | .ok file =>
    IO.println "=== CN Magic Annotations ==="
    IO.println ""
    let mut count := 0
    let mut parseSuccess := 0
    let mut parseFail := 0
    for (sym, funInfo) in file.funinfo.toList do
      if !funInfo.cnMagic.isEmpty then
        count := count + 1
        IO.println s!"Function: {sym.name.getD "<unnamed>"}"
        for ann in funInfo.cnMagic do
          IO.println "--- Raw Annotation ---"
          IO.println ann.text
          IO.println "--- Parsed ---"
          match parseFunctionSpec ann.text with
          | .ok spec =>
            parseSuccess := parseSuccess + 1
            IO.println s!"  requires: {spec.requires.clauses.length} clauses"
            IO.println s!"  ensures: {spec.ensures.clauses.length} clauses"
            IO.println s!"  trusted: {spec.trusted}"
            IO.println "--- Pretty-printed ---"
            IO.println (ppFunctionSpec spec)
          | .error e =>
            parseFail := parseFail + 1
            IO.println s!"  PARSE ERROR: {e}"
          IO.println "--- End ---"
        IO.println ""
    if count == 0 then
      IO.println "(No CN annotations found)"
      IO.println "Note: Use --switches=at_magic_comments when running Cerberus"
    else
      IO.println s!"Total: {count} function(s) with CN annotations"
      IO.println s!"Parse success: {parseSuccess}, failures: {parseFail}"
    return if parseFail > 0 then 1 else 0

/-! ## Main Entry Point -/

/-- Main entry point: run unit tests or JSON test based on args -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => runUnitTests
  | [jsonPath] => runJsonTest jsonPath
  | _ =>
    IO.eprintln "Usage: test_cn              Run unit tests"
    IO.eprintln "       test_cn <json_file>  Test CN annotations from JSON"
    return 1

end CerbLean.Test.CN
