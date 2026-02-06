/-
  Parser smoke tests
  Basic sanity checks - real validation is done by scripts/test_parser.sh against Cerberus output.
-/

import CerbLean.Parser

namespace CerbLean.Test.Parser

open CerbLean.Parser
open CerbLean.Core

/-- Test that parser rejects malformed JSON -/
def testMalformedJson : IO Unit := do
  let badJson := "{ not valid json }"
  match parseFileFromString badJson with
  | .ok _ =>
    throw (IO.userError "expected parse error for malformed JSON")
  | .error _ =>
    IO.println "✓ Malformed JSON rejection test passed"

/-- Test that parser rejects incomplete JSON -/
def testIncompleteJson : IO Unit := do
  let incompleteJson := r#"{ "main": { "id": 1, "name": "main" } }"#
  match parseFileFromString incompleteJson with
  | .ok _ =>
    throw (IO.userError "expected parse error for incomplete JSON")
  | .error _ =>
    IO.println "✓ Incomplete JSON rejection test passed"

/-- Test that parser accepts minimal valid JSON -/
def testMinimalValid : IO Unit := do
  -- Minimal valid structure - empty file with just required fields
  let minJson := r#"{
    "main": { "id": 1, "name": "main", "digest": "" },
    "calling_convention": "Normal",
    "tagDefs": [],
    "globs": [],
    "funs": [],
    "loop_attributes": [],
    "visible_objects_env": []
  }"#
  match parseFileFromString minJson with
  | .ok file =>
    if file.main.isNone then
      throw (IO.userError "expected main to be set")
    IO.println "✓ Minimal valid JSON parse test passed"
  | .error e =>
    throw (IO.userError s!"parse error: {e}")

/-! ## Run All Tests -/

/-- Run parser smoke tests -/
def runAll : IO Unit := do
  IO.println "=== Parser Smoke Tests ==="
  IO.println "(Full validation: scripts/test_parser.sh)"
  IO.println ""

  testMalformedJson
  testIncompleteJson
  testMinimalValid
  IO.println ""

  IO.println "All parser smoke tests passed!"

end CerbLean.Test.Parser
