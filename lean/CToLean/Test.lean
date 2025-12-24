/-
  Simple test for the parser
-/

import CToLean.Parser

open CToLean.Parser
open CToLean.Core

def testJson : String := r#"{
  "main": { "id": 502, "name": "main" },
  "tagDefs": [],
  "globs": [],
  "funs": [
    {
      "symbol": { "id": 502, "name": "main" },
      "declaration": {
        "tag": "Proc",
        "loc": "<tests/ci/0001-emptymain.c:1:0>",
        "return_type": {
          "tag": "BTy_loaded",
          "object_type": { "tag": "OTy_integer" }
        },
        "params": [],
        "body": {
          "loc": null,
          "expr": {
            "tag": "Epure",
            "expr": {
              "loc": null,
              "expr": { "tag": "PEval", "value": { "tag": "Vunit" } }
            }
          }
        }
      }
    }
  ]
}"#

def main : IO Unit := do
  IO.println "Testing JSON parser..."
  match parseFileFromString testJson with
  | .ok file =>
    IO.println s!"✓ Parsed successfully!"
    IO.println s!"  main: {repr file.main}"
    IO.println s!"  functions: {file.funs.size}"
  | .error e =>
    IO.println s!"✗ Parse error: {e}"
