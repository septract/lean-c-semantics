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
import CerbLean.CN.TypeChecking

namespace CerbLean.Test.CN

open CerbLean.Parser
open CerbLean.Core
open CerbLean.CN.Parser
open CerbLean.CN.PrettyPrint
open CerbLean.CN.TypeChecking

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

/-- Run unit tests on the CN parser and type checker -/
def runUnitTests : IO UInt32 := do
  IO.println "=== CN Parser & Type Checker Unit Tests ==="
  IO.println ""

  let mut parsePassed := 0
  let mut parseFailed := 0
  let mut checkPassed := 0
  let mut checkFailed := 0

  for (name, input) in unitTestCases do
    IO.print s!"Test '{name}': "
    match parseFunctionSpec input with
    | .ok spec =>
      parsePassed := parsePassed + 1
      IO.println "PARSE OK"
      IO.println s!"  requires: {spec.requires.clauses.length} clauses"
      IO.println s!"  ensures: {spec.ensures.clauses.length} clauses"
      IO.println s!"  trusted: {spec.trusted}"
      IO.println s!"  pretty: {ppFunctionSpec spec}"

      -- Run type checker
      let result := checkSpecStandalone spec .trivial
      if result.success then
        checkPassed := checkPassed + 1
        IO.println s!"  typecheck: PASS"
      else
        checkFailed := checkFailed + 1
        IO.println s!"  typecheck: FAIL"
        match result.error with
        | some (.missingResource _ _) => IO.println s!"    error: missing resource"
        | some (.unprovableConstraint _ _) => IO.println s!"    error: unprovable constraint"
        | some (.unboundVariable sym) => IO.println s!"    error: unbound variable {sym.name.getD "<unknown>"}"
        | some (.other msg) => IO.println s!"    error: {msg}"
        | none => IO.println s!"    error: unknown"
    | .error e =>
      parseFailed := parseFailed + 1
      IO.println s!"PARSE FAILED: {e}"
    IO.println ""

  IO.println "=== Summary ==="
  IO.println s!"Parse: {parsePassed} passed, {parseFailed} failed"
  IO.println s!"TypeCheck: {checkPassed} passed, {checkFailed} failed"

  if parseFailed > 0 || checkFailed > 0 then
    return 1
  else
    return 0

/-! ## Helper: Find Function Body and Parameters -/

/-- Function info including body and parameters -/
structure FunctionBodyInfo where
  body : Core.AExpr
  params : List (Core.Sym × Core.BaseType)
  retTy : Core.BaseType

/-- Look up a function's body and parameters by symbol name.
    Returns the first Proc (actual function with body), not ProcDecl (forward declaration). -/
def findFunctionInfo (file : Core.File) (name : Option String) : Option FunctionBodyInfo :=
  -- Find the first Proc with matching name (not ProcDecl which has no body)
  file.funs.findSome? fun (sym, decl) =>
    if sym.name == name then
      match decl with
      | .proc _ _ retTy params body => some { body, params, retTy }
      | .fun_ _ _ _ => none  -- Pure functions have APexpr body, not AExpr
      | _ => none  -- ProcDecl, BuiltinDecl have no body
    else
      none

/-- Format a type error for display -/
def formatTypeError : TypeError → String
  | .missingResource req _ =>
    let reqStr := match req with
      | .p pred => s!"predicate {repr pred.name}"
      | .q qpred => s!"quantified predicate {repr qpred.name}"
    s!"missing resource: {reqStr}"
  | .unprovableConstraint _ _ => "unprovable constraint"
  | .unboundVariable sym => s!"unbound variable: {sym.name.getD "<unknown>"}"
  | .other msg => msg

/-! ## JSON Integration Tests -/

/-- Test CN annotations from a Cerberus JSON file.
    If expectFail is true, the test passes if verification FAILS. -/
def runJsonTest (jsonPath : String) (expectFail : Bool := false) : IO UInt32 := do
  let content ← IO.FS.readFile jsonPath
  match parseFileFromString content with
  | .error e =>
    IO.eprintln s!"Parse error: {e}"
    return 1
  | .ok file =>
    IO.println "=== CN Verification ==="
    if expectFail then
      IO.println "(expecting failure)"
    IO.println ""

    let mut count := 0
    let mut parseSuccess := 0
    let mut parseFail := 0
    let mut verifySuccess := 0
    let mut verifyFail := 0

    for (sym, funInfo) in file.funinfo.toList do
      if !funInfo.cnMagic.isEmpty then
        count := count + 1
        let funName := sym.name.getD "<unnamed>"
        IO.println s!"Function: {funName}"

        for ann in funInfo.cnMagic do
          IO.println "--- Spec ---"
          match parseFunctionSpec ann.text with
          | .ok spec =>
            parseSuccess := parseSuccess + 1
            IO.println (ppFunctionSpec spec)

            -- Look up the function body and parameters
            IO.println "--- Verification ---"
            match findFunctionInfo file sym.name with
            | some info =>
              -- Full verification: check body against spec with parameters bound
              let result := checkFunctionWithParams spec info.body info.params Core.Loc.t.unknown .trivial
              if result.success then
                verifySuccess := verifySuccess + 1
                IO.println "  PASS (body verified with trivial oracle)"
              else
                verifyFail := verifyFail + 1
                IO.println "  FAIL"
                match result.error with
                | some err => IO.println s!"    error: {formatTypeError err}"
                | none => IO.println "    error: unknown"

            | none =>
              -- No body found - fall back to spec-only check
              IO.println "  (no body found, checking spec only)"
              let result := checkSpecStandalone spec .trivial
              if result.success then
                verifySuccess := verifySuccess + 1
                IO.println "  PASS (spec-only with trivial oracle)"
              else
                verifyFail := verifyFail + 1
                IO.println "  FAIL"
                match result.error with
                | some err => IO.println s!"    error: {formatTypeError err}"
                | none => IO.println "    error: unknown"

          | .error e =>
            parseFail := parseFail + 1
            IO.println s!"  PARSE ERROR: {e}"
          IO.println "--- End ---"
        IO.println ""

    if count == 0 then
      IO.println "(No CN annotations found)"
      IO.println "Note: Use --switches=at_magic_comments when running Cerberus"
      return 1
    else
      IO.println s!"Total: {count} function(s) with CN annotations"
      IO.println s!"Parse: {parseSuccess} success, {parseFail} failures"
      IO.println s!"Verify: {verifySuccess} success, {verifyFail} failures"

      -- Return code based on expectations
      if expectFail then
        -- For .fail.c tests: pass if verification failed
        if verifyFail > 0 then
          IO.println "=== EXPECTED FAILURE - TEST PASSED ==="
          return 0
        else
          IO.eprintln "=== EXPECTED FAILURE BUT PASSED - TEST FAILED ==="
          return 1
      else
        -- Normal tests: pass if verification succeeded
        if verifyFail > 0 then
          return 1
        else
          return 0

/-! ## Main Entry Point -/

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    -- No arguments: run unit tests
    runUnitTests
  | ["--expect-fail", jsonPath] =>
    -- Expected failure mode for .fail.c tests
    runJsonTest jsonPath (expectFail := true)
  | [jsonPath] =>
    -- JSON file provided: run integration test
    runJsonTest jsonPath
  | _ =>
    IO.eprintln "Usage: test_cn [--expect-fail] [<json_file>]"
    return 1

end CerbLean.Test.CN
