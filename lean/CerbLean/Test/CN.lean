/-
  CN specification tests
  Tests the CN parser, type checker, and verification pipeline.

  Usage:
    test_cn                      Run unit tests (parse + typecheck)
    test_cn --verify             Run SMT verification smoke test
    test_cn <json_file>          Parse and type-check CN annotations from Cerberus JSON
    test_cn --verify <json_file> Full verification with SMT solver
-/

import CerbLean.Parser
import CerbLean.Core
import CerbLean.CN.Parser
import CerbLean.CN.PrettyPrint
import CerbLean.CN.TypeChecking
import CerbLean.CN.Verification.Obligation
import CerbLean.CN.Verification.Verify

namespace CerbLean.Test.CN

open CerbLean.Parser
open CerbLean.Core
open CerbLean.CN.Parser
open CerbLean.CN.PrettyPrint
open CerbLean.CN.TypeChecking
open CerbLean.CN.Verification
open CerbLean.CN.Verification.SmtSolver (checkObligation checkObligations SolverKind)

/-! ## Unit Test Cases

Each test is (name, input, expectFail) where expectFail indicates
whether type checking is expected to fail.
-/

def unitTestCases : List (String × String × Bool) := [
  -- Simple requires/ensures
  ("simple owned",
   " requires take v = Owned<int>(p);
     ensures take v2 = Owned<int>(p);
             v == v2;
             return == v; ",
   false),

  -- Just requires
  ("requires only",
   "requires take x = Owned<int>(ptr);",
   false),

  -- Just ensures (expected to fail - can't produce resources without having them)
  ("ensures only (expect fail)",
   "ensures take y = Owned<int>(q); y > 0;",
   true),

  -- Constraint with binary ops
  ("binary ops",
   "requires x > 0; x < 100;",
   false),

  -- Function call in expression
  ("function call",
   "ensures return == foo(x, y);",
   false),

  -- Member access
  ("member access",
   "requires p->field == 42;",
   false),

  -- Trusted function
  ("trusted",
   "trusted;",
   false),

  -- Not equal
  ("not equal",
   "requires y != 0;",
   false),

  -- Empty spec
  ("empty", "", false)
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

  for (name, input, expectFail) in unitTestCases do
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
      let result := checkSpecStandalone spec
      if result.success then
        if expectFail then
          -- Expected to fail but passed
          checkFailed := checkFailed + 1
          IO.println s!"  typecheck: UNEXPECTED PASS (expected failure)"
        else
          checkPassed := checkPassed + 1
          IO.println s!"  typecheck: PASS"
      else
        if expectFail then
          -- Expected failure
          checkPassed := checkPassed + 1
          IO.println s!"  typecheck: EXPECTED FAIL"
          match result.error with
          | some msg => IO.println s!"    ({msg} - as expected)"
          | none => IO.println s!"    (unknown error - as expected)"
        else
          checkFailed := checkFailed + 1
          IO.println s!"  typecheck: FAIL"
          match result.error with
          | some msg => IO.println s!"    error: {msg}"
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

/-! ## Obligation Unit Tests

Tests for the proof obligation infrastructure.
These verify that obligations are generated correctly during type checking.
-/

/-- Test case for obligation generation: (name, spec, expectedObligationCount, shouldSucceed) -/
structure ObligationTestCase where
  name : String
  spec : String
  expectedMinObligations : Nat  -- Minimum number of obligations expected
  shouldSucceed : Bool          -- Whether structural type checking should succeed

def obligationTestCases : List ObligationTestCase := [
  -- Postcondition constraints become obligations
  { name := "postcondition constraint generates obligation"
  , spec := "requires x > 0; ensures return == x;"
  , expectedMinObligations := 1  -- The `return == x` constraint
  , shouldSucceed := true
  },

  -- Multiple postcondition constraints
  { name := "multiple postcondition constraints"
  , spec := "requires x > 0; y > 0; ensures return == x + y; return > 0;"
  , expectedMinObligations := 2  -- Two ensures constraints
  , shouldSucceed := true
  },

  -- No postcondition constraints = no obligations
  { name := "no postcondition constraints"
  , spec := "requires x > 0;"
  , expectedMinObligations := 0
  , shouldSucceed := true
  },

  -- Precondition constraints are assumptions, not obligations
  { name := "precondition constraints are not obligations"
  , spec := "requires x > 0; x < 100; y != 0;"
  , expectedMinObligations := 0  -- Preconditions are assumptions
  , shouldSucceed := true
  },

  -- Resource clause in postcondition (no explicit constraint obligation)
  { name := "resource postcondition with constraint"
  , spec := "requires take v = Owned<int>(p); ensures take v2 = Owned<int>(p); v == v2;"
  , expectedMinObligations := 1  -- The `v == v2` constraint
  , shouldSucceed := true
  },

  -- Empty spec = no obligations
  { name := "empty spec"
  , spec := ""
  , expectedMinObligations := 0
  , shouldSucceed := true
  },

  -- Trusted spec = no obligations (skips verification)
  { name := "trusted spec"
  , spec := "trusted;"
  , expectedMinObligations := 0
  , shouldSucceed := true
  }
]

/-- Run obligation unit tests -/
def runObligationTests : IO UInt32 := do
  IO.println "=== Obligation Generation Unit Tests ==="
  IO.println ""

  let mut passed := 0
  let mut failed := 0

  for tc in obligationTestCases do
    IO.print s!"Test '{tc.name}': "

    match parseFunctionSpec tc.spec with
    | .error e =>
      failed := failed + 1
      IO.println s!"PARSE ERROR: {e}"
    | .ok spec =>
      let result := checkSpecStandalone spec
      let numObligations := result.obligations.length

      -- Check structural success
      let successOk := result.success == tc.shouldSucceed

      -- Check obligation count
      let obligationsOk := numObligations >= tc.expectedMinObligations

      if successOk && obligationsOk then
        passed := passed + 1
        IO.println s!"PASS (obligations: {numObligations})"
        -- Show obligation details if any
        if numObligations > 0 then
          for ob in result.obligations do
            IO.println s!"    - [{ob.category}] {ob.description}"
      else
        failed := failed + 1
        IO.println "FAIL"
        if !successOk then
          IO.println s!"    Expected success={tc.shouldSucceed}, got success={result.success}"
          if let some err := result.error then
            IO.println s!"    Error: {err}"
        if !obligationsOk then
          IO.println s!"    Expected at least {tc.expectedMinObligations} obligations, got {numObligations}"

    IO.println ""

  IO.println "=== Obligation Test Summary ==="
  IO.println s!"Passed: {passed}, Failed: {failed}"
  IO.println ""

  if failed > 0 then return 1 else return 0

/-- Test that obligations capture assumptions correctly -/
def runAssumptionCaptureTest : IO UInt32 := do
  IO.println "=== Assumption Capture Test ==="
  IO.println ""

  -- This spec has precondition constraints that should become assumptions
  -- in any obligations generated from postcondition constraints
  let spec := "requires x > 0; x < 100; ensures return == x * 2;"

  match parseFunctionSpec spec with
  | .error e =>
    IO.println s!"PARSE ERROR: {e}"
    return 1
  | .ok parsedSpec =>
    let result := checkSpecStandalone parsedSpec

    if !result.success then
      IO.println s!"FAIL: Type checking failed unexpectedly"
      return 1

    if result.obligations.isEmpty then
      IO.println "FAIL: Expected at least one obligation"
      return 1

    -- Check that the first obligation has assumptions
    let ob := result.obligations.head!
    IO.println s!"Obligation: {ob.description}"
    IO.println s!"  Category: {repr ob.category}"
    IO.println s!"  Assumptions: {ob.assumptions.length} constraint(s)"

    -- The precondition had 2 constraints (x > 0, x < 100)
    -- These should be captured as assumptions
    if ob.assumptions.length >= 2 then
      IO.println "PASS: Assumptions captured correctly"
      IO.println ""
      return 0
    else
      IO.println s!"FAIL: Expected at least 2 assumptions, got {ob.assumptions.length}"
      IO.println ""
      return 1

/-- Run all obligation-related tests -/
def runAllObligationTests : IO UInt32 := do
  let mut exitCode : UInt32 := 0

  let r1 ← runObligationTests
  if r1 != 0 then exitCode := 1

  let r2 ← runAssumptionCaptureTest
  if r2 != 0 then exitCode := 1

  return exitCode

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
              let result := checkFunctionWithParams spec info.body info.params Core.Loc.t.unknown
              if result.success then
                verifySuccess := verifySuccess + 1
                IO.println "  PASS (body verified with trivial oracle)"
              else
                verifyFail := verifyFail + 1
                IO.println "  FAIL"
                match result.error with
                | some msg => IO.println s!"    error: {msg}"
                | none => IO.println "    error: unknown"

            | none =>
              -- No body found - fall back to spec-only check
              IO.println "  (no body found, checking spec only)"
              let result := checkSpecStandalone spec
              if result.success then
                verifySuccess := verifySuccess + 1
                IO.println "  PASS (spec-only with trivial oracle)"
              else
                verifyFail := verifyFail + 1
                IO.println "  FAIL"
                match result.error with
                | some msg => IO.println s!"    error: {msg}"
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

/-! ## SMT Verification Tests -/

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types (Term AnnotTerm BaseType LogicalConstraint)

/-- Run SMT solver smoke test -/
def runSmtSmokeTest : IO UInt32 := do
  IO.println "=== SMT Solver Smoke Test ==="
  IO.println ""

  let mut passed := 0
  let mut failed := 0

  -- Test 1: Trivial obligation (True)
  IO.print "Test 'trivial (True)': "
  let trueTerm : AnnotTerm := .mk (.const (.bool true)) .bool .unknown
  let trivialOb : Obligation := {
    description := "trivial (True)"
    constraint := .t trueTerm
    assumptions := []
    loc := .unknown
    category := .arithmetic
  }
  let result1 ← checkObligation .z3 trivialOb
  match result1.result with
  | .valid =>
    passed := passed + 1
    IO.println "PASS (valid)"
  | other =>
    failed := failed + 1
    IO.println s!"FAIL (got {other})"

  -- Test 2: Simple arithmetic (x > 0 → x > 0)
  IO.print "Test 'x > 0 → x > 0': "
  let sym : Sym := { id := 1, name := some "x" }
  let xAnnot : AnnotTerm := .mk (.sym sym) .integer .unknown
  let zeroAnnot : AnnotTerm := .mk (.const (.z 0)) .integer .unknown
  let xGtZeroTerm : Term := .binop .lt zeroAnnot xAnnot  -- 0 < x means x > 0
  let xGtZero : AnnotTerm := .mk xGtZeroTerm .bool .unknown

  let arithmeticOb : Obligation := {
    description := "x > 0 → x > 0"
    constraint := .t xGtZero
    assumptions := [.t xGtZero]
    loc := .unknown
    category := .arithmetic
  }
  let result2 ← checkObligation .z3 arithmeticOb
  match result2.result with
  | .valid =>
    passed := passed + 1
    IO.println "PASS (valid)"
  | other =>
    failed := failed + 1
    IO.println s!"FAIL (got {other})"

  -- Test 3: Invalid obligation (should fail)
  IO.print "Test 'False (should be invalid)': "
  let falseTerm : AnnotTerm := .mk (.const (.bool false)) .bool .unknown
  let invalidOb : Obligation := {
    description := "false (should be invalid)"
    constraint := .t falseTerm
    assumptions := []
    loc := .unknown
    category := .arithmetic
  }
  let result3 ← checkObligation .z3 invalidOb
  match result3.result with
  | .invalid =>
    passed := passed + 1
    IO.println "PASS (correctly invalid)"
  | other =>
    failed := failed + 1
    IO.println s!"FAIL (expected invalid, got {other})"

  IO.println ""
  IO.println s!"=== SMT Summary: {passed} passed, {failed} failed ==="

  if failed > 0 then return 1 else return 0

/-- Run JSON test with full SMT verification -/
def runJsonTestWithVerify (jsonPath : String) (expectFail : Bool := false) : IO UInt32 := do
  let content ← IO.FS.readFile jsonPath
  match parseFileFromString content with
  | .error e =>
    IO.eprintln s!"Parse error: {e}"
    return 1
  | .ok file =>
    IO.println "=== CN Verification (with SMT) ==="
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

            IO.println "--- Verification ---"
            match findFunctionInfo file sym.name with
            | some info =>
              -- Type check first
              let tcResult := checkFunctionWithParams spec info.body info.params Core.Loc.t.unknown
              if !tcResult.success then
                verifyFail := verifyFail + 1
                IO.println "  TYPECHECK FAIL"
                match tcResult.error with
                | some msg => IO.println s!"    error: {msg}"
                | none => IO.println "    error: unknown"
              else if tcResult.obligations.isEmpty then
                verifySuccess := verifySuccess + 1
                IO.println "  PASS (no obligations)"
              else
                -- Verify obligations with SMT
                let obResults ← checkObligations .z3 tcResult.obligations (some 10)
                let allValid := obResults.all fun r => r.result matches .valid
                if allValid then
                  verifySuccess := verifySuccess + 1
                  IO.println s!"  PASS ({obResults.length} obligations verified)"
                else
                  verifyFail := verifyFail + 1
                  IO.println s!"  FAIL (some obligations not verified)"
                  for r in obResults do
                    IO.println s!"    - {r.obligation.description}: {r.result}"
                    if let some q := r.query then
                      IO.println "    SMT query:"
                      IO.println q

            | none =>
              -- No body found - spec-only check
              IO.println "  (no body found, checking spec only)"
              let tcResult := checkSpecStandalone spec
              if !tcResult.success then
                verifyFail := verifyFail + 1
                IO.println "  TYPECHECK FAIL"
              else if tcResult.obligations.isEmpty then
                verifySuccess := verifySuccess + 1
                IO.println "  PASS (no obligations)"
              else
                let obResults ← checkObligations .z3 tcResult.obligations (some 10)
                let allValid := obResults.all fun r => r.result matches .valid
                if allValid then
                  verifySuccess := verifySuccess + 1
                  IO.println s!"  PASS ({obResults.length} obligations verified)"
                else
                  verifyFail := verifyFail + 1
                  IO.println s!"  FAIL"

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

      if expectFail then
        if verifyFail > 0 then
          IO.println "=== EXPECTED FAILURE - TEST PASSED ==="
          return 0
        else
          IO.eprintln "=== EXPECTED FAILURE BUT PASSED - TEST FAILED ==="
          return 1
      else
        if verifyFail > 0 then
          return 1
        else
          return 0

/-! ## Main Entry Point -/

def printUsage : IO Unit := do
  IO.println "Usage: test_cn [options] [<json_file>]"
  IO.println ""
  IO.println "Modes:"
  IO.println "  (no args)              Run unit tests (parse + typecheck)"
  IO.println "  --verify               Run SMT verification smoke test"
  IO.println "  <json_file>            Type-check CN annotations from Cerberus JSON"
  IO.println "  --verify <json_file>   Full verification with SMT solver"
  IO.println ""
  IO.println "Options:"
  IO.println "  --obligations          Run only obligation generation tests"
  IO.println "  --expect-fail          Expect verification to fail (for .fail.c tests)"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    -- No arguments: run all unit tests
    let mut exitCode : UInt32 := 0

    let r1 ← runUnitTests
    if r1 != 0 then exitCode := 1

    IO.println ""
    let r2 ← runAllObligationTests
    if r2 != 0 then exitCode := 1

    return exitCode

  | ["--verify"] =>
    -- SMT verification smoke test
    runSmtSmokeTest

  | ["--verify", jsonPath] =>
    -- Full verification with SMT
    runJsonTestWithVerify jsonPath

  | ["--verify", "--expect-fail", jsonPath] | ["--expect-fail", "--verify", jsonPath] =>
    -- Full verification with SMT, expecting failure
    runJsonTestWithVerify jsonPath (expectFail := true)

  | ["--obligations"] =>
    -- Run only obligation tests
    runAllObligationTests

  | ["--expect-fail", jsonPath] =>
    -- Expected failure mode for .fail.c tests (type-check only)
    runJsonTest jsonPath (expectFail := true)

  | ["--help"] | ["-h"] =>
    printUsage
    return 0

  | [jsonPath] =>
    -- JSON file provided: run type-check integration test
    runJsonTest jsonPath

  | _ =>
    printUsage
    return 1

end CerbLean.Test.CN
