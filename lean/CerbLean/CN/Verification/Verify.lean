/-
  CN Verification Entry Point

  This module provides the main entry point for verifying CN-annotated
  C programs. It combines type checking with SMT-based obligation discharge.

  ## Pipeline

  1. Parse C source with Cerberus → Core IR
  2. Run CN type checking → Obligations
  3. Translate obligations to SMT-LIB2
  4. Call external SMT solver
  5. Report results

  ## Usage

  ```lean
  -- Verify a function specification against a Core expression
  let result ← verify spec coreExpr

  -- Just check obligations without type checking
  let results ← verifyObligations obligations
  ```

  Audited: 2026-01-27 (pragmatic pipeline)
-/

import CerbLean.CN.Verification.Obligation
import CerbLean.CN.Verification.SmtLib
import CerbLean.CN.Verification.SmtSolver
import CerbLean.CN.TypeChecking

namespace CerbLean.CN.Verification

open CerbLean.CN.Verification.SmtSolver
open CerbLean.CN.TypeChecking (checkFunction checkSpecStandalone)
open CerbLean.CN.Types (FunctionSpec)
open CerbLean.Memory (TypeEnv)

/-! ## Verification Result -/

/-- Overall verification result -/
structure VerificationResult where
  /-- Did type checking succeed? -/
  typeCheckSuccess : Bool
  /-- Type checking error message (if failed) -/
  typeCheckError : Option String
  /-- Results for each obligation -/
  obligationResults : List ObligationResult
  /-- Did all obligations pass? -/
  allObligationsValid : Bool
  deriving Inhabited

instance : ToString VerificationResult where
  toString r :=
    let tcStatus := if r.typeCheckSuccess then "✓ Type checking passed" else "✗ Type checking failed"
    let obStatus := if r.allObligationsValid then "✓ All obligations valid" else "✗ Some obligations failed"
    let tcErr := match r.typeCheckError with
      | some e => s!"\n  Error: {e}"
      | none => ""
    let obCount := r.obligationResults.length
    let validCount := r.obligationResults.filter (·.result matches .valid) |>.length
    s!"{tcStatus}{tcErr}\n{obStatus} ({validCount}/{obCount} valid)"

/-! ## Main Verification Functions -/

/-- Verify obligations using SMT solver.

    This is the main entry point when you already have a list of obligations
    (e.g., from type checking).
-/
def verifyObligations
    (obs : ObligationSet)
    (solver : SolverKind := .z3)
    (timeout : Option Nat := some 10)
    (env : Option TypeEnv := none) : IO (List ObligationResult) := do
  if obs.isEmpty then
    return []
  checkObligations solver obs timeout (env := env)

/-- Verify a function specification (spec-only, no body).

    This runs type checking on the specification and then verifies
    all generated obligations with SMT.
-/
def verifySpec
    (spec : FunctionSpec)
    (solver : SolverKind := .z3)
    (timeout : Option Nat := some 10)
    (env : Option TypeEnv := none) : IO VerificationResult := do
  -- Run type checking
  let tcResult ← checkSpecStandalone spec

  if !tcResult.success then
    return {
      typeCheckSuccess := false
      typeCheckError := tcResult.error
      obligationResults := []
      allObligationsValid := false
    }

  -- Check obligations with SMT
  let obResults ← verifyObligations tcResult.obligations solver timeout env

  return {
    typeCheckSuccess := true
    typeCheckError := none
    obligationResults := obResults
    allObligationsValid := allValid obResults
  }

/-! ## Utility Functions -/

/-- Print detailed verification results -/
def printVerificationResult (r : VerificationResult) : IO Unit := do
  IO.println "=== Verification Result ==="
  IO.println ""

  -- Type checking status
  if r.typeCheckSuccess then
    IO.println "Type Checking: ✓ PASSED"
  else
    IO.println "Type Checking: ✗ FAILED"
    if let some err := r.typeCheckError then
      IO.println s!"  Error: {err}"

  IO.println ""

  -- Obligation results
  let total := r.obligationResults.length
  if total == 0 then
    IO.println "Obligations: (none)"
  else
    let valid := r.obligationResults.filter (·.result matches .valid) |>.length
    let invalid := r.obligationResults.filter (·.result matches .invalid) |>.length
    let unknown := r.obligationResults.filter (·.result matches .unknown) |>.length
    let unsupported := r.obligationResults.filter (·.result matches .unsupported _) |>.length
    let errors := r.obligationResults.filter (·.result matches .error _) |>.length

    IO.println s!"Obligations: {valid}/{total} valid"
    if invalid > 0 then IO.println s!"  {invalid} invalid (counterexample exists)"
    if unknown > 0 then IO.println s!"  {unknown} unknown (solver timeout/incomplete)"
    if unsupported > 0 then IO.println s!"  {unsupported} unsupported constructs"
    if errors > 0 then IO.println s!"  {errors} solver errors"

    IO.println ""
    IO.println "Details:"
    printResults r.obligationResults

  IO.println ""

  -- Overall status
  if r.typeCheckSuccess && r.allObligationsValid then
    IO.println "=== VERIFICATION SUCCESSFUL ==="
  else
    IO.println "=== VERIFICATION FAILED ==="

/-! ## Quick Test -/

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types (Term AnnotTerm BaseType LogicalConstraint)

/-- Quick smoke test that the pipeline works -/
def smokeTest : IO Unit := do
  IO.println "SMT Solver Smoke Test"
  IO.println "====================="

  -- Create a trivial obligation: True
  let trueTerm : AnnotTerm := .mk (.const (.bool true)) .bool .unknown
  let trivialOb : Obligation := {
    description := "trivial (True)"
    constraint := .t trueTerm
    assumptions := []
    loc := .unknown
    category := .arithmetic
  }

  IO.println "Testing trivial obligation (True)..."
  let result ← checkObligation .z3 trivialOb
  IO.println s!"Result: {result.result}"

  -- Create a simple arithmetic obligation: x > 0 → x > 0
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

  IO.println "Testing arithmetic obligation (x > 0 → x > 0)..."
  let result2 ← checkObligation .z3 arithmeticOb
  IO.println s!"Result: {result2.result}"

  if let some q := result2.query then
    IO.println "SMT-LIB2 query:"
    IO.println q

end CerbLean.CN.Verification
