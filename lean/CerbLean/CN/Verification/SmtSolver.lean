/-
  SMT Solver Interface for CN Proof Obligations

  This module provides the interface for calling external SMT solvers
  to discharge CN proof obligations. It uses lean-smt's Solver infrastructure.

  ## Usage

  ```lean
  -- Discharge a single obligation
  let result ← SmtSolver.checkObligation .cvc5 obligation

  -- Discharge all obligations
  let results ← SmtSolver.checkObligations .cvc5 obligations
  ```

  Audited: 2026-01-27 (pragmatic pipeline using lean-smt)
-/

import CerbLean.CN.Verification.Obligation
import CerbLean.CN.Verification.SmtLib
import Smt.Translate.Solver
import Smt.Translate.Commands

namespace CerbLean.CN.Verification.SmtSolver

open CerbLean.CN.Verification (Obligation ObligationSet)
open CerbLean.CN.Verification.SmtLib
open CerbLean.Memory (TypeEnv)

-- Aliases for lean-smt types
abbrev SolverKind := Smt.Translate.Kind
abbrev SolverResult := Smt.Translate.Result

/-! ## Result Types -/

/-- Result of checking a single obligation -/
inductive CheckResult where
  | valid       : CheckResult  -- SMT returned unsat (obligation holds)
  | invalid     : CheckResult  -- SMT returned sat (counterexample exists)
  | unknown     : CheckResult  -- SMT couldn't decide
  | unsupported : List String → CheckResult  -- Contains unsupported constructs
  | error       : String → CheckResult  -- Solver error
  deriving Inhabited

instance : ToString CheckResult where
  toString
    | .valid => "valid"
    | .invalid => "invalid"
    | .unknown => "unknown"
    | .unsupported reasons => s!"unsupported: {reasons}"
    | .error msg => s!"error: {msg}"

/-- Result for a single obligation with metadata -/
structure ObligationResult where
  obligation : Obligation
  result : CheckResult
  /-- SMT-LIB2 query that was sent (for debugging) -/
  query : Option String := none
  deriving Inhabited

/-! ## Solver Interface -/

/-- Check a single obligation using an SMT solver.

    The obligation `assumptions → constraint` is checked by asserting
    `not (assumptions → constraint)` and checking satisfiability:
    - unsat means the implication always holds (valid)
    - sat means there's a counterexample (invalid)
    - unknown means the solver couldn't decide
-/
def checkObligation
    (kind : SolverKind)
    (ob : Obligation)
    (timeout : Option Nat := some 10)
    (path : Option String := none)
    (env : Option TypeEnv := none) : IO ObligationResult := do
  -- Translate to SMT terms
  let (queryStr, errors) := obligationToSmtLib2 ob env

  -- If there are unsupported constructs, report them
  if !errors.isEmpty then
    return { obligation := ob, result := .unsupported errors, query := some queryStr }

  -- Get the commands
  let (cmds, _) := obligationToCommands ob env

  -- Create solver with error handling
  try
    let state ← Smt.Translate.Solver.createFromKind kind path timeout

    -- Run the query
    let result ← StateT.run (s := state) do
      -- Emit solver basics preamble (tuples, lists, options, mem_byte, pointers)
      -- CN ref: solver.ml:1098-1104 (declare_solver_basics)
      let st ← get
      st.proc.stdin.putStr solverBasicsPreamble
      -- Emit struct datatype declarations if TypeEnv is available
      match env with
      | some e =>
        match generateStructPreamble e with
        | .ok s => st.proc.stdin.putStr s
        | .error msg => throw (IO.userError s!"SmtSolver: {msg}")
      | none => pure ()
      st.proc.stdin.flush
      -- Emit all commands except checkSat (we'll call it separately)
      for cmd in cmds.dropLast do
        Smt.Translate.Solver.emitCommand cmd
      -- Check satisfiability
      Smt.Translate.Solver.checkSat

    let (smtResult, finalState) := result

    -- Clean up
    let _ ← StateT.run (s := finalState) Smt.Translate.Solver.exit

    -- Convert result
    let checkResult := match smtResult with
      | .unsat => CheckResult.valid      -- No counterexample exists, obligation holds
      | .sat => CheckResult.invalid      -- Counterexample exists, obligation fails
      | .unknown => CheckResult.unknown

    return { obligation := ob, result := checkResult, query := some queryStr }
  catch e =>
    -- Catch solver errors and return as error result with the query
    return { obligation := ob, result := .error (toString e), query := some queryStr }

/-- Check all obligations in a set -/
def checkObligations
    (kind : SolverKind)
    (obs : ObligationSet)
    (timeout : Option Nat := some 10)
    (path : Option String := none)
    (env : Option TypeEnv := none) : IO (List ObligationResult) := do
  obs.mapM (checkObligation kind · timeout path env)

/-! ## Convenience Functions -/

/-- Check obligations with cvc5 (default) -/
def checkWithCvc5 (obs : ObligationSet) (env : Option TypeEnv := none) : IO (List ObligationResult) :=
  checkObligations .cvc5 obs (env := env)

/-- Check if all obligations are valid -/
def allValid (results : List ObligationResult) : Bool :=
  results.all fun r => match r.result with
    | .valid => true
    | _ => false

/-- Get failed obligations -/
def getFailures (results : List ObligationResult) : List ObligationResult :=
  results.filter fun r => match r.result with
    | .valid => false
    | _ => true

/-- Pretty-print results -/
def printResults (results : List ObligationResult) : IO Unit := do
  for r in results do
    let status := match r.result with
      | .valid => "✓"
      | .invalid => "✗"
      | .unknown => "?"
      | .unsupported _ => "!"
      | .error _ => "E"
    IO.println s!"{status} {r.obligation.description}"
    match r.result with
    | .unsupported reasons =>
      for reason in reasons do
        IO.println s!"    unsupported: {reason}"
    | .error msg =>
      IO.println s!"    error: {msg}"
    | _ => pure ()

end CerbLean.CN.Verification.SmtSolver
