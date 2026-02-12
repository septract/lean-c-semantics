/-
  CN Type Checking
  Corresponds to: cn/lib/check.ml

  Top-level type checking for CN function specifications.
  This processes preconditions (requires) and postconditions (ensures),
  consuming and producing resources as specified.

  Audited: 2026-01-20 against cn/lib/check.ml
-/

import CerbLean.CN.TypeChecking.Inference
import CerbLean.CN.TypeChecking.Expr
import CerbLean.CN.Types
import CerbLean.CN.Parser
import CerbLean.CN.Verification.Obligation
import CerbLean.CN.Verification.SmtLib

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types
open CerbLean.CN.Verification (Obligation ObligationSet TypeCheckResult)

/-! ## Processing Specification Clauses

Corresponds to: bind_arguments in cn/lib/check.ml lines 2341-2364

The key operations when processing a spec (function verification):
- Resource clause in precondition: PRODUCE resource (assume caller provides)
- Resource clause in postcondition: CONSUME resource (verify function produces)
- Constraint clause: add to constraint set
-/

/-- Process a single clause from a precondition.
    - Resource clauses: PRODUCE to context (caller provides these)
    - Constraint clauses: add to constraint set (assumptions about inputs)

    When verifying a function, precondition resources are ASSUMED (produced),
    not consumed. The caller provides these resources when calling the function.

    Corresponds to: aux_l in check.ml lines 2342-2353 -/
def processPreClause (clause : Clause) (loc : Loc) : TypingM Unit := do
  match clause with
  | .resource name resource =>
    -- For preconditions, we ASSUME the resource exists (caller provides it)
    -- Bind the output name as a logical variable
    let bt := resource.output.value.bt
    TypingM.addL name bt loc s!"precondition output {name.name.getD ""}"
    -- Add the resource to the context (assume it exists)
    produceResource resource
  | .constraint assertion =>
    -- Add the constraint as an assumption
    TypingM.addC (.t assertion)
  | .letBinding name value =>
    -- Let binding: bind the name to the expression's value in context
    -- Corresponds to: mDefine in core_to_mucore.ml → addLValue in typing monad
    TypingM.addLValue name value loc s!"let binding {name.name.getD ""}"

/-- Process a single clause from a postcondition.
    - Resource clauses: CONSUME from context (verify function produces them)
    - Constraint clauses: generate proof obligations (to be discharged later)

    When verifying a function, postcondition resources must be CONSUMED
    (verified to exist) - the function must produce these for the caller.

    Postcondition constraints become proof OBLIGATIONS, not assumptions.
    They are accumulated and discharged after type checking.

    Corresponds to: similar to bind_arguments but for return types -/
def processPostClause (clause : Clause) (loc : Loc) : TypingM Unit := do
  match clause with
  | .resource name resource =>
    -- For postconditions, we VERIFY the resource exists (consume it)
    consumeResourceClause name resource loc
  | .constraint assertion =>
    -- Postcondition constraints are OBLIGATIONS to prove, not assumptions
    -- They are accumulated with current assumptions as context
    TypingM.requireConstraint (.t assertion) loc "postcondition constraint"
  | .letBinding name value =>
    -- Let binding works the same in postconditions
    TypingM.addLValue name value loc s!"let binding {name.name.getD ""}"

/-! ## Checking Function Specifications

The main type checking function for a function specification.
Uses TypeCheckResult from CN.Verification.Obligation which includes
accumulated proof obligations.
-/

/-- Check for leaked resources at function exit.
    In CN, all resources must be accounted for (consumed or returned).

    Corresponds to: check for leaked resources in check_procedure -/
def checkNoLeakedResources : TypingM Unit := do
  let ctx ← TypingM.getContext
  if ctx.resources.isEmpty then
    pure ()
  else
    -- Fail on leaked resources - CN requires all resources to be accounted for
    TypingM.fail (.other s!"Leaked resources: {ctx.resources.length} resource(s) not consumed")

/-- Process all precondition clauses (requires).
    Consumes resources and binds outputs.

    Corresponds to: bind_arguments for precondition in check.ml -/
def processPrecondition (pre : Precondition) (loc : Loc) : TypingM Unit := do
  for clause in pre.clauses do
    processPreClause clause loc

/-- Process all postcondition clauses (ensures).
    Produces resources and adds constraints.

    Corresponds to: post_state_of_rt in check.ml lines 2367-2374 -/
def processPostcondition (post : Postcondition) (loc : Loc) : TypingM Unit := do
  for clause in post.clauses do
    processPostClause clause loc

/-- Type check a function specification.

    The process:
    1. Start with initial resources (from caller)
    2. Process precondition: add resources as assumptions, bind outputs
    3. (Function body executes - not checked here)
    4. Process postcondition: consume resources, generate constraint obligations

    Returns TypeCheckResult with accumulated proof obligations.
    Obligations are discharged separately (Phase 4).

    For a trusted function, we skip verification.

    Corresponds to: check_procedure in check.ml lines 2377-2426 -/
def checkFunctionSpec
    (spec : FunctionSpec)
    (initialResources : List Resource)
    (loc : Loc)
    (preamble : String := CerbLean.CN.Verification.SmtLib.pointerPreamble)
    : IO TypeCheckResult := do
  -- For trusted specs, skip verification
  if spec.trusted then
    return TypeCheckResult.ok
  else
    -- Initialize inline solver at IO level (lifecycle managed outside TypingM)
    -- If Z3 is not available, proceed without inline solver (all ops become no-ops)
    let solverChild ← try
      let proc ← IO.Process.spawn {
        cmd := "z3"
        args := #["-in", "-smt2"]
        stdin := .piped
        stdout := .piped
        stderr := .piped
      }
      proc.stdin.putStr preamble
      proc.stdin.flush
      pure (some proc)
    catch _ => pure none

    -- Run type checking with obligation accumulation enabled.
    -- Start with empty resources — processPrecondition will produce them.
    let initialState : TypingState := {
      context := Context.empty
      solverStdin := solverChild.map (·.stdin)
      solverStdout := solverChild.map (·.stdout)
    }

    let computation : TypingM Unit := do
      -- Process precondition (assumptions)
      processPrecondition spec.requires loc

      -- Process postcondition (generates obligations)
      processPostcondition spec.ensures loc

      -- Check for leaked resources: all precondition resources must be
      -- accounted for (consumed by postcondition or returned)
      -- Corresponds to: resource leak check in check_procedure
      checkNoLeakedResources

    let result ← TypingM.run computation initialState

    -- Cleanup solver at IO level (regardless of success/failure)
    if let some proc := solverChild then
      try
        proc.stdin.putStr "(exit)\n"
        proc.stdin.flush
        let _ ← proc.wait
      catch _ => pure ()

    match result with
    | .ok (_, finalState) =>
      return TypeCheckResult.okWithObligations finalState.obligations
    | .error err =>
      return TypeCheckResult.fail (toString err)

/-! ## Extract Initial Resources from Spec

For standalone spec checking, we synthesize initial resources from the
precondition's resource clauses. This simulates a caller providing exactly
what the function requires.
-/

/-- Extract resources from precondition clauses.
    Used to synthesize initial context for standalone checking. -/
def extractPreconditionResources (spec : FunctionSpec) : List Resource :=
  spec.requires.clauses.filterMap fun clause =>
    match clause with
    | .resource _ res => some res
    | .constraint _ => none
    | .letBinding _ _ => none

/-! ## Checking Function with Body

Full function verification: check that a function body satisfies its specification.
-/

/-- Type check a function body against its specification.

    **DEPRECATED**: This simplified function is for spec-only checking.
    For full body verification with proper CN-matching semantics
    (including parameter handling and label contexts), use
    `checkFunctionWithParams` from CerbLean.CN.TypeChecking.Params instead.

    This function only checks the spec (precondition/postcondition) without
    verifying the body, since body verification requires:
    - Parameter mapping (ParamValueMap)
    - Return type (for LabelContext)
    - muCore transformation (LabelDefs)

    Corresponds to: checkFunctionSpec for spec-only checking -/
def checkFunction
    (spec : FunctionSpec)
    (_body : Core.AExpr)
    (loc : Loc)
    : IO TypeCheckResult := do
  -- Delegate to spec-only checking since we don't have the full context
  -- needed for CN-matching body verification (params, return type, etc.)
  let initialResources := extractPreconditionResources spec
  checkFunctionSpec spec initialResources loc

/-! ## Convenience Functions -/

/-- Check if a function spec is well-typed given initial resources.
    Returns true if structural type checking succeeds.
    Note: Even if this returns true, obligations still need to be discharged. -/
def isWellTyped
    (spec : FunctionSpec)
    (initialResources : List Resource)
    : IO Bool := do
  let result ← checkFunctionSpec spec initialResources .unknown
  return result.success

/-- Check a function spec and return any error message.
    Returns none if structural checking succeeded, some error otherwise.
    Note: Success here doesn't mean verification is complete - obligations
    must still be discharged. -/
def checkSpec
    (spec : FunctionSpec)
    (initialResources : List Resource)
    : IO (Option String) := do
  let result ← checkFunctionSpec spec initialResources .unknown
  return result.error

/-- Run type checking on a spec in standalone mode.
    Synthesizes initial resources from the precondition.
    Returns the TypeCheckResult with accumulated obligations. -/
def checkSpecStandalone
    (spec : FunctionSpec)
    : IO TypeCheckResult := do
  let initialResources := extractPreconditionResources spec
  checkFunctionSpec spec initialResources .unknown

/-- Parse and type check a CN annotation string.
    Returns TypeCheckResult with accumulated obligations.
    This is the main entry point for checking CN specs. -/
def parseAndCheck
    (input : String)
    : IO (Except String TypeCheckResult) := do
  match CerbLean.CN.Parser.parseFunctionSpec input with
  | .error e => return .error s!"Parse error: {e}"
  | .ok spec => return .ok (← checkSpecStandalone spec)

/-- Parse and type check, returning a simple success/failure.
    Note: This only checks structural success. Obligations are not discharged.
    Use parseAndCheck to get the full result with obligations. -/
def parseAndCheckBool
    (input : String)
    : IO Bool := do
  match ← parseAndCheck input with
  | .ok result => return result.success
  | .error _ => return false

end CerbLean.CN.TypeChecking
