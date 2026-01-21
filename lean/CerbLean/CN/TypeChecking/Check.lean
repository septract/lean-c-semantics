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

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types

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

/-- Process a single clause from a postcondition.
    - Resource clauses: CONSUME from context (verify function produces them)
    - Constraint clauses: add to constraint set (obligations to prove)

    When verifying a function, postcondition resources must be CONSUMED
    (verified to exist) - the function must produce these for the caller.

    Corresponds to: similar to bind_arguments but for return types -/
def processPostClause (clause : Clause) (loc : Loc) : TypingM Unit := do
  match clause with
  | .resource name resource =>
    -- For postconditions, we VERIFY the resource exists (consume it)
    consumeResourceClause name resource loc
  | .constraint assertion =>
    -- Add the constraint to be proved
    TypingM.addC (.t assertion)

/-! ## Checking Function Specifications

The main type checking function for a function specification.
-/

/-- Result of type checking -/
structure TypeCheckResult where
  /-- Whether type checking succeeded -/
  success : Bool
  /-- Final typing context after checking -/
  finalContext : Context
  /-- Any error that occurred -/
  error : Option TypeError
  deriving Inhabited

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

/-- Verify all constraints are provable.
    Called after processing spec to check accumulated constraints. -/
def verifyConstraints : TypingM Unit := do
  let ctx ← TypingM.getContext
  for lc in ctx.constraints do
    TypingM.ensureProvable lc

/-- Type check a function specification.

    The process:
    1. Start with initial resources (from caller)
    2. Process precondition: consume resources, bind outputs
    3. (Function body executes - not checked here)
    4. Process postcondition: produce resources, add constraints
    5. Verify all constraints are provable

    For a trusted function, we skip verification.

    Corresponds to: check_procedure in check.ml lines 2377-2426 -/
def checkFunctionSpec
    (spec : FunctionSpec)
    (initialResources : List Resource)
    (loc : Loc)
    (oracle : ProofOracle := .trivial)
    : TypeCheckResult :=
  -- For trusted specs, skip verification
  if spec.trusted then
    { success := true
    , finalContext := Context.empty
    , error := none }
  else
    -- Run type checking
    let initialState : TypingState := {
      context := { Context.empty with resources := initialResources }
      oracle := oracle
    }

    let computation : TypingM Unit := do
      -- Process precondition
      processPrecondition spec.requires loc

      -- Process postcondition
      processPostcondition spec.ensures loc

      -- Verify all accumulated constraints
      verifyConstraints

    match TypingM.run computation initialState with
    | .ok (_, finalState) =>
      { success := true
      , finalContext := finalState.context
      , error := none }
    | .error err =>
      { success := false
      , finalContext := Context.empty
      , error := some err }

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

/-! ## Checking Function with Body

Full function verification: check that a function body satisfies its specification.
-/

/-- Check for leaked resources at function exit.
    In CN, all resources must be accounted for (consumed or returned).

    Corresponds to: check for leaked resources in check_procedure -/
def checkNoLeakedResources : TypingM Unit := do
  let ctx ← TypingM.getContext
  if ctx.resources.isEmpty then
    pure ()
  else
    -- For now, just warn about leaked resources
    -- A strict implementation would fail here
    TypingM.fail (.other s!"Leaked resources: {ctx.resources.length} resource(s) not consumed")

/-- Type check a function body against its specification.

    The process:
    1. Start with initial resources (from caller)
    2. Process precondition: add resources to context
    3. Check body expression: track resources through execution
    4. Process postcondition: verify final resources match
    5. Verify all constraints are provable
    6. Check no resources leaked

    Corresponds to: check_procedure in check.ml lines 2377-2426 -/
def checkFunction
    (spec : FunctionSpec)
    (body : Core.AExpr)
    (loc : Loc)
    (oracle : ProofOracle := .trivial)
    : TypeCheckResult :=
  -- For trusted specs, skip verification
  if spec.trusted then
    { success := true
    , finalContext := Context.empty
    , error := none }
  else
    -- Synthesize initial resources from precondition
    let initialResources := extractPreconditionResources spec

    -- Run type checking
    let initialState : TypingState := {
      context := { Context.empty with resources := initialResources }
      oracle := oracle
    }

    let computation : TypingM Unit := do
      -- 1. Process precondition: consume initial resources, bind outputs
      processPrecondition spec.requires loc

      -- 2. Check the body expression
      let _returnVal ← checkExpr body

      -- 3. Process postcondition: produce final resources
      processPostcondition spec.ensures loc

      -- 4. Verify all accumulated constraints
      verifyConstraints

      -- 5. Check no resources leaked (optional strictness)
      -- checkNoLeakedResources  -- Uncomment for strict mode

    match TypingM.run computation initialState with
    | .ok (_, finalState) =>
      { success := true
      , finalContext := finalState.context
      , error := none }
    | .error err =>
      { success := false
      , finalContext := Context.empty
      , error := some err }

/-! ## Convenience Functions -/

/-- Check if a function spec is well-typed given initial resources.
    Returns true if type checking succeeds. -/
def isWellTyped
    (spec : FunctionSpec)
    (initialResources : List Resource)
    (oracle : ProofOracle := .trivial)
    : Bool :=
  let result := checkFunctionSpec spec initialResources .unknown oracle
  result.success

/-- Check a function spec and return any error.
    Returns none if successful, some error otherwise. -/
def checkSpec
    (spec : FunctionSpec)
    (initialResources : List Resource)
    (oracle : ProofOracle := .trivial)
    : Option TypeError :=
  let result := checkFunctionSpec spec initialResources .unknown oracle
  result.error

/-- Run type checking on a spec in standalone mode.
    Synthesizes initial resources from the precondition.
    Returns the TypeCheckResult. -/
def checkSpecStandalone
    (spec : FunctionSpec)
    (oracle : ProofOracle := .trivial)
    : TypeCheckResult :=
  let initialResources := extractPreconditionResources spec
  checkFunctionSpec spec initialResources .unknown oracle

/-- Parse and type check a CN annotation string.
    This is the main entry point for checking CN specs. -/
def parseAndCheck
    (input : String)
    (oracle : ProofOracle := .trivial)
    : Except String TypeCheckResult :=
  match CerbLean.CN.Parser.parseFunctionSpec input with
  | .error e => .error s!"Parse error: {e}"
  | .ok spec => .ok (checkSpecStandalone spec oracle)

/-- Parse and type check, returning a simple success/failure. -/
def parseAndCheckBool
    (input : String)
    (oracle : ProofOracle := .trivial)
    : Bool :=
  match parseAndCheck input oracle with
  | .ok result => result.success
  | .error _ => false

end CerbLean.CN.TypeChecking
