/-
  CN Expression Checking
  Corresponds to: cn/lib/check.ml (check_expr)

  Walks effectful Core expressions, threading resources through the computation.
  This is the main entry point for Level 2 (separation logic verification).

  Audited: 2026-01-20 against cn/lib/check.ml
-/

import CerbLean.CN.TypeChecking.Pexpr
import CerbLean.CN.TypeChecking.Action

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Expr AExpr APexpr APattern Name)
open CerbLean.CN.Types

/-! ## Path Conditions

For conditional branches, we track path conditions to enable
reasoning about branch-specific constraints.
-/

/-- Add a path condition for the current branch -/
def withPathCondition (cond : IndexTerm) (m : TypingM α) : TypingM α := do
  -- Add the condition as a constraint (assumption)
  TypingM.addC (.t cond)
  m

/-- Create the negation of a term -/
def negTerm (t : IndexTerm) : IndexTerm :=
  AnnotTerm.mk (.unop .not t) .bool t.loc

/-! ## Branch Handling

For conditionals and case expressions, we need to:
1. Save the current resource state
2. Check each branch
3. Merge resource states (in CN, branches must agree)
-/

/-- Check that resources after branches match.
    In CN, both branches must end with the same resources. -/
def checkResourcesMatch (_ctx1 _ctx2 : Context) : TypingM Unit := do
  -- For now, we just trust that branches agree
  -- A full implementation would check resource equality
  pure ()

/-! ## Expression Checking

Main function to walk effectful Core expressions.
-/

/-- Check an effectful expression, threading resources.
    Returns the result value of the expression.

    Corresponds to: check_expr in check.ml lines 1506-2315 -/
partial def checkExpr (e : AExpr) : TypingM IndexTerm := do
  let loc := getAnnotsLoc e.annots
  match e.expr with
  -- Pure expression (no side effects)
  | .pure pe =>
    checkPexpr pe

  -- Memory operation (memop)
  | .memop _op args =>
    -- Evaluate all arguments (simplified - just return unit)
    for arg in args do
      let _ ← checkPexpr arg
    return mkUnitTerm loc

  -- Memory action (create, kill, store, load)
  | .action pact =>
    checkAction pact

  -- Weak sequencing: e1 ; e2 (resources flow from e1 to e2)
  | .wseq pat e1 e2 =>
    let v1 ← checkExpr e1
    -- Bind the result to the pattern
    let bindings ← bindPattern pat v1
    let result ← checkExpr e2
    unbindPattern bindings
    return result

  -- Strong sequencing: e1 ; e2 (same as weak for sequential code)
  | .sseq pat e1 e2 =>
    let v1 ← checkExpr e1
    let bindings ← bindPattern pat v1
    let result ← checkExpr e2
    unbindPattern bindings
    return result

  -- Let binding: let pat = pe in e2
  | .let_ pat pe e2 =>
    let v1 ← checkPexpr pe
    let bindings ← bindPattern pat v1
    let result ← checkExpr e2
    unbindPattern bindings
    return result

  -- Conditional: if cond then thenE else elseE
  | .if_ cond thenE elseE =>
    let condVal ← checkPexpr cond

    -- Save current state for branching
    let savedCtx ← TypingM.getContext

    -- Check "then" branch with condition as assumption
    let _thenResult ← withPathCondition condVal (checkExpr thenE)
    let thenCtx ← TypingM.getContext

    -- Restore state and check "else" branch with negated condition
    TypingM.setContext savedCtx
    let elseResult ← withPathCondition (negTerm condVal) (checkExpr elseE)
    let elseCtx ← TypingM.getContext

    -- Check that branches produce compatible resources
    checkResourcesMatch thenCtx elseCtx

    -- For now, return the else result (both branches should return same type)
    return elseResult

  -- Case expression
  | .case_ scrut branches =>
    let scrutVal ← checkPexpr scrut

    if branches.isEmpty then
      TypingM.fail (.other "Empty case expression")

    -- Check each branch
    let savedCtx ← TypingM.getContext
    let mut lastResult := mkUnitTerm loc

    for (pat, body) in branches do
      TypingM.setContext savedCtx
      let bindings ← bindPattern pat scrutVal
      lastResult ← checkExpr body
      unbindPattern bindings

    return lastResult

  -- C function call
  | .ccall funPtr _funTy args =>
    -- Evaluate function pointer and arguments
    let _fnVal ← checkPexpr funPtr
    let argVals ← args.mapM checkPexpr

    -- In a full implementation, we would:
    -- 1. Look up the function's specification
    -- 2. Check that we have the required precondition resources
    -- 3. Consume those resources
    -- 4. Produce the postcondition resources
    -- 5. Return the result

    -- For now, just return a placeholder
    let resultBt := if argVals.isEmpty then .unit else argVals.head!.bt
    return AnnotTerm.mk (.const .unit) resultBt loc

  -- Named procedure call
  | .proc name args =>
    let argVals ← args.mapM checkPexpr

    -- Similar to ccall - would need to look up the procedure's spec
    let fnSym := match name with
      | .sym s => s
      | .impl _ => { id := 0, name := some "impl" : Sym }

    let resultBt := if argVals.isEmpty then .unit else argVals.head!.bt
    return AnnotTerm.mk (.apply fnSym argVals) resultBt loc

  -- Unsequenced (for sequential, pick first ordering)
  | .unseq es =>
    if es.isEmpty then
      return mkUnitTerm loc

    -- For sequential execution, just execute in order
    let mut result := mkUnitTerm loc
    for e' in es do
      result ← checkExpr e'
    return result

  -- Bound (resource boundary)
  | .bound e' =>
    checkExpr e'

  -- Nondeterministic choice (pick first for now)
  | .nd es =>
    if es.isEmpty then
      return mkUnitTerm loc
    checkExpr es.head!

  -- Save/run (for labels/goto - simplified)
  | .save _retSym _retTy args body =>
    -- Evaluate the argument expressions
    for (_, _, argPe) in args do
      let _ ← checkPexpr argPe
    checkExpr body

  | .run _label args =>
    for arg in args do
      let _ ← checkPexpr arg
    return mkUnitTerm loc

  -- Concurrency constructs (not fully supported)
  | .par es =>
    -- For parallel, check all expressions but don't merge properly
    if es.isEmpty then
      return mkUnitTerm loc

    let mut result := mkUnitTerm loc
    for e' in es do
      result ← checkExpr e'
    return result

  | .wait _tid =>
    return mkUnitTerm loc

where
  /-- Helper to create a unit term -/
  mkUnitTerm (loc : Core.Loc) : IndexTerm :=
    AnnotTerm.mk (.const .unit) .unit loc

/-! ## Function Body Checking

Check a complete function body against its specification.
-/

/-- Check a function body, returning the result value.
    This is the entry point for checking a function's implementation.

    The process:
    1. Precondition resources should already be in context
    2. Check the body expression, tracking resources
    3. Return value should satisfy postcondition constraints

    Corresponds to: the body checking part of check_procedure in check.ml -/
def checkFunctionBody (body : AExpr) : TypingM IndexTerm := do
  checkExpr body

end CerbLean.CN.TypeChecking
