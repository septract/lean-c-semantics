/-
  CN Expression Checking (CPS Style)
  Corresponds to: cn/lib/check.ml (check_expr)

  Walks effectful Core expressions using continuation-passing style (CPS).
  This matches CN's approach where each branch is verified independently
  by calling the continuation for each path.

  Key design:
  - checkExprK takes a continuation `k : IndexTerm → TypingM Unit`
  - Branches use `pure_` to isolate state changes (each branch is speculative)
  - The continuation is called for each path that reaches an exit point

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

/-! ## Expression Checking (CPS Style)

Main function to walk effectful Core expressions with continuation-passing.

In CN, check_expr has signature:
  check_expr : labels → expr → (IT.t → unit m) → unit m

The continuation `k` receives the computed value and performs further verification.
For branches, both paths call the same continuation independently.
-/

/-- Helper to create a unit term -/
private def mkUnitTermExpr (loc : Core.Loc) : IndexTerm :=
  AnnotTerm.mk (.const .unit) .unit loc

/-- Evaluate a list of arguments in CPS style, collecting results.
    The final continuation receives all evaluated argument terms. -/
private def evalArgsK (args : List APexpr) (k : List IndexTerm → TypingM Unit) : TypingM Unit := do
  let rec go (remaining : List APexpr) (acc : List IndexTerm) : TypingM Unit := do
    match remaining with
    | [] => k acc.reverse
    | arg :: rest =>
      checkPexprK arg fun argVal =>
        go rest (argVal :: acc)
  go args []

/-- Check an effectful expression using continuation-passing style.

    The continuation `k` is called with the result value for each
    path through the expression. For branches, this means `k` may
    be called multiple times (once per branch).

    Corresponds to: check_expr in check.ml lines 1506-2315 -/
partial def checkExprK (e : AExpr) (k : IndexTerm → TypingM Unit) : TypingM Unit := do
  let loc := getAnnotsLoc e.annots
  match e.expr with
  -- Pure expression (no side effects)
  | .pure pe =>
    checkPexprK pe k

  -- Memory operation (memop)
  | .memop _op args =>
    -- Evaluate all arguments (simplified)
    for arg in args do
      checkPexprK arg fun _ => pure ()
    k (mkUnitTermExpr loc)

  -- Memory action (create, kill, store, load)
  | .action pact =>
    checkActionK pact k

  -- Weak sequencing: e1 ; e2 (resources flow from e1 to e2)
  | .wseq pat e1 e2 =>
    checkExprK e1 fun v1 => do
      let bindings ← bindPattern pat v1
      checkExprK e2 fun result => do
        unbindPattern bindings
        k result

  -- Strong sequencing: e1 ; e2 (same as weak for sequential code)
  | .sseq pat e1 e2 =>
    checkExprK e1 fun v1 => do
      let bindings ← bindPattern pat v1
      checkExprK e2 fun result => do
        unbindPattern bindings
        k result

  -- Let binding: let pat = pe in e2
  | .let_ pat pe e2 =>
    checkPexprK pe fun v1 => do
      let bindings ← bindPattern pat v1
      checkExprK e2 fun result => do
        unbindPattern bindings
        k result

  -- Conditional: if cond then thenE else elseE
  -- CPS style: both branches call the same continuation independently
  -- Each branch is checked speculatively with `pure_` to isolate state
  -- Corresponds to: Eif case in check.ml lines 1985-2002
  | .if_ cond thenE elseE =>
    checkPexprK cond fun condVal => do
      -- Helper: check a branch with a path condition
      let checkBranch (branchCond : IndexTerm) (branchE : AExpr) : TypingM Unit := do
        TypingM.addC (.t branchCond)
        checkExprK branchE k

      -- Check both branches speculatively (state changes are discarded)
      -- This matches CN's: pure (aux carg "true" e1)
      let _ ← TypingM.pure_ (checkBranch condVal thenE)
      let _ ← TypingM.pure_ (checkBranch (negTerm condVal) elseE)
      pure ()

  -- Case expression
  -- Each branch is checked speculatively with its pattern binding
  | .case_ scrut branches =>
    checkPexprK scrut fun scrutVal => do
      if branches.isEmpty then
        TypingM.fail (.other "Empty case expression")

      -- Check each branch speculatively
      for (pat, body) in branches do
        let _ ← TypingM.pure_ do
          let bindings ← bindPattern pat scrutVal
          checkExprK body fun result => do
            unbindPattern bindings
            k result
      pure ()

  -- C function call
  | .ccall funPtr _funTy args =>
    -- Evaluate function pointer
    checkPexprK funPtr fun _fnVal => do
      -- Evaluate arguments
      evalArgsK args fun argVals => do
        -- In a full implementation, we would:
        -- 1. Look up the function's specification
        -- 2. Check precondition resources
        -- 3. Consume/produce resources
        -- 4. Call continuation with result

        let resultBt := if argVals.isEmpty then .unit else argVals.head!.bt
        k (AnnotTerm.mk (.const .unit) resultBt loc)

  -- Named procedure call
  | .proc name args =>
    evalArgsK args fun argVals => do
      let fnSym := match name with
        | .sym s => s
        | .impl _ => { id := 0, name := some "impl" : Sym }

      let resultBt := if argVals.isEmpty then .unit else argVals.head!.bt
      k (AnnotTerm.mk (.apply fnSym argVals) resultBt loc)

  -- Unsequenced (for sequential, pick first ordering)
  | .unseq es =>
    if es.isEmpty then
      k (mkUnitTermExpr loc)
    else
      -- Execute in order, continuation called at end
      let rec execSeq (remaining : List AExpr) : TypingM Unit := do
        match remaining with
        | [] => k (mkUnitTermExpr loc)
        | [e'] => checkExprK e' k
        | e' :: rest =>
          checkExprK e' fun _ => execSeq rest
      execSeq es

  -- Bound (resource boundary)
  | .bound e' =>
    checkExprK e' k

  -- Nondeterministic choice
  -- Each alternative is checked speculatively
  | .nd es =>
    if es.isEmpty then
      k (mkUnitTermExpr loc)
    else
      for e' in es do
        let _ ← TypingM.pure_ (checkExprK e' k)
      pure ()

  -- Save/run (for labels/goto)
  | .save _retSym _retTy args body =>
    -- Bind save parameters as variables in scope
    let mut bindings : List (Sym × BaseType) := []
    for (sym, bt, _defaultPe) in args do
      let cnBt := coreBaseTypeToCN bt
      TypingM.addL sym cnBt loc s!"save parameter {sym.name.getD ""}"
      bindings := (sym, cnBt) :: bindings
    -- Check body with parameters in scope
    checkExprK body fun result => do
      -- Unbind parameters (in reverse order)
      for (sym, _) in bindings do
        TypingM.modifyContext fun ctx =>
          { ctx with logical := ctx.logical.filter (·.1.id != sym.id) }
      k result

  | .run _label args =>
    for arg in args do
      checkPexprK arg fun _ => pure ()
    k (mkUnitTermExpr loc)

  -- Concurrency constructs (not fully supported)
  | .par es =>
    if es.isEmpty then
      k (mkUnitTermExpr loc)
    else
      -- For parallel, check each speculatively
      for e' in es do
        let _ ← TypingM.pure_ (checkExprK e' k)
      pure ()

  | .wait _tid =>
    k (mkUnitTermExpr loc)

end CerbLean.CN.TypeChecking
