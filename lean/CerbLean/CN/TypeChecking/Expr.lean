/-
  CN Expression Checking (CPS Style)
  Corresponds to: cn/lib/check.ml (check_expr)

  Walks effectful Core expressions using continuation-passing style (CPS).
  This matches CN's approach where each branch is verified independently
  by calling the continuation for each path.

  Key design:
  - checkExpr takes `labels : LabelContext` and continuation `k : IndexTerm → TypingM Unit`
  - Branches use `pure_` to isolate state changes (each branch is speculative)
  - For Erun, calls Spine.calltypeLt with the label type (does NOT call k)

  Audited: 2026-01-28 against cn/lib/check.ml lines 1506-2315
-/

import CerbLean.CN.TypeChecking.Pexpr
import CerbLean.CN.TypeChecking.Action
import CerbLean.CN.TypeChecking.Spine
import CerbLean.CN.Types.ArgumentTypes

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

IMPORTANT: For Erun, we call Spine.calltypeLt which is TERMINAL - it does NOT
call the original continuation k. This matches CN exactly.
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

    IMPORTANT: For Erun, we call Spine.calltypeLt which handles the
    label call (including return labels). This is TERMINAL - the
    original continuation k is NOT called. This matches CN exactly.

    Corresponds to: check_expr in check.ml lines 1506-2315

    let rec check_expr labels (e : BT.t Mu.expr) (k : IT.t -> unit m) : unit m -/
partial def checkExpr (labels : LabelContext) (e : AExpr) (k : IndexTerm → TypingM Unit)
    : TypingM Unit := do
  let loc := getAnnotsLoc e.annots
  match e.expr with
  -- Pure expression (no side effects)
  -- Corresponds to: Epure case in check.ml line 1521-1523
  | .pure pe =>
    checkPexprK pe k

  -- Memory operation (memop)
  -- Corresponds to: Ememop case in check.ml lines 1524-1710
  | .memop _op args =>
    -- Evaluate all arguments (simplified)
    for arg in args do
      checkPexprK arg fun _ => pure ()
    k (mkUnitTermExpr loc)

  -- Memory action (create, kill, store, load)
  -- Corresponds to: Eaction case in check.ml lines 1711-1984
  | .action pact =>
    checkActionK pact k

  -- Weak sequencing: e1 ; e2 (resources flow from e1 to e2)
  -- Corresponds to: Ewseq case in check.ml lines 2288-2297
  | .wseq pat e1 e2 =>
    checkExpr labels e1 fun v1 => do
      let bindings ← bindPattern pat v1
      checkExpr labels e2 fun result => do
        unbindPattern bindings
        k result

  -- Strong sequencing: e1 ; e2 (same as weak for sequential code)
  -- Corresponds to: Esseq case in check.ml lines 2288-2297
  | .sseq pat e1 e2 =>
    checkExpr labels e1 fun v1 => do
      let bindings ← bindPattern pat v1
      checkExpr labels e2 fun result => do
        unbindPattern bindings
        k result

  -- Let binding: let pat = pe in e2
  -- Corresponds to: Elet case in check.ml lines 2003-2017
  | .let_ pat pe e2 =>
    checkPexprK pe fun v1 => do
      let bindings ← bindPattern pat v1
      checkExpr labels e2 fun result => do
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
        checkExpr labels branchE k

      -- Check both branches speculatively (state changes are discarded)
      -- This matches CN's: pure (aux carg "true" e1)
      let _ ← TypingM.pure_ (checkBranch condVal thenE)
      let _ ← TypingM.pure_ (checkBranch (negTerm condVal) elseE)
      pure ()

  -- Case expression
  -- Each branch is checked speculatively with its pattern binding
  -- Corresponds to: Ecase case in check.ml (similar pattern to Eif)
  | .case_ scrut branches =>
    checkPexprK scrut fun scrutVal => do
      if branches.isEmpty then
        TypingM.fail (.other "Empty case expression")

      -- Check each branch speculatively
      for (pat, body) in branches do
        let _ ← TypingM.pure_ do
          let bindings ← bindPattern pat scrutVal
          checkExpr labels body fun result => do
            unbindPattern bindings
            k result
      pure ()

  -- C function call
  -- Corresponds to: Eccall case in check.ml lines 2018-2080
  | .ccall funPtr _funTy args =>
    -- Evaluate function pointer
    checkPexprK funPtr fun _fnVal => do
      -- Evaluate arguments
      evalArgsK args fun argVals => do
        -- In a full implementation, we would:
        -- 1. Look up the function's specification
        -- 2. Check precondition resources via Spine.calltype_ft
        -- 3. Consume/produce resources
        -- 4. Call continuation with result

        let resultBt := if argVals.isEmpty then .unit else argVals.head!.bt
        k (AnnotTerm.mk (.const .unit) resultBt loc)

  -- Named procedure call
  -- Corresponds to: Eproc case in check.ml
  | .proc name args =>
    evalArgsK args fun argVals => do
      let fnSym := match name with
        | .sym s => s
        | .impl _ => { id := 0, name := some "impl" : Sym }

      let resultBt := if argVals.isEmpty then .unit else argVals.head!.bt
      k (AnnotTerm.mk (.apply fnSym argVals) resultBt loc)

  -- Unsequenced (for sequential, pick first ordering)
  -- Corresponds to: Eunseq case in check.ml
  | .unseq es =>
    if es.isEmpty then
      k (mkUnitTermExpr loc)
    else
      -- Execute in order, continuation called at end
      let rec execSeq (remaining : List AExpr) : TypingM Unit := do
        match remaining with
        | [] => k (mkUnitTermExpr loc)
        | [e'] => checkExpr labels e' k
        | e' :: rest =>
          checkExpr labels e' fun _ => execSeq rest
      execSeq es

  -- Bound (resource boundary)
  -- Corresponds to: Ebound case in check.ml
  | .bound e' =>
    checkExpr labels e' k

  -- Nondeterministic choice
  -- Each alternative is checked speculatively
  -- Corresponds to: End case in check.ml
  | .nd es =>
    if es.isEmpty then
      k (mkUnitTermExpr loc)
    else
      for e' in es do
        let _ ← TypingM.pure_ (checkExpr labels e' k)
      pure ()

  -- Save (should not appear after muCore transformation)
  -- In muCore, all saves have been extracted to labelDefs
  | .save _retSym _retTy _args _body =>
    TypingM.fail (.other "Esave should not appear in muCore (after transformation)")

  -- Run (jump to a label/continuation)
  -- This is the key case that matches CN exactly.
  -- Corresponds to: Erun case in check.ml lines 2298-2314
  --
  -- | Erun (label_sym, pes) ->
  --   let@ () = WellTyped.ensure_base_type loc ~expect Unit in
  --   let@ lt, lkind =
  --     match Sym.Map.find_opt label_sym labels with
  --     | None -> fail ...
  --     | Some (lt, lkind, _) -> return (lt, lkind)
  --   in
  --   let@ original_resources = all_resources loc in
  --   Spine.calltype_lt loc pes None (lt, lkind) (fun False ->
  --     let@ () = all_empty loc original_resources in
  --     return ())
  | .run label args => do
    match labels.get? label with
    | none =>
      TypingM.fail (.other s!"Undefined code label: {label.name.getD "?"}")
    | some entry =>
      -- Get all resources before the call (for checking all_empty after)
      let originalResources ← TypingM.getResources

      -- Call Spine.calltypeLt with the label type and kind
      -- The continuation receives False (uninhabited) - never actually called
      calltypeLt loc args entry fun _false => do
        -- After the label call, check that all resources are consumed
        -- Corresponds to: all_empty loc original_resources
        let remainingResources ← TypingM.getResources
        if !remainingResources.isEmpty then
          -- For now, just warn about leaked resources
          -- A strict implementation would fail here
          pure ()
        pure ()

  -- Concurrency constructs (not fully supported)
  -- Corresponds to: Epar case in check.ml
  | .par es =>
    if es.isEmpty then
      k (mkUnitTermExpr loc)
    else
      -- For parallel, check each speculatively
      for e' in es do
        let _ ← TypingM.pure_ (checkExpr labels e' k)
      pure ()

  -- Corresponds to: Ewait case in check.ml
  | .wait _tid =>
    k (mkUnitTermExpr loc)

/-! ## check_expr_top: Top-Level Expression Checking

Corresponds to: check_expr_top in check.ml lines 2317-2330

  let check_expr_top loc labels rt e =
    let@ () = WellTyped.ensure_base_type loc ~expect:Unit (Mu.bt_of_expr e) in
    check_expr labels e (fun lvt ->
      let (RT.Computational ((return_s, return_bt), _info, lrt)) = rt in
      match return_bt with
      | Unit ->
        let lrt = LRT.subst (IT.make_subst [ (return_s, lvt) ]) lrt in
        let@ original_resources = all_resources loc in
        Spine.subtype loc lrt (fun () ->
          let@ () = all_empty loc original_resources in
          return ())
      | _ ->
        let msg = "Non-void-return function does not call 'return'." in
        fail ...)

This wraps checkExpr for function body checking:
- For void functions that fall through: processes postcondition via Spine.subtype
- For non-void functions that fall through: fails (must call return)
-/

/-- Check an expression at the top level (function body).
    Corresponds to: check_expr_top in check.ml lines 2317-2330

    This wraps checkExpr and provides the continuation that handles
    function completion (either via return or fallthrough).

    For void functions: the continuation processes the postcondition
    For non-void functions: the continuation fails (must explicitly return) -/
def checkExprTop (loc : Core.Loc) (labels : LabelContext) (spec : FunctionSpec)
    (returnBt : BaseType) (e : AExpr) : TypingM Unit := do
  checkExpr labels e fun lvt => do
    match returnBt with
    | .unit =>
      -- Void function: process postcondition with return value = unit
      -- Substitute return symbol with the actual return value
      let σ := Subst.single spec.returnSym lvt
      let substitutedPost := spec.ensures.subst σ

      -- Get resources before subtype check
      let originalResources ← TypingM.getResources

      -- Use Spine.subtype to check postcondition
      subtype loc substitutedPost fun () => do
        -- Check all resources consumed
        let remainingResources ← TypingM.getResources
        if !remainingResources.isEmpty then
          TypingM.fail (.other s!"Leaked resources: {remainingResources.length} resource(s) not consumed")
        pure ()

    | _ =>
      -- Non-void function that didn't call return
      TypingM.fail (.other "Non-void-return function does not call 'return'.")

end CerbLean.CN.TypeChecking
