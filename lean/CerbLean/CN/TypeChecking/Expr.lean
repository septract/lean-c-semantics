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
  -- Corresponds to: Ememop case in check.ml lines 1524-1777
  | .memop op args =>
    match op, args with
    -- PtrValidForDeref: check if pointer is valid for dereferencing
    -- Corresponds to: check.ml lines 1700-1715
    -- Returns Bool (aligned_ term)
    | .ptrValidForDeref, [pe_ct, pe] =>
      match extractCtypeConst pe_ct with
      | .error e => TypingM.fail e
      | .ok ct =>
        match alignOfCtype ct with
        | none => TypingM.fail (.other s!"Cannot compute alignment for type: {repr ct}")
        | some alignVal =>
          checkPexprK pe fun ptrTerm => do
            -- Create aligned(ptr, align) term with Bool type
            let alignTerm := AnnotTerm.mk (.const (.bits .unsigned 64 alignVal)) (.bits .unsigned 64) loc
            let result := AnnotTerm.mk (.aligned ptrTerm alignTerm) .bool loc
            k result

    -- PtrWellAligned: same as PtrValidForDeref
    -- Corresponds to: check.ml lines 1716-1725
    | .ptrWellAligned, [pe_ct, pe] =>
      match extractCtypeConst pe_ct with
      | .error e => TypingM.fail e
      | .ok ct =>
        match alignOfCtype ct with
        | none => TypingM.fail (.other s!"Cannot compute alignment for type: {repr ct}")
        | some alignVal =>
          checkPexprK pe fun ptrTerm => do
            let alignTerm := AnnotTerm.mk (.const (.bits .unsigned 64 alignVal)) (.bits .unsigned 64) loc
            let result := AnnotTerm.mk (.aligned ptrTerm alignTerm) .bool loc
            k result

    -- PtrArrayShift: pointer arithmetic (base + index * sizeof(element))
    -- Corresponds to: check.ml lines 1726-1746
    -- Returns Loc (pointer type)
    | .ptrArrayShift, [pe_base, pe_ct, pe_idx] =>
      match extractCtypeConst pe_ct with
      | .error e => TypingM.fail e
      | .ok ct =>
        checkPexprK pe_base fun baseTerm =>
          checkPexprK pe_idx fun idxTerm => do
            -- Cast index to uintptr type (CN invariant: ArrayShift index must be uintptr)
            let castIdx := AnnotTerm.mk (.cast (.bits .unsigned 64) idxTerm) (.bits .unsigned 64) loc
            let result := AnnotTerm.mk (.arrayShift baseTerm ct castIdx) .loc loc
            k result

    -- Pointer comparisons: NOT YET IMPLEMENTED
    -- CN's pointer comparison (check.ml lines 1525-1618) involves:
    -- - For PtrEq/PtrNe: complex constraint involving hasAllocId_, allocId_, addr_,
    --   and handling of ambiguous cases (same address, different provenance)
    -- - For PtrLt/PtrGt/PtrLe/PtrGe: check_both_eq_alloc and check_live_alloc_bounds
    --   side condition checks before creating ltPointer_/lePointer_ terms
    -- These are NOT simple binary operations - they have semantic side effects.
    | .ptrEq, _ => TypingM.fail (.other "memop ptrEq not yet implemented (requires provenance handling)")
    | .ptrNe, _ => TypingM.fail (.other "memop ptrNe not yet implemented (requires provenance handling)")
    | .ptrLt, _ => TypingM.fail (.other "memop ptrLt not yet implemented (requires allocation checks)")
    | .ptrGt, _ => TypingM.fail (.other "memop ptrGt not yet implemented (requires allocation checks)")
    | .ptrLe, _ => TypingM.fail (.other "memop ptrLe not yet implemented (requires allocation checks)")
    | .ptrGe, _ => TypingM.fail (.other "memop ptrGe not yet implemented (requires allocation checks)")

    -- Unimplemented memops - fail explicitly with details
    | .ptrdiff, _ => TypingM.fail (.other "memop ptrdiff not yet implemented")
    | .intFromPtr, _ => TypingM.fail (.other "memop intFromPtr not yet implemented")
    | .ptrFromInt, _ => TypingM.fail (.other "memop ptrFromInt not yet implemented")
    | .ptrMemberShift _ _, _ => TypingM.fail (.other "memop ptrMemberShift not yet implemented")
    | .memcpy, _ => TypingM.fail (.other "memop memcpy not yet implemented")
    | .memcmp, _ => TypingM.fail (.other "memop memcmp not yet implemented")
    | .realloc, _ => TypingM.fail (.other "memop realloc not yet implemented")
    | .vaStart, _ => TypingM.fail (.other "memop vaStart not yet implemented")
    | .vaCopy, _ => TypingM.fail (.other "memop vaCopy not yet implemented")
    | .vaArg, _ => TypingM.fail (.other "memop vaArg not yet implemented")
    | .vaEnd, _ => TypingM.fail (.other "memop vaEnd not yet implemented")
    | .copyAllocId, _ => TypingM.fail (.other "memop copyAllocId not yet implemented")
    | .cheriIntrinsic _, _ => TypingM.fail (.other "memop cheriIntrinsic not yet implemented")

    -- Argument count mismatch - fail with details
    | _, _ => TypingM.fail (.other s!"memop {repr op} called with wrong number of arguments: {args.length}")

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
  -- Filter Unspecified branches (muCore strips these), then check ALL
  -- remaining branches speculatively with pure_ (like Eif checks both branches).
  -- CN asserts Ecase away (core_to_mucore.ml:451) — it never reaches check.ml.
  -- Our filterSpecifiedBranches simulates the muCore transformation.
  -- After filtering, remaining branches are all reachable paths (like if/else).
  -- Corresponds to: Eif in check.ml lines 1985-2002 (similar pattern)
  | .case_ scrut branches =>
    checkPexprK scrut fun scrutVal => do
      if branches.isEmpty then
        TypingM.fail (.other "Empty case expression")

      -- Filter branches: remove Unspecified patterns and wildcard catch-alls
      -- This mirrors CN's muCore transformation which strips non-Specified branches
      let branches := filterSpecifiedBranches branches

      if branches.isEmpty then
        TypingM.fail (.other "All case branches filtered (no Specified branch found)")

      -- Check each remaining branch speculatively (errors propagate)
      for (pat, body) in branches do
        let _ ← TypingM.pure_ do
          let bindings ← bindPattern pat scrutVal
          checkExpr labels body fun result => do
            unbindPattern bindings
            k result
      pure ()

  -- C function call
  -- Corresponds to: Eccall case in check.ml lines 2018-2080
  | .ccall _funPtr _funTy _args =>
    -- C function call requires:
    -- 1. Looking up the function's specification
    -- 2. Checking precondition resources via Spine.calltype_ft
    -- 3. Consuming/producing resources
    -- 4. Calling continuation with result
    TypingM.fail (.other "ccall not implemented - requires function specification lookup")

  -- Named procedure call
  -- Corresponds to: Eproc case in check.ml
  | .proc name _args =>
    -- Named procedure call requires:
    -- 1. Looking up the function's specification
    -- 2. Checking precondition resources
    -- 3. Consuming/producing resources
    -- 4. Calling continuation with properly typed result
    let nameStr := match name with
      | .sym s => s.name.getD "?"
      | .impl _ => "impl"
    TypingM.fail (.other s!"proc call not implemented: {nameStr}")

  -- Unsequenced (for sequential, pick first ordering)
  -- Corresponds to: Eunseq case in check.ml
  --
  -- IMPORTANT: In Core, unseq(e1, e2, ..., en) returns a TUPLE of all results (v1, v2, ..., vn).
  -- This is used for binding multiple values in tuple patterns like:
  --   let weak (a_524: loaded integer, a_525: loaded integer) = unseq(load(...), pure(...))
  --
  -- We evaluate all expressions and construct a tuple term with proper element types.
  | .unseq es =>
    if es.isEmpty then
      k (mkUnitTermExpr loc)
    else if es.length == 1 then
      -- Single expression: return its result directly
      checkExpr labels es.head! k
    else
      -- Multiple expressions: evaluate all and return a tuple
      -- Use CPS to collect all results
      let rec collectResults (remaining : List AExpr) (acc : List IndexTerm)
          : TypingM Unit := do
        match remaining with
        | [] =>
          -- All expressions evaluated, construct tuple term
          -- Create proper tuple type with ALL element types
          let elemTypes := acc.map (·.bt)
          let tupleBt := BaseType.tuple elemTypes
          let tupleTermInner := Term.tuple acc
          let tupleTerm := AnnotTerm.mk tupleTermInner tupleBt loc
          k tupleTerm
        | e' :: rest =>
          checkExpr labels e' fun v => collectResults rest (acc ++ [v])
      collectResults es []

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
      let _originalResources ← TypingM.getResources

      -- Call Spine.calltypeLt with the label type and kind
      -- The continuation receives False (uninhabited) - never actually called
      calltypeLt loc args entry fun _false => do
        -- After the label call, check that all resources are consumed
        -- Corresponds to: all_empty loc original_resources
        let remainingResources ← TypingM.getResources
        if !remainingResources.isEmpty then
          TypingM.fail (.other s!"Leaked resources: {remainingResources.length} resource(s) not consumed after label call")
        pure ()

  -- Concurrency constructs - not supported
  -- Corresponds to: Epar case in check.ml
  | .par _es =>
    TypingM.fail (.other "par (parallel) expressions not supported")

  -- Corresponds to: Ewait case in check.ml
  | .wait _tid =>
    TypingM.fail (.other "wait expressions not supported")

  -- Dynamic annotations for race detection (runtime construct, not used by CN)
  | .annot _dynAnnots _e =>
    TypingM.fail (.other "annot expressions not supported in CN type checking")

  -- Excluded wrapper for neg action transformation (runtime construct, not used by CN)
  | .excluded _exclId _act =>
    TypingM.fail (.other "excluded expressions not supported in CN type checking")

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
      let _originalResources ← TypingM.getResources

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
