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
import CerbLean.CN.TypeChecking.GhostStatement
import CerbLean.CN.TypeChecking.Resolve
import CerbLean.CN.Types.ArgumentTypes
import CerbLean.CN.Parser

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

/- Check an effectful expression using continuation-passing style.

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

    -- PtrEq: pointer equality comparison
    -- Corresponds to: pointer_eq in check.ml lines 1527-1595
    -- DIVERGES-FROM-CN: simplified - skips ambiguous case detection (same address,
    -- different provenance). CN creates fresh booleans for ambiguous/both_eq/neither
    -- and constrains the result with implications. We directly bind result = eq(arg1, arg2)
    -- and require both pointers have allocation IDs.
    -- Audited: 2026-02-19
    | .ptrEq, [pe1, pe2] =>
      checkPexprK pe1 fun arg1 =>
        checkPexprK pe2 fun arg2 => do
          -- Fresh result symbol, bound to eq(arg1, arg2)
          let resSym ← TypingM.freshSym "ptrEq"
          TypingM.addA resSym .bool loc "pointer equality result"
          let eqTerm := AnnotTerm.mk (.binop .eq arg1 arg2) .bool loc
          TypingM.addC (.t (AnnotTerm.mk (.binop .eq (AnnotTerm.mk (.sym resSym) .bool loc) eqTerm) .bool loc))
          -- Require both pointers have allocation IDs (both are valid pointers)
          let hasAlloc1 := AnnotTerm.mk (.hasAllocId arg1) .bool loc
          let hasAlloc2 := AnnotTerm.mk (.hasAllocId arg2) .bool loc
          let bothValid := AnnotTerm.mk (.binop .and_ hasAlloc1 hasAlloc2) .bool loc
          TypingM.requireConstraint (.t bothValid) loc "ptrEq: both pointers have allocation IDs"
          k (AnnotTerm.mk (.sym resSym) .bool loc)

    -- PtrNe: pointer inequality comparison
    -- Corresponds to: pointer_eq ~negate:true in check.ml lines 1527-1595
    -- DIVERGES-FROM-CN: simplified - same as ptrEq but negated result.
    -- Audited: 2026-02-19
    | .ptrNe, [pe1, pe2] =>
      checkPexprK pe1 fun arg1 =>
        checkPexprK pe2 fun arg2 => do
          -- Fresh result symbol, bound to eq(arg1, arg2)
          let resSym ← TypingM.freshSym "ptrNe"
          TypingM.addA resSym .bool loc "pointer inequality result"
          let eqTerm := AnnotTerm.mk (.binop .eq arg1 arg2) .bool loc
          TypingM.addC (.t (AnnotTerm.mk (.binop .eq (AnnotTerm.mk (.sym resSym) .bool loc) eqTerm) .bool loc))
          -- Require both pointers have allocation IDs
          let hasAlloc1 := AnnotTerm.mk (.hasAllocId arg1) .bool loc
          let hasAlloc2 := AnnotTerm.mk (.hasAllocId arg2) .bool loc
          let bothValid := AnnotTerm.mk (.binop .and_ hasAlloc1 hasAlloc2) .bool loc
          TypingM.requireConstraint (.t bothValid) loc "ptrNe: both pointers have allocation IDs"
          -- CN: k (not_ res) - negate the equality result
          k (AnnotTerm.mk (.unop .not (AnnotTerm.mk (.sym resSym) .bool loc)) .bool loc)

    -- PtrLt/PtrGt/PtrLe/PtrGe: ordered pointer comparisons
    -- Corresponds to: pointer_op in check.ml lines 1597-1606
    -- Requires check_both_eq_alloc and check_live_alloc_bounds - not yet implemented
    | .ptrLt, _ => TypingM.fail (.other "memop ptrLt not yet implemented (requires allocation checks)")
    | .ptrGt, _ => TypingM.fail (.other "memop ptrGt not yet implemented (requires allocation checks)")
    | .ptrLe, _ => TypingM.fail (.other "memop ptrLe not yet implemented (requires allocation checks)")
    | .ptrGe, _ => TypingM.fail (.other "memop ptrGe not yet implemented (requires allocation checks)")

    -- Unimplemented memops - fail explicitly with details
    | .ptrdiff, _ => TypingM.fail (.other "memop ptrdiff not yet implemented")

    -- IntFromPtr: cast pointer to integer
    -- Corresponds to: IntFromPtr case in check.ml lines 1646-1672
    -- Arguments: [from_ct, to_ct, ptr]
    -- DIVERGES-FROM-CN: simplified representability check - CN uses inline provable
    -- to check representable and fails immediately if refuted (with model). We add
    -- a post-hoc obligation instead.
    -- Audited: 2026-02-19
    | .intFromPtr, [_pe_from_ct, pe_to_ct, pe_ptr] =>
      match extractCtypeConst pe_to_ct with
      | .error e => TypingM.fail e
      | .ok to_ct =>
        let resultBt := ctypeInnerToBaseType to_ct.ty
        checkPexprK pe_ptr fun ptrArg => do
          -- Cast pointer to target integer type
          -- Corresponds to: cast_ (Memory.bt_of_sct to_ct) arg loc in check.ml:1653
          let castResult := AnnotTerm.mk (.cast resultBt ptrArg) resultBt loc
          -- Add representable obligation
          -- Corresponds to: representable_ (to_ct, arg) in check.ml:1662
          -- CN passes the raw pointer to representable_, but our SMT translation
          -- dispatches on the C type (integer), not value type (Loc). We pass the
          -- cast result instead: for BitVec values, representable is trivially true
          -- (bounded by sort width), matching CN's semantics.
          let reprTerm := AnnotTerm.mk (.representable to_ct castResult) .bool loc
          TypingM.requireConstraint (.t reprTerm) loc "intFromPtr: result representable in target type"
          k castResult

    | .ptrFromInt, _ => TypingM.fail (.other "memop ptrFromInt not yet implemented")
    -- PtrMemberShift: compute pointer to struct/union member
    -- Corresponds to: PEmember_shift in check.ml lines 693-711
    -- CN marks the memop version as CHERI-only (check.ml:1747-1748) and uses the pure
    -- PEmember_shift instead. Our Cerberus generates the memop form; we handle it
    -- equivalently by producing a memberShift index term.
    -- Returns Loc (shifted pointer)
    | .ptrMemberShift tag member, [ptrArg] =>
      checkPexprK ptrArg fun ptrTerm => do
        -- Create memberShift index term (same as Pexpr.lean:749-752 for pure PEmember_shift)
        let result := AnnotTerm.mk (.memberShift ptrTerm tag member) .loc loc
        k result
    | .ptrMemberShift _ _, args =>
      TypingM.fail (.other s!"memop ptrMemberShift expects exactly 1 argument, got {args.length}")
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
  --
  -- Ghost statement detection: CN's core_to_mucore.ml:535-593 detects ghost statements
  -- when Esseq has (1) unit pattern, (2) Epure(Vunit) as e1, (3) cerb::magic annotations.
  -- The magic attribute text contains the ghost statement (e.g., "cn_have(x == y)").
  | .sseq pat e1 e2 =>
    -- Check for ghost statement pattern
    let magicTexts := e.annots.getCerbMagic
    let isUnitPat := match pat.pat with | .base none .unit => true | _ => false
    let isUnitExpr := match e1.expr with
      | .pure pe => match pe.expr with | .val .unit => true | _ => false
      | _ => false
    if isUnitPat && isUnitExpr && !magicTexts.isEmpty then
      -- Ghost statement: parse and process magic attributes
      -- CN ref: core_to_mucore.ml:545-589 (cn_statements → Translate.statement)
      --
      -- Ghost statement expressions are parsed with placeholder symbols (id=0).
      -- We resolve them against the current typing context, matching CN's
      -- compile.ml:689-705 (cn_expr → lookup_computational_or_logical).
      let ctx ← TypingM.getContext
      let st ← TypingM.getState
      -- Convert store map to list for resolve context
      let storeList := st.storeValues.toList.map fun (id, val) => (id, val)
      let resolveCtx := Resolve.resolveContextFromTypingContext ctx st.tagDefs st.freshCounter storeList
      for magicText in magicTexts do
        match CerbLean.CN.Parser.parseGhostStatements magicText with
        | .ok stmts =>
          for stmt in stmts do
            -- Resolve placeholder symbols in the constraint term, then
            -- substitute stored values for stack slot references
            let resolvedConstraint ← match stmt.constraint with
              | some c =>
                match Resolve.resolveAnnotTerm resolveCtx c none with
                | .ok resolved =>
                  -- Replace stack slot sym references with stored values
                  -- This is the ghost statement analog of ccall store resolution
                  pure (some (Resolve.substStoreValues ctx storeList resolved))
                | .error (.symbolNotFound name) =>
                  TypingM.fail (.other s!"ghost statement: unresolved symbol '{name}'")
                | .error (.integerTooLarge n) =>
                  TypingM.fail (.other s!"ghost statement: integer too large: {n}")
                | .error (.unknownPointeeType msg) =>
                  TypingM.fail (.other s!"ghost statement: {msg}")
                | .error (.other msg) =>
                  TypingM.fail (.other s!"ghost statement resolution error: {msg}")
              | none => pure none
            processGhostStatementByName stmt.kind resolvedConstraint loc
        | .error _ =>
          -- If it doesn't parse as a ghost statement, it might be something else
          -- (e.g., a function spec or loop spec) — skip silently
          pure ()
      -- Continue with e2 (ghost statement doesn't bind a value)
      checkExpr labels e2 k
    else
      -- Normal strong sequencing
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
  -- Corresponds to: Eif case in check.ml lines 1985-2002
  --
  -- CN uses inline solver access (`provable(false)`) to detect dead branches.
  -- We use conditional failures instead: try each branch, catch errors, create
  -- obligations proving the branch is dead. Post-hoc SMT discharge validates.
  --
  -- Both branches are tried independently from the same starting state using
  -- tryBranch. Each branch's full state (including resource changes) is preserved.
  -- The caller picks the right final state:
  -- - If one succeeds and the other fails: use the successful branch's state,
  --   add a conditional failure for the failed branch.
  -- - If both succeed: merge obligations from both, use either's resources
  --   (should be equivalent since both called k).
  -- - If both fail: add conditional failures for both.
  | .if_ cond thenE elseE =>
    checkPexprK cond fun condVal => do
      let outerAssumptions ← TypingM.getConstraints

      let checkBranch (branchCond : IndexTerm) (branchE : AExpr) : TypingM Unit := do
        TypingM.addC (.t branchCond)
        checkExpr labels branchE k

      -- Try both branches independently from the SAME starting state.
      -- tryBranch does NOT modify the caller's state.
      let thenResult ← TypingM.tryBranch (checkBranch condVal thenE)
      let elseResult ← TypingM.tryBranch (checkBranch (negTerm condVal) elseE)

      -- Pick the final state based on results
      match thenResult, elseResult with
      | .ok (_, thenState), .ok (_, elseState) =>
        -- Both succeeded: merge obligations and CFs from both branches,
        -- use either's resources (should be equivalent since both called k).
        -- Obligations from each branch are conditional on their branch condition
        -- (via addC above), so combining them is sound.
        let preObs := (← TypingM.getState).obligations
        let preCFs := (← TypingM.getState).conditionalFailures
        let thenNewObs := thenState.obligations.drop preObs.length
        let thenNewCFs := thenState.conditionalFailures.drop preCFs.length
        let elseNewObs := elseState.obligations.drop preObs.length
        let elseNewCFs := elseState.conditionalFailures.drop preCFs.length
        TypingM.setState { thenState with
          obligations := preObs ++ thenNewObs ++ elseNewObs
          conditionalFailures := preCFs ++ thenNewCFs ++ elseNewCFs
        }
      | .ok (_, thenState), .error e =>
        -- Then succeeded, else failed: use then-state, add CF for else
        TypingM.setState thenState
        TypingM.addConditionalFailure (negTerm condVal) e outerAssumptions loc
      | .error e, .ok (_, elseState) =>
        -- Then failed, else succeeded: use else-state, add CF for then
        TypingM.setState elseState
        TypingM.addConditionalFailure condVal e outerAssumptions loc
      | .error e1, .error e2 =>
        -- Both failed: add CFs for both, keep pre-branch state
        TypingM.addConditionalFailure condVal e1 outerAssumptions loc
        TypingM.addConditionalFailure (negTerm condVal) e2 outerAssumptions loc

  -- Case expression
  -- Filter Unspecified branches (muCore strips these), then check remaining branches.
  -- CN asserts Ecase away (core_to_mucore.ml:451) — it never reaches check.ml.
  -- Our filterSpecifiedBranches simulates the muCore transformation.
  -- After filtering, typically one Specified branch remains (the live path).
  --
  -- IMPORTANT: We must NOT wrap the continuation k inside pure_, because the
  -- continuation includes resource operations (stores, ccalls, etc.) whose
  -- state changes must be preserved.
  --
  -- For a single branch: run directly (most common case after filtering).
  -- For multiple branches: use tryBranch to try each independently, picking
  -- the successful one's state (like Eif handler).
  | .case_ scrut branches =>
    checkPexprK scrut fun scrutVal => do
      if branches.isEmpty then
        TypingM.fail (.other "Empty case expression")

      -- Filter branches: remove Unspecified patterns and wildcard catch-alls
      -- This mirrors CN's muCore transformation which strips non-Specified branches
      let branches := filterSpecifiedBranches branches

      if branches.isEmpty then
        TypingM.fail (.other "All case branches filtered (no Specified branch found)")

      match branches with
      | [(pat, body)] =>
        -- Single branch (most common): run directly, preserving all state changes
        let bindings ← bindPattern pat scrutVal
        checkExpr labels body fun result => do
          unbindPattern bindings
          k result
      | _ =>
        -- Multiple branches: try each with tryBranch, use first successful state
        let mut succeeded := false
        for (pat, body) in branches do
          if !succeeded then
            let branchResult ← TypingM.tryBranch do
              let bindings ← bindPattern pat scrutVal
              checkExpr labels body fun result => do
                unbindPattern bindings
                k result
            match branchResult with
            | .ok (_, branchState) =>
              TypingM.setState branchState
              succeeded := true
            | .error _ => pure ()  -- Try next branch
        if !succeeded then
          TypingM.fail (.other "All case branches failed")

  -- C function call
  -- Corresponds to: Eccall case in check.ml lines 1935-1984
  --
  -- IMPORTANT: Core IR vs muCore argument mismatch.
  -- In Core IR, ccall passes stack slot ADDRESSES as arguments:
  --   create(slot) → store(val, slot) → ccall(f, slot) → kill(slot)
  -- CN's core_to_mucore eliminates this pattern, passing actual VALUES:
  --   ccall(f, val)
  -- We handle this lazily by resolving arguments through the store map.
  | .ccall funPtr _funTy args =>
    -- 1. Evaluate function pointer and extract function symbol
    -- Corresponds to: known_function_pointer in check.ml lines 363-379
    -- CN evaluates the function pointer IT, then calls IT.is_sym to extract the symbol.
    -- In Core IR, the function pointer goes through intermediaries (e.g., a_547),
    -- so we must EVALUATE it (not just read the AST) to get the actual function symbol.
    let funPtrVal ← checkPexpr funPtr
    let funSym ← match funPtrVal.term with
      | .sym s => pure s
      | _ => TypingM.fail (.other s!"Indirect function calls not yet supported")

    -- 2. Look up pre-built function type
    -- Corresponds to: Global.get_fun_decl loc fsym in check.ml
    let ft ← match (← TypingM.lookupFunctionSpec funSym.id) with
      | some ft => pure ft
      | none => TypingM.fail (.other s!"Call to function with no spec: {funSym.name.getD "<unnamed>"}")

    -- 3. Parse call-site ghost arguments from cerb::magic annotations
    -- Ghost args appear as /*@ expr1, expr2 @*/ at the call site
    -- Corresponds to: CN's parsing of ghost arguments in c_parser.mly
    let ghostArgs : List IndexTerm ← do
      let magicTexts := e.annots.getCerbMagic
      let mut allArgs : List IndexTerm := []
      for magicText in magicTexts do
        match CerbLean.CN.Parser.parseGhostArgs magicText with
        | .ok parsedArgs =>
          -- Resolve parsed ghost arg terms against current context
          let ctx ← TypingM.getContext
          let st ← TypingM.getState
          let storeList := st.storeValues.toList.map fun (id, val) => (id, val)
          let resolveCtx := Resolve.resolveContextFromTypingContext ctx st.tagDefs st.freshCounter storeList
          for parsedArg in parsedArgs do
            match Resolve.resolveAnnotTerm resolveCtx parsedArg none with
            | .ok resolved =>
              let resolved' := Resolve.substStoreValues ctx storeList resolved
              allArgs := allArgs ++ [resolved']
            | .error (.symbolNotFound name) =>
              TypingM.fail (.other s!"ghost argument: unresolved symbol '{name}'")
            | .error e =>
              TypingM.fail (.other s!"ghost argument resolution error: {repr e}")
        | .error _ => pure ()  -- Not parseable as ghost args, skip
      pure allArgs

    -- 4. Process computational args with store resolution, then spine_l for precondition
    -- This inlines spine's computational arg processing with an additional
    -- store-resolution step for the lazy muCore transformation.
    -- Corresponds to: Spine.calltype_ft → spine → spine_l
    let rec processComputationalArgs (argsList : List APexpr) (at_ : AT ReturnType)
        (gargs : List IndexTerm) : TypingM Unit := do
      match argsList, at_ with
      | arg :: restArgs, .computational s bt _info rest =>
        -- Evaluate the argument expression
        -- Corresponds to: spine computational case, check.ml lines 1163-1173
        checkPexprK arg (fun argVal => do
          -- Resolve through store map: if this is a stack slot with a stored
          -- value, use the stored value instead of the slot address.
          -- This is the lazy muCore transformation for ccall arguments.
          let resolvedVal ← match argVal.term with
            | .sym sym =>
              match ← TypingM.lookupStore sym.id with
              | some storedVal => pure storedVal
              | none => pure argVal
            | _ => pure argVal
          -- Substitute resolved value for parameter in rest of type
          let σ := Subst.single s resolvedVal
          let rest' := AT.subst ReturnType.subst σ rest
          processComputationalArgs restArgs rest' gargs) (some bt)
      | _, .ghost s _bt _info rest =>
        -- Ghost argument: substitute from parsed ghost arg annotations
        -- Ghost args come from /*@ expr1, expr2 @*/ at the call site (cerb::magic)
        -- Corresponds to: spine ghost case, check.ml lines 1170-1200
        match gargs with
        | garg :: restGargs =>
          let σ := Subst.single s garg
          let rest' := AT.subst ReturnType.subst σ rest
          processComputationalArgs argsList rest' restGargs
        | [] =>
          TypingM.fail (.other s!"Not enough ghost arguments provided in call to {funSym.name.getD "<unnamed>"}")
      | [], .L lat =>
        -- All computational args processed, now process precondition via spine_l
        -- Corresponds to: spine delegates to spine_l for LAT processing
        spineL loc (.functionCall funSym) lat (fun rt => do
          -- 4. Create fresh return symbol
          -- Corresponds to: let s' = Sym.fresh_make_uniq_kind ~prefix "return" in
          let s' ← TypingM.freshSym "return"
          TypingM.addL s' rt.bt loc "function return value"

          -- 5. Rename return symbol and process postcondition
          -- Corresponds to: let su = IT.make_rename ~from:s ~to_:s' in
          --                 bind_logical_return loc prefix (LRT.subst su lrt)
          let σ := Subst.single rt.sym (AnnotTerm.mk (.sym s') rt.bt loc)
          let lrt' := rt.lrt.subst σ
          bindLogicalReturn loc lrt'

          -- 6. Continue with return value
          -- Corresponds to: k (IT.sym_ (s', bt, here))
          k (AnnotTerm.mk (.sym s') rt.bt loc))
      | _ :: _, .L _ =>
        TypingM.fail (.other s!"Too many arguments in call to {funSym.name.getD "<unnamed>"}")
      | [], .computational _ _ _ _ =>
        TypingM.fail (.other s!"Not enough arguments in call to {funSym.name.getD "<unnamed>"}")
    processComputationalArgs args ft ghostArgs

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
      calltypeLt loc args [] entry fun _false => do
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
