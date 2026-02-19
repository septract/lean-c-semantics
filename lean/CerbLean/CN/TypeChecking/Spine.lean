/-
  CN Spine Judgment
  Corresponds to: cn/lib/check.ml (Spine module)

  The spine judgment processes argument types (AT) by:
  1. Processing computational arguments (substituting values)
  2. Processing ghost arguments (logical only)
  3. Processing the logical part (LAT) via spine_l

  For label types (AT False_), the spine judgment handles:
  - Return labels: substitutes return value, processes postcondition
  - Regular labels: checks label body

  Audited: 2026-01-28 against cn/lib/check.ml lines 1122-1220
-/

import CerbLean.CN.TypeChecking.Monad
import CerbLean.CN.TypeChecking.Pexpr
import CerbLean.CN.TypeChecking.Inference
import CerbLean.CN.Types.ArgumentTypes

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc APexpr)
open CerbLean.CN.Types

/-! ## Call Situation

Corresponds to: call_situation in check.ml
Tracks what kind of call we're processing (function call, label call, etc.)
-/

/-- What kind of call is being processed.
    Corresponds to: call_situation in check.ml -/
inductive CallSituation where
  | functionCall (fsym : Sym)
  | labelCall (kind : LabelKind)
  | subtyping
  | lemmaApplication (lemma : Sym)
  deriving Inhabited

/-! ## Spine_L: Logical Part Processing

Corresponds to: spine_l in check.ml lines 1122-1142

Processes the logical part of an argument type (LAT):
- Define: bind a logical variable with a value
- Resource: consume a resource
- Constraint: add as obligation (or assumption depending on context)
- I: return the inner type

In CN, this uses RI.General.ftyp_args_request_step for resource inference.
For our pragmatic approach, we directly process each case.
-/

/-- Process the logical part of an argument type.
    Corresponds to: spine_l in check.ml lines 1122-1142

    let spine_l rt_subst rt_pp loc (situation : call_situation) ftyp k =
      let@ original_resources = all_resources loc in
      let@ rt =
        let rec check ftyp =
          let@ ftyp = RI.General.ftyp_args_request_step ... ftyp in
          match ftyp with I rt -> return rt | _ -> check ftyp
        in
        check ftyp
      in
      k rt

    For our implementation:
    - Define: add logical variable with value
    - Resource: consume the resource
    - Constraint: add as obligation
    - I: return the inner type -/
partial def spineL {α : Type} (loc : Loc) (situation : CallSituation)
    (lat : LAT α) (k : α → TypingM Unit) : TypingM Unit := do
  match lat with
  | .define_ name value info rest =>
    -- Corresponds to: RI handling of Define
    -- Bind the logical variable with its value
    TypingM.addLValue name value info.loc s!"define {name.name.getD ""}"
    spineL loc situation rest k

  | .resource name request outputBt info rest =>
    -- Corresponds to: RI handling of Resource (consumption)
    -- Consume the resource and bind the output
    -- For postconditions, this verifies the function produces the resource
    consumeResourceRequest request name outputBt info.loc
    spineL loc situation rest k

  | .constraint lc info rest =>
    -- Corresponds to: RI handling of Constraint
    -- For postconditions, this becomes a proof obligation
    TypingM.requireConstraint lc info.loc "postcondition constraint"
    spineL loc situation rest k

  | .I inner =>
    -- Base case: call the continuation with the inner type.
    -- For label types (α = False_), inner = False_.false_ and the continuation
    -- IS called — CN checks all_empty (leaked resources) there.
    -- Corresponds to: LAT.I case in spine_l, including LAT.I False.False
    k inner

where
  /-- Consume a resource matching a request and bind the output.
      Simplified version of CN's resource inference.

      Corresponds to: RI.General.ftyp_args_request_step handling of Resource case -/
  consumeResourceRequest (request : Request) (outputName : Sym)
      (outputBt : BaseType) (loc : Loc) : TypingM Unit := do
    -- Create a Resource structure with the request and expected output
    let resource : Resource := {
      request := request
      output := { value := AnnotTerm.mk (.sym outputName) outputBt loc }
    }
    -- Use the existing resource consumption mechanism
    -- This matches the request against available resources and binds the output
    consumeResourceClause outputName resource loc

/-! ## Spine: Full Argument Type Processing

Corresponds to: spine in check.ml lines 1145-1200

Processes a full argument type (AT):
1. Match computational arguments against provided args
2. Match ghost arguments against provided ghost args
3. Process the logical part via spine_l
-/

/-- Process a full argument type.
    Corresponds to: spine in check.ml lines 1145-1200

    The spine processes:
    - Computational args: check type, evaluate, substitute
    - Ghost args: check type, substitute (from separate gargs list)
    - L (logical part): delegate to spine_l

    The `innerSubst` parameter controls how substitution propagates to the
    inner type α. For label types (α = False_), it's identity. For function
    types (α = ReturnType), it's ReturnType.subst.

    Ghost args are provided as already-evaluated IndexTerms (not APexprs),
    matching CN where gargs are IT.t values passed separately from
    computational args.

    Corresponds to:
      let spine rt_subst rt_pp loc situation args gargs_opt ftyp k = ... -/
partial def spine {α : Type} (loc : Loc) (situation : CallSituation)
    (innerSubst : Subst → α → α)
    (args : List APexpr) (gargs : List IndexTerm) (at_ : AT α)
    (k : α → TypingM Unit) : TypingM Unit := do
  aux [] args gargs at_ k
where
  aux (argsAcc : List IndexTerm) (args : List APexpr) (gargs : List IndexTerm)
      (at_ : AT α) (k : α → TypingM Unit) : TypingM Unit := do
    match args, gargs, at_ with
    | arg :: restArgs, _, .computational s bt _info rest =>
      -- Computational argument: check and substitute
      -- Corresponds to: check.ml lines 1163-1173
      -- Pass expected type to checkPexprK for type-aware literal creation
      checkPexprK arg (fun argVal => do
        -- Substitute arg value for parameter in rest of type
        let σ := Subst.single s argVal
        let rest' := AT.subst innerSubst σ rest
        aux (argsAcc ++ [argVal]) restArgs gargs rest' k) (some bt)

    | _, garg :: restGargs, .ghost s bt _info rest =>
      -- Ghost argument: check type and substitute
      -- Corresponds to: check.ml lines 1174-1176
      -- CN: let@ garg = WellTyped.check_term (fst info) bt garg in
      --     aux args_acc args gargs (subst rt_subst (make_subst [(s, garg)]) ftyp) k
      -- WellTyped.check_term verifies the term's base type matches expected bt.
      -- Compare types via Repr string since BaseType lacks BEq/DecidableEq.
      if toString (repr garg.bt) != toString (repr bt) then
        TypingM.fail (.other s!"Ghost argument type mismatch at {repr loc}: expected {repr bt}, got {repr garg.bt}")
      -- Substitute ghost value for parameter in rest of type
      -- Ghost args do NOT accumulate into argsAcc (only computational args do)
      let σ := Subst.single s garg
      let rest' := AT.subst innerSubst σ rest
      aux argsAcc args restGargs rest' k

    | [], [], .L lat =>
      -- All args processed, now process logical part
      -- Corresponds to: check.ml lines 1177-1187

      -- Record action based on situation
      match situation with
      | .labelCall .return_ =>
        -- For return labels, the accumulated arg is the return value
        -- Corresponds to: check.ml lines 1182-1184
        -- record_action (Return { arg = returned; ... }, loc)
        pure ()  -- We don't have action recording yet
      | _ => pure ()

      -- Process the logical part
      spineL loc situation lat k

    | _ :: _, _, .L _ =>
      -- Too many computational args provided
      -- Corresponds to: check.ml lines 1188-1191
      TypingM.fail (.other s!"Too many arguments provided at {repr loc}")

    | _, _ :: _, .L _ =>
      -- Too many ghost args provided
      -- Corresponds to: check.ml lines 1192-1195
      TypingM.fail (.other s!"Too many ghost arguments provided at {repr loc}")

    | _, [], .ghost _ _ _ _ =>
      -- Not enough ghost args provided
      -- Corresponds to: check.ml lines 1192-1195
      TypingM.fail (.other s!"Not enough ghost arguments provided at {repr loc}")

    | [], _, .computational _ _ _ _ =>
      -- Not enough computational args provided
      -- Corresponds to: check.ml lines 1188-1191
      TypingM.fail (.other s!"Not enough arguments provided at {repr loc}")

/-! ## Calltype_lt: Label Type Calling

Corresponds to: calltype_lt in check.ml lines 1207-1208

  let calltype_lt loc args gargs_opt ((ltyp : AT.lt), label_kind) k =
    spine False.subst False.pp loc (LabelCall label_kind) args gargs_opt ltyp k

Calls spine with a label type and label kind.
-/

/-- Call a label type (for Erun handling).
    Corresponds to: calltype_lt in check.ml lines 1207-1208

    For return labels (LAreturn), this:
    1. Substitutes the return value into the label type
    2. Processes the postcondition (resources and constraints)
    3. The continuation receives False (uninhabited) - never called

    DIVERGES-FROM-CN: CN's calltype_lt passes gargs_opt through to spine.
    We pass [] for gargs since label calls with ghost args are not yet
    exercised. When ghost label args are needed, callers should pass gargs. -/
def calltypeLt (loc : Loc) (args : List APexpr) (entry : LabelEntry)
    (k : False_ → TypingM Unit) : TypingM Unit := do
  spine loc (.labelCall entry.kind) (fun _ x => x) args [] entry.lt k

/-! ## Subtype: Postcondition Checking

Corresponds to: Spine.subtype in check.ml lines 1218-1220

  let subtype (loc : Locations.t) (rtyp : LRT.t) k =
    let lft = LAT.of_lrt rtyp (LAT.I False.False) in
    spine_l False.subst False.pp loc Subtyping lft (fun False.False -> k ())

Used by check_expr_top to verify that a void function's fallthrough
satisfies the postcondition.
-/

/-- Check subtyping (postcondition satisfaction for fallthrough).
    Corresponds to: Spine.subtype in check.ml lines 1218-1220

    Converts the postcondition to LAT form and processes it via spine_l.
    Used when a void function falls through without explicit return. -/
def subtype (loc : Loc) (post : Postcondition) (k : Unit → TypingM Unit) : TypingM Unit := do
  let lat : LAT Unit := LAT.ofPostcondition post (.I ())
  spineL loc .subtyping lat k

/-! ## Calltype_ft: Function Type Calling

Corresponds to: calltype_ft in check.ml lines 1203-1204

  let calltype_ft loc ~fsym args gargs_opt (ftyp : AT.ft) k =
    spine RT.subst RT.pp loc (FunctionCall fsym) args gargs_opt ftyp k

Calls spine with a function type and function call situation.
The inner substitution is ReturnType.subst (substitutes in the LRT).
-/

/-- Call a function type (for Eccall handling).
    Corresponds to: calltype_ft in check.ml lines 1203-1204

    Processes the function's arguments via spine, consuming precondition
    resources and returning the ReturnType (which contains the postcondition).

    DIVERGES-FROM-CN: CN's calltype_ft passes gargs_opt through to spine.
    We pass [] for gargs since function calls with ghost args are not yet
    exercised. When ghost function args are needed, callers should pass gargs. -/
def calltypeFt (loc : Loc) (fsym : Sym) (args : List APexpr)
    (ft : AT ReturnType) (k : ReturnType → TypingM Unit) : TypingM Unit :=
  spine loc (.functionCall fsym) ReturnType.subst args [] ft k

/-! ## Bind Logical Return: Postcondition Processing

Corresponds to: bind_logical_return in check.ml

  let bind_logical_return loc prefix lrt =
    let rec aux = function
    | LRT.Define ((s, it), info, lrt) -> ...
    | LRT.Resource ((s, (re, bt)), info, lrt) -> ...
    | LRT.Constraint (lc, info, lrt) -> ...
    | LRT.I -> return ()

Processes the postcondition of a function call:
- Define: create fresh name, bind in logical context, add equality
- Resource: create fresh name, PRODUCE resource into context
- Constraint: add as ASSUMPTION (not obligation)
- I: done

This is the OPPOSITE direction from spine_l:
- spine_l CONSUMES resources (precondition: caller must provide)
- bindLogicalReturn PRODUCES resources (postcondition: callee guarantees)
-/

/-- Process the postcondition (LRT) of a function call.
    Corresponds to: bind_logical_return in check.ml

    Produces postcondition resources into the caller's context and
    adds postcondition constraints as assumptions.

    This is the opposite direction from spineL:
    - spineL consumes resources and generates obligations
    - bindLogicalReturn produces resources and assumes constraints -/
partial def bindLogicalReturn (loc : Loc) (lrt : LRT) : TypingM Unit := do
  match lrt with
  | .define name value _info rest =>
    -- Create fresh name for the defined variable
    let s' ← TypingM.freshSym (name.name.getD "define")
    -- Add to logical context
    TypingM.addL s' value.bt loc s!"postcondition define {name.name.getD ""}"
    -- Add equality constraint: s' == value
    let eqTerm := AnnotTerm.mk
      (.binop .eq (AnnotTerm.mk (.sym s') value.bt loc) value)
      .bool loc
    TypingM.addC (.t eqTerm)
    -- Continue with renamed LRT
    let σ := Subst.single name (AnnotTerm.mk (.sym s') value.bt loc)
    bindLogicalReturn loc (rest.subst σ)

  | .resource name request outputBt _info rest =>
    -- Create fresh name for the resource output
    let s' ← TypingM.freshSym (name.name.getD "resource")
    -- Add to logical context
    TypingM.addL s' outputBt loc s!"postcondition resource {name.name.getD ""}"
    -- Substitute fresh name into request
    let σ := Subst.single name (AnnotTerm.mk (.sym s') outputBt loc)
    let request' := request.subst σ
    -- PRODUCE the resource into context (opposite of spineL which consumes)
    let resource : Resource := {
      request := request'
      output := { value := AnnotTerm.mk (.sym s') outputBt loc }
    }
    produceResource resource
    -- Continue with renamed LRT
    bindLogicalReturn loc (rest.subst σ)

  | .constraint lc _info rest =>
    -- Add constraint as ASSUMPTION (opposite of spineL which generates obligations)
    -- The callee guarantees this constraint holds after the call
    TypingM.addC lc
    bindLogicalReturn loc rest

  | .I =>
    -- Postcondition fully processed
    pure ()

end CerbLean.CN.TypeChecking
