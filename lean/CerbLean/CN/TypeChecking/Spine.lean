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
    - Ghost args: check type, substitute
    - L (logical part): delegate to spine_l

    For label calls with LAreturn, records a Return action. -/
partial def spine {α : Type} (loc : Loc) (situation : CallSituation)
    (args : List APexpr) (at_ : AT α) (k : α → TypingM Unit) : TypingM Unit := do
  aux [] args at_ k
where
  aux (argsAcc : List IndexTerm) (args : List APexpr) (at_ : AT α)
      (k : α → TypingM Unit) : TypingM Unit := do
    match args, at_ with
    | arg :: restArgs, .computational s bt _info rest =>
      -- Computational argument: check and substitute
      -- Corresponds to: check.ml lines 1163-1173
      -- Pass expected type to checkPexprK for type-aware literal creation
      checkPexprK arg (fun argVal => do
        -- Substitute arg value for parameter in rest of type
        let σ := Subst.single s argVal
        let rest' := AT.subst (fun _ x => x) σ rest  -- No inner subst needed for False
        aux (argsAcc ++ [argVal]) restArgs rest' k) (some bt)

    | _, .ghost _s _bt _info rest =>
      -- Ghost argument: we don't have ghost args in our simplified model
      -- For now, skip ghost processing
      -- TODO: Add ghost argument handling if needed
      aux argsAcc args rest k

    | [], .L lat =>
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

    | _ :: _, .L _ =>
      -- Too many args provided
      TypingM.fail (.other s!"Too many arguments provided at {repr loc}")

    | [], .computational _ _ _ _ =>
      -- Not enough args provided
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

    Parameters:
    - loc: Source location for error messages
    - args: Arguments to the label (for return labels, the return value)
    - entry: Label context entry (contains label type and kind)
    - k: Continuation (receives False - never actually called for terminal labels) -/
def calltypeLt (loc : Loc) (args : List APexpr) (entry : LabelEntry)
    (k : False_ → TypingM Unit) : TypingM Unit := do
  spine loc (.labelCall entry.kind) args entry.lt k

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

end CerbLean.CN.TypeChecking
