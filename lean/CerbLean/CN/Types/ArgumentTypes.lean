/-
  CN Argument Types
  Corresponds to: cn/lib/argumentTypes.ml and cn/lib/logicalArgumentTypes.ml

  This module defines the exact type structures CN uses for function/label types:
  - LogicalArgumentTypes (LAT): The logical part (Define, Resource, Constraint, I)
  - ArgumentTypes (AT): Full argument type (Computational, Ghost, L)

  Type aliases:
  - FT = AT RT    (function type, returns RT)
  - LT = AT False (label type, returns False - uninhabited/terminal)

  Audited: 2026-01-28 against cn/lib/argumentTypes.ml, logicalArgumentTypes.ml
-/

import CerbLean.CN.Types.Resource
import CerbLean.CN.Types.Constraint
import CerbLean.CN.Types.Spec
import CerbLean.Core.MuCore

namespace CerbLean.CN.Types

open CerbLean.Core (Sym Loc)

/-! ## Info Type

Corresponds to: info in cn/lib/*.ml
Location and lazy description for error messages.
-/

/-- Info attached to argument type nodes.
    Corresponds to: info = Locations.t * Pp.document Lazy.t -/
structure Info where
  loc : Loc
  desc : String := ""
  deriving Inhabited

/-! ## False Type (Uninhabited)

Corresponds to: cn/lib/false.ml

type t = False

This is an uninhabited type used for label types to indicate they never
return normally. In CN, when you have `AT.lt = False.t AT.t`, the inner
`LAT.I False.False` case can never be reached at runtime because return
labels are terminal.
-/

/-- False type for label types.
    Corresponds to: type t = False in cn/lib/false.ml

    CN's False.t has a single constructor `False`. It is used to mark label
    types as terminal, but the continuation IS reachable (it's where CN's
    all_empty leak check runs). We model it as a unit-like inductive. -/
inductive False_ where
  | false_
  deriving Inhabited

/-! ## Logical Argument Types (LAT)

Corresponds to: cn/lib/logicalArgumentTypes.ml

The logical part of an argument type. Processes:
- Define: bind a logical variable with a computed value
- Resource: consume/produce a resource
- Constraint: add/verify a constraint
- I: the inner return type
-/

/-- Logical argument type, parameterized by inner return type.
    Corresponds to: 'i t in logicalArgumentTypes.ml

    type 'i t =
      | Define of (Sym.t * IT.t) * info * 'i t
      | Resource of (Sym.t * (Req.t * BT.t)) * info * 'i t
      | Constraint of LC.t * info * 'i t
      | I of 'i

    Corresponds to: 'i t in logicalArgumentTypes.ml -/
inductive LAT (α : Type) where
  /-- Define a logical variable with a value.
      `Define (name, value) info rest` means: let name = value in rest -/
  | define_ (name : Sym) (value : IndexTerm) (info : Info) (rest : LAT α)
  /-- Resource clause: consume/produce a resource.
      The name binds the resource output value. -/
  | resource (name : Sym) (request : Request) (outputBt : BaseType) (info : Info) (rest : LAT α)
  /-- Constraint clause: a logical constraint to verify/assume. -/
  | constraint (lc : LogicalConstraint) (info : Info) (rest : LAT α)
  /-- Inner return type (base case).
      For label types, `I False_.false_` is the terminal case matching CN's
      `LAT.I False.False`. The continuation IS called (CN checks all_empty there). -/
  | I (inner : α)

namespace LAT

/-- Substitute in a LAT.
    Corresponds to: LAT.subst in logicalArgumentTypes.ml -/
partial def subst {α : Type} (innerSubst : Subst → α → α) (σ : Subst) : LAT α → LAT α
  | .define_ name value info rest =>
    -- Alpha-rename bound variable if it conflicts with substitution
    -- Corresponds to: logicalArgumentTypes.ml lines 53-55 (suitably_alpha_rename)
    let (name', rest') := if σ.relevant.contains name.id then
      let name' := freshSymFor name σ.relevant
      let renameσ := Subst.single name (AnnotTerm.mk (.sym name') value.bt value.loc)
      (name', subst innerSubst renameσ rest)
    else (name, rest)
    .define_ name' (value.subst σ) info (subst innerSubst σ rest')
  | .resource name req bt info rest =>
    -- Alpha-rename bound variable if it conflicts with substitution
    -- Corresponds to: logicalArgumentTypes.ml lines 57-59
    let (name', rest') := if σ.relevant.contains name.id then
      let name' := freshSymFor name σ.relevant
      let renameσ := Subst.single name (AnnotTerm.mk (.sym name') bt default)
      (name', subst innerSubst renameσ rest)
    else (name, rest)
    .resource name' (req.subst σ) bt info (subst innerSubst σ rest')
  | .constraint lc info rest =>
    .constraint (lc.subst σ) info (subst innerSubst σ rest)
  | .I inner => .I (innerSubst σ inner)

/-- Convert a Postcondition (list of clauses) to LAT.
    Corresponds to: LAT.of_lrt in logicalArgumentTypes.ml line 181

    This converts our simplified Postcondition representation to the
    exact LAT structure CN uses.

    rec of_lrt (lrt : LRT.t) (rest : 'i t) : 'i t =
      match lrt with
      | LRT.I () -> rest
      | LRT.Define ((name, it), info, args) -> Define ((name, it), info, of_lrt args rest)
      | LRT.Resource ((name, t), info, args) -> Resource ((name, t), info, of_lrt args rest)
      | LRT.Constraint (t, info, args) -> Constraint (t, info, of_lrt args rest) -/
def ofPostcondition {α : Type} (post : Postcondition) (rest : LAT α) : LAT α :=
  -- Our Postcondition is a list of clauses, so we fold right
  post.clauses.foldr (init := rest) fun clause acc =>
    match clause with
    | .resource name res =>
      -- Resource clause: the name binds the resource output
      -- Resource has: request : Request, output : Output
      -- We create a new Request from the Resource's request
      .resource name
                res.request
                res.output.value.bt
                { loc := res.output.value.loc }
                acc
    | .constraint assertion =>
      .constraint (.t assertion) { loc := assertion.loc } acc
    | .letBinding name value =>
      -- Let binding becomes Define in LAT
      .define_ name value { loc := value.loc } acc

end LAT

/-! ## Argument Types (AT)

Corresponds to: cn/lib/argumentTypes.ml

Full argument type including computational and ghost arguments.
-/

/-- Argument type, parameterized by inner return type.
    Corresponds to: 'i t in argumentTypes.ml

    type 'i t =
      | Computational of (Sym.t * BT.t) * info * 'i t
      | Ghost of (Sym.t * BT.t) * info * 'i t
      | L of 'i LAT.t -/
inductive AT (α : Type) where
  /-- Computational argument (runtime value). -/
  | computational (name : Sym) (bt : BaseType) (info : Info) (rest : AT α)
  /-- Ghost argument (logical only, not in runtime). -/
  | ghost (name : Sym) (bt : BaseType) (info : Info) (rest : AT α)
  /-- Logical part (LAT). -/
  | L (lat : LAT α)

namespace AT

/-- Substitute in an AT.
    Corresponds to: AT.subst in argumentTypes.ml -/
partial def subst {α : Type} (innerSubst : Subst → α → α) (σ : Subst) : AT α → AT α
  | .computational name bt info rest =>
    -- Alpha-rename bound variable if it conflicts with substitution
    -- Corresponds to: argumentTypes.ml lines 30-32 (suitably_alpha_rename)
    let (name', rest') := if σ.relevant.contains name.id then
      let name' := freshSymFor name σ.relevant
      let renameσ := Subst.single name (AnnotTerm.mk (.sym name') bt default)
      (name', subst innerSubst renameσ rest)
    else (name, rest)
    .computational name' bt info (subst innerSubst σ rest')
  | .ghost name bt info rest =>
    -- Alpha-rename bound variable if it conflicts with substitution
    -- Corresponds to: argumentTypes.ml lines 34-36
    let (name', rest') := if σ.relevant.contains name.id then
      let name' := freshSymFor name σ.relevant
      let renameσ := Subst.single name (AnnotTerm.mk (.sym name') bt default)
      (name', subst innerSubst renameσ rest)
    else (name, rest)
    .ghost name' bt info (subst innerSubst σ rest')
  | .L lat => .L (LAT.subst innerSubst σ lat)

/-- Create an argument type from a function spec (return type).
    Corresponds to: AT.of_rt in argumentTypes.ml line 121

    let of_rt (rt : RT.t) (rest : 'i LAT.t) : 'i t =
      let (RT.Computational ((name, t), info, lrt)) = rt in
      Computational ((name, t), info, L (LAT.of_lrt lrt rest))

    For label types, `rest` is `LAT.I False` (uninhabited - terminal).
    The return symbol becomes a computational argument; when you call
    the label with the return value, it's substituted throughout.

    Parameters:
    - spec: The function specification containing return symbol and postcondition
    - returnBt: The base type of the return value
    - rest: What comes after the postcondition (LAT.I False for labels) -/
def ofFunctionSpec {α : Type} (spec : FunctionSpec) (returnBt : BaseType) (rest : LAT α) : AT α :=
  .computational spec.returnSym returnBt
                  { loc := .unknown, desc := "return value" }
                  (.L (LAT.ofPostcondition spec.ensures rest))

end AT

/-! ## Logical Return Types (LRT)

Corresponds to: cn/lib/logicalReturnTypes.ml

The logical return type represents the postcondition of a function call.
It has the same structure as LAT but different semantics:
- LAT resources are CONSUMED (precondition: caller must provide)
- LRT resources are PRODUCED (postcondition: callee guarantees)
- LAT constraints become OBLIGATIONS (to verify)
- LRT constraints become ASSUMPTIONS (guaranteed by callee)

  type t =
    | Define of (Sym.t * IT.t) * BaseTypes.info * t
    | Resource of (Sym.t * (RE.t * BT.t)) * BaseTypes.info * t
    | Constraint of LC.t * BaseTypes.info * t
    | I
-/

/-- Logical Return Type (postcondition structure for function types).
    Corresponds to: LRT.t in cn/lib/logicalReturnTypes.ml -/
inductive LRT where
  /-- Define a logical variable with a value. -/
  | define (name : Sym) (value : IndexTerm) (info : Info) (rest : LRT)
  /-- Resource clause: a resource to produce (callee guarantees it). -/
  | resource (name : Sym) (request : Request) (outputBt : BaseType) (info : Info) (rest : LRT)
  /-- Constraint: a postcondition constraint (assumed by caller). -/
  | constraint (lc : LogicalConstraint) (info : Info) (rest : LRT)
  /-- Terminal: postcondition fully processed. -/
  | I

namespace LRT

/-- Substitute in an LRT.
    Corresponds to: LRT.subst in logicalReturnTypes.ml -/
partial def subst (σ : Subst) : LRT → LRT
  | .define name value info rest =>
    -- Alpha-rename bound variable if it conflicts with substitution
    -- Corresponds to: logicalReturnTypes.ml suitably_alpha_rename
    let (name', rest') := if σ.relevant.contains name.id then
      let name' := freshSymFor name σ.relevant
      let renameσ := Subst.single name (AnnotTerm.mk (.sym name') value.bt value.loc)
      (name', LRT.subst renameσ rest)
    else (name, rest)
    .define name' (value.subst σ) info (LRT.subst σ rest')
  | .resource name req bt info rest =>
    -- Alpha-rename bound variable if it conflicts with substitution
    let (name', rest') := if σ.relevant.contains name.id then
      let name' := freshSymFor name σ.relevant
      let renameσ := Subst.single name (AnnotTerm.mk (.sym name') bt default)
      (name', LRT.subst renameσ rest)
    else (name, rest)
    .resource name' (req.subst σ) bt info (LRT.subst σ rest')
  | .constraint lc info rest =>
    .constraint (lc.subst σ) info (subst σ rest)
  | .I => .I

/-- Convert a Postcondition (list of clauses) to LRT.
    Corresponds to: building LRT.t from postcondition clauses -/
def ofPostcondition (post : Postcondition) : LRT :=
  post.clauses.foldr (init := .I) fun clause acc =>
    match clause with
    | .resource name res =>
      .resource name res.request res.output.value.bt { loc := res.output.value.loc } acc
    | .constraint assertion =>
      .constraint (.t assertion) { loc := assertion.loc } acc
    | .letBinding name value =>
      .define name value { loc := value.loc } acc

end LRT

/-! ## Return Types

Corresponds to: cn/lib/returnTypes.ml

  type t = Computational of (Sym.t * BT.t) * BaseTypes.info * LRT.t

The return type of a function, containing:
- The return symbol and its base type
- The postcondition as an LRT
-/

/-- Return type for function types.
    Corresponds to: ReturnTypes.t in cn/lib/returnTypes.ml

    type t = Computational of (Sym.t * BT.t) * BaseTypes.info * LRT.t -/
structure ReturnType where
  /-- Symbol for the return value -/
  sym : Sym
  /-- Base type of the return value -/
  bt : BaseType
  /-- Postcondition (logical return type) -/
  lrt : LRT

namespace ReturnType

/-- Substitute in a ReturnType.
    Corresponds to: ReturnTypes.subst in returnTypes.ml

    Alpha-renames the return symbol if it conflicts with the substitution,
    then substitutes in the LRT (postcondition).
    CN ref: returnTypes.ml:16-19 (subst with suitably_alpha_rename) -/
def subst (σ : Subst) (rt : ReturnType) : ReturnType :=
  let (sym', lrt') := if σ.relevant.contains rt.sym.id then
    let sym' := freshSymFor rt.sym σ.relevant
    let renameσ := Subst.single rt.sym (AnnotTerm.mk (.sym sym') rt.bt default)
    (sym', rt.lrt.subst renameσ)
  else (rt.sym, rt.lrt)
  { rt with sym := sym', lrt := LRT.subst σ lrt' }

end ReturnType

/-! ## Function Types

  type ft = ReturnTypes.t t   (argumentTypes.ml line 135)

A function type is an AT parameterized by ReturnType.
-/

/-- Function type: argument type that returns a ReturnType.
    Corresponds to: type ft = ReturnTypes.t t in argumentTypes.ml line 135 -/
abbrev FT := AT ReturnType

/-! ## Type Aliases

These match CN's exact type aliases.
-/

/-- Label type: argument type that returns False (terminal).
    Corresponds to: type lt = False.t t in argumentTypes.ml line 137

    For return labels, this encodes:
    - One computational argument (the return value)
    - The postcondition resources and constraints
    - Ends in False (never continues normally) -/
abbrev LT := AT False_

/-- The terminal LAT value for label types.
    Corresponds to: LAT.I False.False in CN

    CN's False.t has a single constructor `False`. The continuation IS reachable
    (CN checks all_empty there). We use `I False_.false_` to match. -/
def LAT.terminalValue : LAT False_ := .I .false_

/-- Create a label type for a return label.
    Corresponds to: AT.of_rt function_rt (LAT.I False.False) in wellTyped.ml

    The return symbol becomes a computational argument to the label.
    When you call the return label with the actual return value,
    the spine substitutes that value for the return symbol in the postcondition. -/
def LT.ofFunctionSpec (spec : FunctionSpec) (returnBt : BaseType) : LT :=
  AT.ofFunctionSpec spec returnBt LAT.terminalValue

/-! ## Label Kind

Corresponds to: CF.Annot.label_annot in cerberus
-/

/-- Label kind annotation.
    Corresponds to: CF.Annot.label_annot in cerberus -/
inductive LabelKind where
  | return_  -- LAreturn: return label
  | loop     -- LAloop: loop label
  | other    -- Other label kinds
  deriving Inhabited, BEq

/-! ## Label Context

Corresponds to: label_context in cn/lib/wellTyped.ml line 1359
type label_context = (AT.lt * Where.label * Locations.t) Sym.Map.t

The label context maps each label symbol to:
- Its argument type (LT = AT False)
- Its kind (return, loop, etc.)
- Its source location
-/

/-- Entry in the label context: label type, kind, and location.
    Corresponds to: (AT.lt * Where.label * Locations.t) -/
structure LabelEntry where
  /-- The label's argument type (ends in False - terminal) -/
  lt : LT
  /-- What kind of label (return, loop, etc.) -/
  kind : LabelKind
  /-- Source location -/
  loc : Loc

/-- Label context: maps label symbol ID to its entry.
    Corresponds to: label_context = (AT.lt * Where.label * Locations.t) Sym.Map.t -/
abbrev LabelContext := List (Nat × LabelEntry)

namespace LabelContext

/-- Look up a label by symbol.
    Corresponds to: Sym.Map.find_opt in CN -/
def get? (ctx : LabelContext) (sym : Sym) : Option LabelEntry :=
  ctx.lookup sym.id

/-- Get the loop ID from a label's annotations if it has an LAloop annotation.
    Corresponds to: get_label_annot + match LAloop in CN -/
private def getLoopIdFromAnnots (annots : Core.Annots) : Option Nat :=
  annots.findSome? fun
    | .label (.loop id) => some id
    | _ => none

/-- Get the label kind from a label's annotations.
    Corresponds to: get_label_annot in annot.lem -/
private def getLabelKindFromAnnots (annots : Core.Annots) : LabelKind :=
  match annots.findSome? (fun | .label a => some a | _ => none) with
  | some (Core.LabelAnnot.return_) => .return_
  | some (Core.LabelAnnot.loop _) => .loop
  | _ => .other

/-- Create label context from function spec and label definitions.
    Corresponds to: WProc.label_context in wellTyped.ml line 2474

    Pmap.fold
      (fun sym def label_context ->
         let lt, kind, loc =
           match def with
           | Non_inlined (loc, _name, label_annot, args) ->
             (WLabel.typ args, label_annot, loc)
           | Return loc ->
             (AT.of_rt function_rt (LAT.I False.False), CF.Annot.LAreturn, loc)
           | Loop (loc, label_args_and_body, annots, _parsed_spec, _loop_info) ->
             ...
         in
         Sym.Map.add sym (lt, kind, loc) label_context)
      label_defs
      Sym.Map.empty

    Parameters:
    - spec: Function specification (contains return symbol and postcondition)
    - returnBt: Base type of the return value
    - labelDefs: Label definitions from muCore transformation
    - loopLabelTypes: Pre-built label types for loop labels, keyed by label sym ID.
      Built by the caller (Params.lean) using loop_attributes and saveArgCTypes. -/
def ofLabelDefs (spec : FunctionSpec) (returnBt : BaseType)
    (labelDefs : Core.MuCore.LabelDefs)
    (loopLabelTypes : List (Nat × LT) := []) : LabelContext :=
  labelDefs.filterMap fun (symId, labelDef) =>
    match labelDef with
    | .return_ loc =>
      -- Return label: type is derived from function return type
      -- AT.of_rt function_rt (LAT.I False.False)
      let lt := LT.ofFunctionSpec spec returnBt
      some (symId, { lt := lt, kind := .return_, loc := loc })
    | .label info =>
      -- Determine label kind from annotations
      let kind := getLabelKindFromAnnots info.annots
      match kind with
      | .loop =>
        -- Loop label: use pre-built label type if available
        -- Corresponds to: Loop case in WProc.label_context (wellTyped.ml:2483-2486)
        match loopLabelTypes.lookup symId with
        | some lt => some (symId, { lt := lt, kind := .loop, loc := info.loc })
        | none =>
          -- Fallback: create label type with correct number of computational args
          -- but no resource/constraint clauses.
          -- DIVERGES-FROM-CN: CN's make_label_args also produces Owned resources
          -- and invariant constraints. We build a minimal type with just args.
          let lt := info.params.foldr (init := (.L LAT.terminalValue : LT)) fun (sym, _bt) acc =>
            .computational sym .loc { loc := info.loc, desc := s!"loop var {sym.name.getD ""}" } acc
          some (symId, { lt := lt, kind := .loop, loc := info.loc })
      | _ =>
        -- Non-loop non-return label: create a simple label type with args
        -- Corresponds to: Non_inlined case in WProc.label_context
        let lt := info.params.foldr (init := (.L LAT.terminalValue : LT)) fun (sym, _bt) acc =>
          .computational sym .loc { loc := info.loc, desc := s!"label var {sym.name.getD ""}" } acc
        some (symId, { lt := lt, kind := .other, loc := info.loc })

end LabelContext

end CerbLean.CN.Types
