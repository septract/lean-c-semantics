/-
  CN Resource Interpretation
  Corresponds to: cn/coq/Cn/Context.v, cn/coq/Reasoning/ResourceInference.v

  This module defines:
  - Level 1 (Syntactic): Context for resource tracking, inference validity
  - Level 2 (Semantic): Interpretation of resources as heap predicates

  Audited: 2026-01-18 against cn/coq/Cn/Context.v, cn/coq/Reasoning/ResourceInference.v
-/

import CerbLean.CN.Types
import CerbLean.CN.Semantics.Heap

namespace CerbLean.CN.Semantics

open CerbLean.Core (Sym Loc Ctype)
open CerbLean.CN.Types

/-! ## Level 1: Syntactic Resource Tracking

This level matches CN's approach: resources are tracked symbolically
as a set in the context. The "frame" is implicit - remaining resources
after consumption.

Corresponds to: cn/coq/Cn/Context.v, cn/lib/context.ml
-/

/-- A binding in the context: either a base type or a concrete value
    Corresponds to: basetype_or_value in cn/coq/Cn/Context.v -/
inductive BaseTypeOrValue where
  | baseType (bt : BaseType)
  | value (it : IndexTerm)
  deriving Inhabited

/-- Location info for a binding -/
structure LInfo where
  loc : Loc
  description : String
  deriving Repr, Inhabited

/-- CN typing context
    Corresponds to: Context.t in cn/coq/Cn/Context.v

    Note: CN tracks resources as `(list (Resource.t * Z)) * Z` where Z is
    a counter for generating fresh resource IDs. We simplify to just a list. -/
structure Context where
  /-- Computational variable bindings (C variables) -/
  computational : List (Sym × BaseTypeOrValue × LInfo)
  /-- Logical variable bindings (CN logical variables) -/
  logical : List (Sym × BaseTypeOrValue × LInfo)
  /-- Current resources (the key for separation logic) -/
  resources : List Resource
  /-- Logical constraints that must hold (represented as index terms) -/
  constraints : List IndexTerm
  deriving Inhabited

namespace Context

/-- Empty context -/
def empty : Context :=
  { computational := []
  , logical := []
  , resources := []
  , constraints := [] }

/-- Get the list of resources from a context
    Corresponds to: get_rs in cn/coq/Cn/Context.v -/
def getResources (ctx : Context) : List Resource := ctx.resources

/-- Add a resource to the context -/
def addResource (ctx : Context) (r : Resource) : Context :=
  { ctx with resources := r :: ctx.resources }

end Context

/-! ## Resource Inference Correctness

Defines when resource inference steps are correct.
This is the key to CN's approach - rather than stating a frame rule,
CN proves that resource inference preserves the correct resources.

Corresponds to: cn/coq/Reasoning/ResourceInference.v
-/

/-- Predicate subsumption: p1 can be satisfied by p2
    Owned<T>(Uninit) can be satisfied by Owned<T>(Init)
    Corresponds to: subsumed in cn/coq/Reasoning/ResourceInference.v -/
def nameSubsumed (n1 n2 : ResourceName) : Prop :=
  n1 = n2 ∨
  match n1, n2 with
  | ResourceName.owned ct1 Init.uninit, ResourceName.owned ct2 Init.init => ct1 = ct2
  | _, _ => False

/-- A resource inference step is valid when:
    - The output resources plus the consumed resource equals input resources
    - The predicate name matches (with subsumption)
    - Pointer equality is provable

    Corresponds to: simple_resource_inference_step in cn/coq/Reasoning/ResourceInference.v

    This is where the "frame rule" is implicit: resources not consumed
    remain in out_resources unchanged. -/
structure SimpleResourceInferenceStep where
  -- Input context
  inputCtx : Context
  -- Output context (after consuming resource)
  outputCtx : Context
  -- The requested predicate
  requested : Predicate
  -- The used predicate (found in context)
  used : Predicate
  -- The output value bound to the resource
  output : IndexTerm
  -- Names match (with subsumption)
  nameMatch : nameSubsumed requested.name used.name
  -- Output resources + used = input resources (the frame property)
  resourceBalance : ∀ r, r ∈ inputCtx.resources ↔
    (r ∈ outputCtx.resources ∨ r.request = Request.p used)
  -- Other context components unchanged
  computationalUnchanged : inputCtx.computational = outputCtx.computational
  logicalUnchanged : inputCtx.logical = outputCtx.logical
  constraintsUnchanged : inputCtx.constraints = outputCtx.constraints

/-- A complete resource inference for a function spec:
    - Start with precondition resources
    - Each clause consumption is valid
    - End with postcondition resources -/
structure SpecInferenceValid where
  -- The function specification
  spec : FunctionSpec
  -- Initial context (before function call)
  preCtx : Context
  -- Final context (after function returns)
  postCtx : Context
  -- For trusted specs, inference is trivially valid
  trustedOrValid : spec.trusted = true ∨
    -- All precondition resources are in preCtx
    ((∀ clause, clause ∈ spec.requires.clauses →
      match clause with
      | Clause.resource _ res => res ∈ preCtx.resources
      | Clause.constraint _ => True
      | Clause.letBinding _ _ => True) ∧
    -- All postcondition resources are in postCtx
    (∀ clause, clause ∈ spec.ensures.clauses →
      match clause with
      | Clause.resource _ res => res ∈ postCtx.resources
      | Clause.constraint _ => True
      | Clause.letBinding _ _ => True))

/-! ## Level 2: Semantic Interpretation

This level provides meaning to resources by interpreting them
as predicates on concrete memory (heap fragments).

This is where separation logic's disjointness appears.
-/

/-- Check if a heap value matches a C type -/
def valueMatchesType (ct : Ctype) (v : HeapValue) : Prop :=
  let ty := match ct.ty with
    | .atomic inner => inner
    | other => other
  match ty, v with
  | .basic (.integer _), .integer _ _ => True
  | .pointer _ _, .pointer _ => True
  | .struct_ tag, .struct_ tag' _ => tag == tag'
  | .array _ _, .array _ _ => True
  | _, _ => False

/-- Interpretation of a single Owned resource
    `interpOwned ct loc initState v h` means:
    - h is a singleton heap containing value v at location loc
    - v has type ct
    - If initState = Init, v is a proper initialized value

    This is where the heap fragment appears! -/
def interpOwned (ct : Ctype) (loc : Location) (initState : Init) (v : HeapValue)
    (h : HeapFragment) : Prop :=
  h = HeapFragment.singleton loc v ∧
  match initState with
  | .init => valueMatchesType ct v
  | .uninit => True

/-- Interpretation of a predicate resource
    Maps a predicate to a heap predicate -/
def interpPredicate (pred : Predicate) (outputVal : HeapValue) (ρ : Valuation)
    (h : HeapFragment) : Prop :=
  match pred.name with
  | .owned ct initState =>
    match pred.pointer.term with
    | .sym s =>
      match ρ.lookup s with
      | some (.pointer (some loc)) => interpOwned ct loc initState outputVal h
      | _ => False
    | _ => False
  | .pname _ => False  -- User predicates not yet supported

/-- Interpretation of a resource
    `interpResource res ρ h` means heap h satisfies resource res
    under valuation ρ -/
def interpResource (res : Resource) (ρ : Valuation) (h : HeapFragment) : Prop :=
  match res.request with
  | .p pred =>
    match res.output.value.term with
    | .sym s =>
      match ρ.lookup s with
      | some v => interpPredicate pred v ρ h
      | none => False
    | _ => False
  | .q _ => False  -- Quantified predicates not yet supported

/-- Interpretation of a resource set as separating conjunction
    `interpResources rs ρ h` means:
    - h can be split into disjoint sub-heaps h1, h2, ..., hn
    - Each sub-heap hi satisfies the corresponding resource ri

    This is where separation logic appears at the semantic level! -/
def interpResources (rs : List Resource) (ρ : Valuation) (h : HeapFragment) : Prop :=
  match rs with
  | [] => h = HeapFragment.empty
  | r :: rs' =>
    ∃ h1 h2,
      h1.disjoint h2 ∧
      h = h1 ++ h2 ∧
      interpResource r ρ h1 ∧
      interpResources rs' ρ h2

/-! ## Helper Functions -/

/-- Helper to create a symbol -/
def mkSym (name : String) (id : Nat) : Sym :=
  { digest := "", id := id, description := .none_, name := some name }

/-- Enumerate a list with indices -/
def enumList {α : Type} (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (i, x) :: go (i + 1) xs
  go 0 xs

end CerbLean.CN.Semantics
