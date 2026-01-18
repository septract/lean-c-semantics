/-
  CN Separation Logic Semantics
  Corresponds to: cn/coq/Cn/Context.v, cn/coq/Reasoning/ResourceInference.v

  This module defines semantics for CN specifications following CN's two-level approach:

  **Level 1: Syntactic (Resource Tracking)**
  - Context: tracks resources as a set, plus logical/computational bindings
  - Resource inference: how resources are consumed/produced during checking
  - Matches: cn/lib/context.ml, cn/coq/Cn/Context.v

  **Level 2: Semantic (Interpretation)**
  - HeapFragment: concrete memory as partial map from locations to values
  - Interpretation: maps resource sets to heap predicates
  - This is where separation (disjointness) is defined

  **Soundness** connects the two levels:
  - If resource inference succeeds (Level 1)
  - And initial memory satisfies interpretation of precondition resources
  - Then final memory satisfies interpretation of postcondition resources

  Audited: 2026-01-18 against cn/coq/Cn/Context.v, cn/coq/Reasoning/ResourceInference.v
-/

import CerbLean.CN.Request
import CerbLean.CN.Spec
import CerbLean.Memory.Types
import CerbLean.Memory.Layout

namespace CerbLean.CN.Semantics

open CerbLean.Core
open CerbLean.Memory

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
      | Clause.constraint _ => True) ∧
    -- All postcondition resources are in postCtx
    (∀ clause, clause ∈ spec.ensures.clauses →
      match clause with
      | Clause.resource _ res => res ∈ postCtx.resources
      | Clause.constraint _ => True))

/-! ## Level 2: Semantic Interpretation

This level provides meaning to resources by interpreting them
as predicates on concrete memory (heap fragments).

This is where separation logic's disjointness appears.
-/

/-- A location in concrete memory (allocation ID + address)
    Corresponds to: CNMem.location = (provenance * address) in cn/coq/Cn/CNMem.v -/
structure Location where
  allocId : Nat
  addr : Nat
  deriving Repr, BEq, Inhabited, DecidableEq, Hashable

/-- A concrete value in memory
    Corresponds to: mem_value in cn/coq/Cn/CNMem.v -/
inductive HeapValue where
  | integer (ity : IntegerType) (val : Int)
  | pointer (addr : Option Location)  -- None = NULL
  | struct_ (tag : Sym) (fields : List (Identifier × HeapValue))
  | array (elemTy : Ctype) (elems : List HeapValue)
  | uninitialized (ty : Ctype)
  deriving Repr, Inhabited

/-- A heap fragment - partial map from locations to values
    This is the standard separation logic heap.
    Corresponds to: implicit heap in separation logic -/
structure HeapFragment where
  cells : List (Location × HeapValue)
  deriving Repr, Inhabited

namespace HeapFragment

def empty : HeapFragment := ⟨[]⟩

def singleton (loc : Location) (val : HeapValue) : HeapFragment :=
  ⟨[(loc, val)]⟩

def dom (h : HeapFragment) : List Location :=
  h.cells.map (·.1)

def lookup (h : HeapFragment) (loc : Location) : Option HeapValue :=
  h.cells.find? (·.1 == loc) |>.map (·.2)

/-- Disjointness: no shared locations -/
def disjoint (h1 h2 : HeapFragment) : Prop :=
  ∀ loc, loc ∈ h1.dom → loc ∉ h2.dom

/-- Separating conjunction: combine disjoint heaps -/
def union (h1 h2 : HeapFragment) : HeapFragment :=
  ⟨h1.cells ++ h2.cells⟩

instance : Append HeapFragment := ⟨union⟩

/-- A sub-heap relation -/
def subheap (h1 h2 : HeapFragment) : Prop :=
  ∀ loc v, h1.lookup loc = some v → h2.lookup loc = some v

end HeapFragment

/-- Valuation: maps logical symbols to concrete values -/
abbrev Valuation := List (Sym × HeapValue)

namespace Valuation

def lookup (v : Valuation) (s : Sym) : Option HeapValue :=
  v.find? (fun (s', _) => s'.id == s.id) |>.map (·.2)

def empty : Valuation := []

end Valuation

/-! ## Resource Interpretation

Map CN resources to heap predicates. This is the semantic
interpretation function.

Key property: interpretation of a resource set decomposes into
disjoint heaps for each resource (separating conjunction).
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

/-! ## Soundness

The main soundness theorem connects the two levels:
1. If resource inference is valid (syntactic level)
2. And the initial heap satisfies the interpretation of precondition resources
3. Then the final heap satisfies the interpretation of postcondition resources

This is CN's approach to soundness.
-/

/-- Helper to create a symbol -/
def mkSym (name : String) (id : Nat) : Sym :=
  { digest := "", id := id, description := .none_, name := some name }

/-- Enumerate a list with indices -/
def enumList {α : Type} (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (i, x) :: go (i + 1) xs
  go 0 xs

/- TODO: Soundness theorem requires proper execution relation
   The statement below is incomplete - it needs:
   1. A proper execution relation connecting pre/post states
   2. Connection between ρPre and ρPost via execution
   3. Connection between hPre and hPost via execution

theorem cn_soundness
    (spec : FunctionSpec)
    (preCtx postCtx : Context)
    (hPre hPost : HeapFragment)
    (ρPre ρPost : Valuation)
    (hInferValid : SpecInferenceValid)
    (hInferSpec : hInferValid.spec = spec)
    (hInferPre : hInferValid.preCtx = preCtx)
    (hInferPost : hInferValid.postCtx = postCtx)
    (hPreSat : interpResources preCtx.resources ρPre hPre)
    (_hExec : True)  -- PLACEHOLDER: needs real execution relation
    : interpResources postCtx.resources ρPost hPost := by
  sorry
-/

/-- Frame property (derived)

    The frame property follows from how resource inference works:
    resources not mentioned in the spec are preserved in the context,
    so their interpretation is preserved in the heap.

    This is a consequence of SimpleResourceInferenceStep.resourceBalance -/
theorem frame_derived
    (rs_used rs_frame : List Resource)
    (ρ : Valuation)
    (h_used h_frame : HeapFragment)
    -- Frame is disjoint from used resources
    (hDisj : h_used.disjoint h_frame)
    -- Used resources satisfy their interpretation
    (hUsedSat : interpResources rs_used ρ h_used)
    -- Frame resources satisfy their interpretation
    (hFrameSat : interpResources rs_frame ρ h_frame)
    : interpResources (rs_used ++ rs_frame) ρ (h_used ++ h_frame) := by
  sorry

end CerbLean.CN.Semantics
