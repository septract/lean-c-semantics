/-
  CN Resource Inference
  Corresponds to: cn/lib/resourceInference.ml

  Resource inference is the core of CN's type checking. When we need a resource
  (e.g., `take v = Owned<int>(p)`), we search the context for a matching resource.

  The algorithm uses two-phase matching:
  1. Syntactic fast path: check if pointers are syntactically equal
  2. SMT slow path: use solver to check pointer equality

  Audited: 2026-01-20 against cn/lib/resourceInference.ml
-/

import CerbLean.CN.TypeChecking.Monad

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types

/-! ## Name Subsumption

Corresponds to: cn/lib/request.ml lines 130-140 (subsumed function)
```ocaml
let subsumed name1 name2 =
  match (name1, name2) with
  | Owned (ct1, Init), Owned (ct2, Init) -> Sctypes.equal ct1 ct2
  | Owned (ct1, Uninit), Owned (ct2, _) -> Sctypes.equal ct1 ct2
  | PName pn1, PName pn2 -> Sym.equal pn1 pn2
  | _ -> false
```

Key insight: Uninit can be satisfied by either Init or Uninit (W<T> ≤ RW<T>)
because initialized memory can always be treated as uninitialized.
-/

/-- Check if name1 can be satisfied by name2 (subsumption)
    `Owned<T>(Uninit)` can be satisfied by `Owned<T>(Init)` - initialized memory
    can be treated as uninitialized.

    Corresponds to: subsumed in request.ml lines 130-140 -/
def nameSubsumed (name1 name2 : ResourceName) : Bool :=
  match name1, name2 with
  | .owned ct1 .init, .owned ct2 .init => ct1 == ct2  -- exact match for init
  | .owned ct1 .uninit, .owned ct2 _ => ct1 == ct2    -- uninit matches both
  | .pname pn1, .pname pn2 => pn1.id == pn2.id
  | _, _ => false

/-! ## Index Term Equality

For the fast path, we check syntactic equality of pointers.
For the slow path, we construct an equality constraint and check provability.
-/

/-- Syntactic equality check for index terms (fast path) -/
def termSyntacticEq (t1 t2 : IndexTerm) : Bool :=
  -- Simple structural equality for now - just check symbols
  -- In full CN, this uses Simplify.IndexTerms.simp first
  match t1.term, t2.term with
  | .sym s1, .sym s2 => s1.id == s2.id
  | _, _ => false

/-- Build an equality constraint for two index terms -/
def mkEqConstraint (t1 t2 : IndexTerm) : LogicalConstraint :=
  -- Construct: t1 == t2 as a logical constraint
  let eqTerm : IndexTerm := AnnotTerm.mk (.binop .eq t1 t2) .bool t1.loc
  .t eqTerm

/-! ## Predicate Request Scan

Corresponds to: cn/lib/resourceInference.ml lines 169-226 (predicate_request_scan)

This is the core matching algorithm. For each resource in context:
1. Check if names match (with subsumption)
2. Check if pointers match (syntactic first, then SMT)
3. Check if iargs match
4. If all match, consume the resource and return its output
-/

/-- Result of scanning for a resource -/
inductive ScanResult where
  /-- Found a matching resource with its output -/
  | found (pred : Predicate) (output : Output)
  /-- No matching resource found -/
  | notFound
  deriving Inhabited

/-- Scan context for a resource matching the requested predicate.
    Uses two-phase matching: syntactic fast path, then SMT slow path.

    Corresponds to: predicate_request_scan in resourceInference.ml lines 169-226 -/
def predicateRequestScan (requested : Predicate) : TypingM ScanResult := do
  let resources ← TypingM.getResources

  -- Phase 1: Fast path - syntactic matching
  for h : idx in [:resources.length] do
    let r := resources[idx]
    match r.request with
    | .p p' =>
      if nameSubsumed requested.name p'.name then
        -- Check pointer equality syntactically
        if termSyntacticEq requested.pointer p'.pointer then
          -- Check iargs match syntactically
          let iargsMatch := requested.iargs.length == p'.iargs.length &&
            (List.zip requested.iargs p'.iargs).all fun (a, b) => termSyntacticEq a b
          if iargsMatch then
            -- Found a syntactic match! Consume the resource.
            TypingM.removeResourceAt idx
            return .found p' r.output
    | .q _ => pure ()  -- Quantified predicates handled separately

  -- Phase 2: Slow path - SMT matching
  for h : idx in [:resources.length] do
    let r := resources[idx]
    match r.request with
    | .p p' =>
      if nameSubsumed requested.name p'.name then
        -- Build equality constraint for pointer
        let ptrEq := mkEqConstraint requested.pointer p'.pointer

        -- Build equality constraints for iargs
        let iargEqs := List.zipWith mkEqConstraint requested.iargs p'.iargs

        -- TODO: Also check alloc_id equality (CN does this)
        -- For now we just check address equality

        -- Check if all equalities are provable
        let mut allProvable := true
        match ← TypingM.provable ptrEq with
        | .true_ => pure ()
        | .false_ _ => allProvable := false

        for eq in iargEqs do
          if allProvable then
            match ← TypingM.provable eq with
            | .true_ => pure ()
            | .false_ _ => allProvable := false

        if allProvable then
          -- Found a match via SMT! Consume the resource.
          TypingM.removeResourceAt idx
          return .found p' r.output
    | .q _ => pure ()

  -- No match found
  return .notFound

/-! ## Predicate Request

Corresponds to: cn/lib/resourceInference.ml lines 229-250 (predicate_request)

First tries direct scan, then tries "packing" for compound resources.
For our minimal subset, we only implement the direct scan.
-/

/-- Request a predicate resource from the context.
    Returns the matched predicate and its output value.

    Corresponds to: predicate_request in resourceInference.ml lines 229-250 -/
def predicateRequest (requested : Predicate) : TypingM (Option (Predicate × Output)) := do
  match ← predicateRequestScan requested with
  | .found pred output => return some (pred, output)
  | .notFound =>
    -- In full CN, this would try "packing" compound resources
    -- For our minimal subset, we just fail
    return none

/-! ## Resource Request

Corresponds to: cn/lib/resourceInference.ml lines 400-432 (resource_request)
-/

/-- Request a resource from the context.
    For simple predicates, delegates to predicateRequest.
    For quantified predicates, would use qpredicate_request (not yet implemented).

    Corresponds to: resource_request in resourceInference.ml lines 400-432 -/
def resourceRequest (request : Request) : TypingM (Option (Request × Output)) := do
  match request with
  | .p pred =>
    match ← predicateRequest pred with
    | some (p', output) => return some (.p p', output)
    | none => return none
  | .q _qpred =>
    -- Quantified predicates not yet supported
    -- Would call qpredicate_request
    return none

/-! ## Consuming Resources from Specs

When processing a function spec, we need to consume resources from preconditions
and produce resources for postconditions.
-/

/-- Process a resource clause from a spec: request the resource and bind output.
    Used for precondition `take v = Owned<T>(p)` clauses.

    Corresponds to part of bind_arguments in check.ml -/
def consumeResourceClause (name : Sym) (resource : Resource) (loc : Loc) : TypingM Unit := do
  -- The resource contains both the request and expected output binding
  match ← resourceRequest resource.request with
  | some (_, output) =>
    -- Bind the output value to the given name
    -- The output.value contains the actual value from the consumed resource
    let bt := output.value.bt
    TypingM.addL name bt loc s!"resource output {name.name.getD ""}"
    -- Add equality constraint: name == output.value
    let nameAsTerm : IndexTerm := AnnotTerm.mk (.sym name) bt loc
    TypingM.addC (mkEqConstraint nameAsTerm output.value)
  | none =>
    let ctx ← TypingM.getContext
    TypingM.fail (.missingResource resource.request ctx)

/-- Add a resource to the context (for postconditions).
    Used for postcondition `take v = Owned<T>(p)` clauses where we produce ownership. -/
def produceResource (resource : Resource) : TypingM Unit := do
  TypingM.addR resource

end CerbLean.CN.TypeChecking
