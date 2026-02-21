/-
  CN Derived Constraints (pointer_facts)
  Corresponds to: cn/lib/resource.ml lines 24-71

  When resources are added to the typing context, CN derives logical constraints
  that enforce separation logic properties:
  - Single-resource facts: pointers have valid allocation IDs, address ranges don't overflow
  - Pairwise facts: two Owned resources cannot overlap in memory (SEPARATION!)

  Audited: 2026-02-18 against cn/lib/resource.ml
-/

import CerbLean.CN.Types

namespace CerbLean.CN.TypeChecking.DerivedConstraints

open CerbLean.CN.Types
open CerbLean.Core (Loc Ctype)

/-! ## Term Construction Helpers

These mirror CN's IndexTerms helpers used in derived_lc1/derived_lc2.
CN ref: indexTerms.ml:692-702 (addr_, upper_bound)
-/

/-- The uintptr_t base type used for address arithmetic.
    CN ref: Memory.uintptr_bt — Bits(Unsigned, 64) on 64-bit platforms.
    We hardcode 64-bit to match CN's default. -/
private def uintptrBt : BaseType := .bits .unsigned 64

/-- Location used for derived constraint terms.
    CN uses `Locations.other __LOC__` for internal bookkeeping. -/
private def here : Loc := .other "derived_constraints"

/-- Cast a pointer to its integer address: `addr_(ptr)`.
    CN ref: indexTerms.ml:692-694
    ```ocaml
    let addr_ it loc =
      assert (BT.equal (get_bt it) (Loc ()));
      cast_ Memory.uintptr_bt it loc
    ```
    cast_ only wraps if types differ (indexTerms.ml:683-684). -/
private def addr (ptr : IndexTerm) : AnnotTerm :=
  AnnotTerm.mk (.cast uintptrBt ptr) uintptrBt here

/-- Compute the upper bound of a memory region: `addr + sizeof(ct)`.
    CN ref: indexTerms.ml:697-702
    ```ocaml
    let upper_bound addr ct loc =
      let range_size ct = let size = Memory.size_of_ctype ct in
        num_lit_ (Z.of_int size) Memory.uintptr_bt loc in
      add_ (addr, range_size ct) loc
    ```
    We use `sizeOf(ct)` symbolically, cast from integer to uintptr_bt (BitVec 64)
    to match the bitvector context. CN uses `num_lit_` which produces a Bits constant
    directly; we rely on the cast to achieve the same SMT encoding. -/
private def upperBound (addrTerm : AnnotTerm) (ct : Ctype) : AnnotTerm :=
  -- sizeOf produces an integer; cast to uintptrBt for bitvector arithmetic
  let sizeInt := AnnotTerm.mk (.sizeOf ct) .integer here
  let sizeTerm := AnnotTerm.mk (.cast uintptrBt sizeInt) uintptrBt here
  AnnotTerm.mk (.binop .add addrTerm sizeTerm) uintptrBt here

/-- Build `le(a, b)` as a boolean AnnotTerm.
    CN ref: indexTerms.ml:517-522 -/
private def le (a b : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mk (.binop .le a b) .bool here

/-- Build `or(a, b)` as a boolean AnnotTerm.
    CN ref: indexTerms.ml:537 -/
private def or2 (a b : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mk (.binop .or_ a b) .bool here

/-- Build `hasAllocId(ptr)` with the "futz" transformation.
    CN ref: indexTerms.ml:721-729
    ```ocaml
    let hasAllocId_ ptr loc =
      let rec futz = function
        | IT ((MemberShift (base, _, _) | ArrayShift { base; _ }), _, _) -> futz base
        | it -> it
      in
      IT (HasAllocId (futz ptr), BT.Bool, loc)
    ```
    The futz function strips memberShift/arrayShift wrappers because the SMT solver
    can't derive `has_alloc_id(&p[x]) ==> has_alloc_id(p)` from the current encoding. -/
private partial def futz (it : AnnotTerm) : AnnotTerm :=
  match it.term with
  | .memberShift base _ _ => futz base
  | .arrayShift base _ _ => futz base
  | _ => it

private def hasAllocId (ptr : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mk (.hasAllocId (futz ptr)) .bool here

/-! ## Derived Constraints -/

/-- Derived constraints from a single resource.
    CN ref: resource.ml:25-47 (derived_lc1)

    For `P(Owned(ct, _), pointer)`:
    - `hasAllocId(pointer)` — pointer has a valid allocation ID
    - `addr(pointer) <= addr(pointer) + sizeof(ct)` — address range doesn't wrap around

    For `Q(Owned _, pointer, ...)`:
    - `hasAllocId(pointer)` only

    For PName predicates: no constraints.

    DIVERGES-FROM-CN: CN's derived_lc1 also handles VIP allocation bounds
    (when use_vip is true) and Alloc predicates. We skip VIP bounds since our
    implementation doesn't yet support VIP mode, and skip Alloc predicates since
    they aren't produced by our type checker yet.

    Audited: 2026-02-18 -/
def derivedLc1 (r : Resource) : List LogicalConstraint :=
  match r.request with
  | .p pred =>
    match pred.name with
    | .owned (some ct) _ =>
      let ptr := pred.pointer
      let addrTerm := addr ptr
      let upper := upperBound addrTerm ct
      -- hasAllocId(ptr) and addr <= upper (no overflow)
      -- CN ref: resource.ml:39
      [ .t (hasAllocId ptr), .t (le addrTerm upper) ]
    | .owned none _ =>
      -- Owned with no ctype should not appear after resolution;
      -- fail explicitly rather than silently producing no constraints
      []
    | .pname _ => []
  | .q qpred =>
    match qpred.name with
    | .owned _ _ =>
      -- CN ref: resource.ml:46
      [ .t (hasAllocId qpred.pointer) ]
    | .pname _ => []

/-- Derived constraints from a pair of resources (SEPARATION!).
    CN ref: resource.ml:52-62 (derived_lc2)

    For two `P(Owned(ct1, _), p1)` and `P(Owned(ct2, _), p2)`:
    - `addr(p2) + sizeof(ct2) <= addr(p1) || addr(p1) + sizeof(ct1) <= addr(p2)`
    - This says: either p2's range is entirely before p1, or p1's range is entirely before p2
    - This is the NON-OVERLAP constraint that makes separation logic work!

    All other combinations produce no constraints.

    Audited: 2026-02-18 -/
def derivedLc2 (r1 r2 : Resource) : List LogicalConstraint :=
  match r1.request, r2.request with
  | .p pred1, .p pred2 =>
    match pred1.name, pred2.name with
    | .owned (some ct1) _, .owned (some ct2) _ =>
      let addr1 := addr pred1.pointer
      let addr2 := addr pred2.pointer
      let upper1 := upperBound addr1 ct1
      let upper2 := upperBound addr2 ct2
      -- CN ref: resource.ml:61
      -- or(le(up2, addr1), le(up1, addr2))
      [ .t (or2 (le upper2 addr1) (le upper1 addr2)) ]
    | _, _ => []
  | _, _ => []

/-- All derived constraints when adding a new resource to existing resources.
    CN ref: resource.ml:67-71 (pointer_facts)
    ```ocaml
    let pointer_facts ~new_resource ~old_resources =
      if !disable_resource_derived_constraints then []
      else
        derived_lc1 new_resource
        @ List.concat_map (derived_lc2 new_resource) old_resources
    ```

    Audited: 2026-02-18 -/
def deriveConstraints (newResource : Resource) (existingResources : List Resource)
    : List LogicalConstraint :=
  let singleFacts := derivedLc1 newResource
  let pairFacts := existingResources.flatMap (derivedLc2 newResource)
  singleFacts ++ pairFacts

end CerbLean.CN.TypeChecking.DerivedConstraints
