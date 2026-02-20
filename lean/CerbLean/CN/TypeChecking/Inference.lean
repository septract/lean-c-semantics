/-
  CN Resource Inference
  Corresponds to: cn/lib/resourceInference.ml

  Resource inference is the core of CN's type checking. When we need a resource
  (e.g., `take v = Owned<int>(p)`), we search the context for a matching resource.

  The algorithm uses two-phase matching:
  1. Syntactic fast path: check if pointers are syntactically equal
  2. SMT slow path: use solver to check pointer equality

  Additionally, struct resources are automatically unpacked into individual field
  resources when added to the context, matching CN's do_unfold_resources (typing.ml:548).
  When a struct resource is requested, it is repacked from field resources via
  Pack.packing_ft (pack.ml:52-92).

  Audited: 2026-02-19 against cn/lib/resourceInference.ml + cn/lib/pack.ml
-/

import CerbLean.CN.TypeChecking.Monad
import CerbLean.CN.TypeChecking.Resolve

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc Identifier Ctype FieldDef TagDef)
open CerbLean.CN.Types
open CerbLean.CN.TypeChecking.Resolve (ctypeToOutputBaseType)

/-- Compare base types for equality using their Repr representation.
    BaseType does not derive BEq (it's recursive), so we compare via repr.
    This is used only for QPredicate quantifier type matching.
    Corresponds to: BaseTypes.equal in CN (baseTypes.ml). -/
private def baseTypeReprEq (bt1 bt2 : BaseType) : Bool :=
  toString (repr bt1) == toString (repr bt2)

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

/-- Compare Ctypes by their inner type only, ignoring annotations.
    Corresponds to: Sctypes.equal in CN which works on annotation-free Sctypes.
    Our Ctype has an annots field that CN's Sctypes doesn't have. -/
def ctypeEqualIgnoringAnnots (ct1 ct2 : Core.Ctype) : Bool :=
  ct1.ty == ct2.ty

/-- Check if name1 can be satisfied by name2 (subsumption)
    `Owned<T>(Uninit)` can be satisfied by `Owned<T>(Init)` - initialized memory
    can be treated as uninitialized.

    Corresponds to: subsumed in request.ml lines 130-140
    Uses ctypeEqualIgnoringAnnots to match CN's Sctypes.equal. -/
def nameSubsumed (name1 name2 : ResourceName) : Bool :=
  match name1, name2 with
  | .owned (some ct1) .init, .owned (some ct2) .init => ctypeEqualIgnoringAnnots ct1 ct2
  | .owned (some ct1) .uninit, .owned (some ct2) _ => ctypeEqualIgnoringAnnots ct1 ct2
  | .pname pn1, .pname pn2 => pn1 == pn2  -- Uses BEq Sym (digest + id, matching CN)
  | _, _ => false

/-! ## Index Term Equality

For the fast path, we check syntactic equality of pointers.
For the slow path, we construct an equality constraint and check provability.
-/

/-- Extract the integer value from a constant term, if it is an integer constant.
    Handles both unbounded integers (.z) and fixed-width integers (.bits). -/
private def constIntValue : Term → Option Int
  | .const (.z v) => some v
  | .const (.bits _ _ v) => some v
  | _ => none

/-- Structural equality check for index terms (fast path).

    CN does not have a dedicated syntactic equality function. Instead,
    predicate_request_scan (resourceInference.ml:169-226) constructs
    equality terms `addr_(ptr1) == addr_(ptr2)` and passes them to
    `Simplify.LogicalConstraints.simp` (fast path) or the solver (slow path).
    The simplifier recognizes structurally identical terms as equal.

    This function approximates CN's fast-path simplifier behavior for the
    specific case of checking term equality. It handles the structural cases
    that arise from pointer expressions (memberShift, arrayShift, etc.).

    Also handles cross-type integer comparison: `z(N)` matches `bits(_, _, N)`
    when both represent the same mathematical integer. This is needed because
    Core IR produces unbounded integers while specs produce fixed-width integers. -/
partial def termSyntacticEq (t1 t2 : IndexTerm) : Bool :=
  match t1.term, t2.term with
  | .sym s1, .sym s2 => s1 == s2  -- Uses BEq Sym (digest + id, matching CN)
  | .memberShift ptr1 tag1 member1, .memberShift ptr2 tag2 member2 =>
    tag1 == tag2 && member1 == member2 && termSyntacticEq ptr1 ptr2
  | .arrayShift ptr1 ct1 idx1, .arrayShift ptr2 ct2 idx2 =>
    ct1.ty == ct2.ty && termSyntacticEq ptr1 ptr2 && termSyntacticEq idx1 idx2
  | .offsetOf tag1 member1, .offsetOf tag2 member2 =>
    tag1 == tag2 && member1 == member2
  | .const (.z v1), .const (.z v2) => v1 == v2
  | .const (.bits s1 w1 v1), .const (.bits s2 w2 v2) => s1 == s2 && w1 == w2 && v1 == v2
  | .const (.bool b1), .const (.bool b2) => b1 == b2
  | .const .null, .const .null => true
  | .const .unit, .const .unit => true
  | .cast bt1 inner1, .cast bt2 inner2 =>
    baseTypeReprEq bt1 bt2 && termSyntacticEq inner1 inner2
  | .binop op1 l1 r1, .binop op2 l2 r2 =>
    op1 == op2 && termSyntacticEq l1 l2 && termSyntacticEq r1 r2
  | .unop op1 arg1, .unop op2 arg2 =>
    op1 == op2 && termSyntacticEq arg1 arg2
  | _, _ =>
    -- Cross-type integer comparison: z(N) == bits(_, _, N) when N is the same
    -- This handles the common case where Core IR produces unbounded integers (z)
    -- but specs produce fixed-width integers (bits) for the same mathematical value.
    -- CN's simplifier normalizes these before comparison; we handle it here.
    match constIntValue t1.term, constIntValue t2.term with
    | some v1, some v2 => v1 == v2
    | _, _ => false

/-! ## Struct Resource Unpacking

Corresponds to: cn/lib/pack.ml lines 104-140 (unpack_owned) and
cn/lib/typing.ml lines 548-657 (do_unfold_resources).

When a resource `Owned<struct tag>(p)` with value `v` is added to the context,
CN automatically unpacks it into individual field resources:
- `Owned<field_type>(memberShift(p, tag, field))` with value `structMember(v, field)`

This ensures that loads from individual struct fields find matching resources.
The original struct resource is REPLACED by the field resources.
-/

/-- Unpack a struct resource into individual field resources.
    Given `Owned<struct tag>(Init)(p)` with value `v`, returns a list of field resources:
    `Owned<field_type>(Init)(memberShift(p, tag, field_name))` with value `structMember(v, field_name)`

    Corresponds to: unpack_owned in pack.ml lines 104-140 for the Struct case.

    Returns `none` if:
    - The resource is not Owned<struct>
    - The tag definition is not found

    Fails if:
    - The type is a union (CN does not support unions — check.ml:200, sctypes.ml:192)
-/
def unpackStructResource (r : Resource) : TypingM (Option (List Resource)) := do
  match r.request with
  | .p pred =>
    match pred.name with
    | .owned (some ct) initState =>
      match ct.ty with
      | .struct_ tag =>
        -- Look up the struct definition
        match ← TypingM.lookupTag tag with
        | some (.struct_ fields _) =>
          -- Unpack: create one field resource per struct member
          -- Corresponds to: pack.ml lines 113-124 (member_or_padding = Some case)
          -- DIVERGES-FROM-CN: CN's unpack_owned (pack.ml:113-124) also produces
          -- padding resources (Owned<char[N]>(Uninit) at padding offsets). We only
          -- produce member resources. Internally consistent since tryRepackStruct
          -- also skips padding during repacking.
          let fieldResources := fields.filterMap fun (field : FieldDef) =>
            let fieldPtr : IndexTerm := AnnotTerm.mk
              (.memberShift pred.pointer tag field.name) .loc pred.pointer.loc
            let fieldBt := ctypeToOutputBaseType field.ty
            let fieldValue : IndexTerm := AnnotTerm.mk
              (.structMember r.output.value field.name) fieldBt r.output.value.loc
            let fieldPred : Predicate := {
              name := .owned (some field.ty) initState
              pointer := fieldPtr
              iargs := []
            }
            some { request := .p fieldPred, output := { value := fieldValue } }
          return some fieldResources
        | some (.union_ _) =>
          -- CN does not support unions (check.ml:200: error "todo: union types")
          TypingM.fail (.other s!"union types are not supported (tag: {tag.name.getD "?"})")
        | none =>
          -- DIVERGES-FROM-CN: CN's get_struct_members would fail here.
          -- We return none (can't unpack), surfacing as "missing resource" upstream.
          return none
      | .union_ tag =>
        -- CN does not support unions (check.ml:200, sctypes.ml:192-198)
        TypingM.fail (.other s!"union types are not supported (tag: {tag.name.getD "?"})")
      | _ => return none  -- Not a struct/union type, no unpacking needed
    | .owned none _ => TypingM.fail (.other "unpackStructResource: unresolved resource type (should have been inferred during resolution)")
    | .pname _ => return none  -- Not Owned
  | .q _ => return none  -- Not a predicate resource

/-! ## Array Resource Unpacking

Corresponds to: cn/lib/pack.ml lines 24-39 (unfolded_array) and lines 104-108
(unpack_owned Array case).

When a resource `Owned<T[N]>(p)` with value `v` is added to the context,
CN automatically unpacks it into a QPredicate:
  `each(i; 0 <= i && i < N) { Owned<T>(arrayShift(p, T, i)) }`
with the output as a map from indices to values.
-/

/-- Unpack an array resource into a QPredicate.
    Converts `Owned<array(T, N)>(init)(p)` with value `v` into:
      `Q { name = Owned<T>(init), pointer = p, q = (i, uintptr_bt),
           step = T, permission = (0 <= i && i < N) }`
    with output value `v` (which is a map from indices to element values).

    Corresponds to: unpack_owned in pack.ml lines 104-108 (Array case) +
                    unfolded_array in pack.ml lines 24-39.

    Returns `none` if the resource is not `Owned<array(T, N)>`.
    Audited: 2026-02-19 -/
def unpackArrayResource (r : Resource) : TypingM (Option Resource) := do
  match r.request with
  | .p pred =>
    match pred.name with
    | .owned (some ct) initState =>
      match ct.ty with
      | .array elemTy (some length) =>
        -- CN ref: pack.ml:24-39 (unfolded_array)
        -- Create fresh quantifier variable: `i` with uintptr_bt type
        -- Corresponds to: IT.fresh_named Memory.uintptr_bt "i" loc in pack.ml:26
        let uintptrBt : BaseType := .bits .unsigned 64
        let qSym ← TypingM.freshSym "i"
        let loc := pred.pointer.loc
        let qVar : IndexTerm := AnnotTerm.mk (.sym qSym) uintptrBt loc
        -- Build permission: 0 <= i && i < N
        -- Corresponds to: pack.ml:36-38
        --   IT.(and_ [le_ (uintptr_int_ 0 loc, q) loc; lt_ (q, uintptr_int_ length loc) loc] loc)
        let zero : IndexTerm := AnnotTerm.mk (.const (.bits .unsigned 64 0)) uintptrBt loc
        let len : IndexTerm := AnnotTerm.mk (.const (.bits .unsigned 64 length)) uintptrBt loc
        let leBound : IndexTerm := AnnotTerm.mk (.binop .le zero qVar) .bool loc
        let ltBound : IndexTerm := AnnotTerm.mk (.binop .lt qVar len) .bool loc
        let permission : IndexTerm := AnnotTerm.mk (.binop .and_ leBound ltBound) .bool loc
        -- Build the element Ctype (strip annotations from inner type)
        let elemCtype : Ctype := Ctype.mk' elemTy
        -- Build QPredicate
        -- Corresponds to: pack.ml:27-39 (Q { name, pointer, q, q_loc, step, iargs, permission })
        let qpred : QPredicate := {
          name := .owned (some elemCtype) initState
          pointer := pred.pointer
          q := (qSym, uintptrBt)
          qLoc := loc
          step := elemCtype
          permission := permission
          iargs := []
        }
        -- Output value is the original output (a map from indices to element values)
        -- Corresponds to: pack.ml:108: (unfolded_array ..., O o) — output passed through
        return some { request := .q qpred, output := r.output }
      | .array _ none =>
        -- CN ref: pack.ml:25 — Option.get olength would fail for unsized arrays
        TypingM.fail (.other "unpackArrayResource: array type has no size (unsized arrays cannot be unpacked)")
      | _ => return none  -- Not an array type
    | .owned none _ => TypingM.fail (.other "unpackArrayResource: unresolved resource type (should have been inferred during resolution)")
    | .pname _ => return none  -- Not Owned
  | .q _ => return none  -- Already a QPredicate

/-- Add a resource to the context, unpacking struct and array resources.
    Corresponds to: add_r + do_unfold_resources in typing.ml lines 687-694.

    For struct resources, replaces `Owned<struct tag>(p)` with individual field
    resources `Owned<field_type>(memberShift(p, tag, field))`.
    For array resources, replaces `Owned<T[N]>(p)` with a QPredicate
    `each(i; 0<=i && i<N) { Owned<T>(arrayShift(p,T,i)) }`.
    Audited: 2026-02-19 -/
partial def addResourceWithUnfold (r : Resource) : TypingM Unit := do
  match ← unpackStructResource r with
  | some fieldResources =>
    -- Struct was unpacked: add individual field resources instead.
    -- Recursively unfold in case fields are themselves structs.
    -- Corresponds to: do_unfold_resources iterating until fixpoint (typing.ml:548-657)
    for fr in fieldResources do
      addResourceWithUnfold fr
  | none =>
    -- Not a struct: try array unpacking
    -- CN ref: pack.ml:108 — unpack_owned Array case produces a single QPredicate
    match ← unpackArrayResource r with
    | some qResource =>
      -- Array was unpacked into a QPredicate: add directly (no further unfold needed)
      TypingM.addR qResource
    | none =>
      -- Not a struct or array resource (or couldn't unpack): add as-is
      TypingM.addR r

/-! ## Predicate Request Scan

Corresponds to: cn/lib/resourceInference.ml lines 169-226 (predicate_request_scan)

This is the core matching algorithm. For each resource in context:
1. Check if names match (with subsumption)
2. Check if pointers match (syntactic equality)
3. Check if iargs match
4. If all match, consume the resource and return its output

Uses syntactic matching first, then SMT-based obligation matching as fallback.
-/

/-- Result of scanning for a resource -/
inductive ScanResult where
  /-- Found a matching resource with its output -/
  | found (pred : Predicate) (output : Output)
  /-- No matching resource found -/
  | notFound
  deriving Inhabited

/-- Scan context for a resource matching the requested predicate.
    Uses syntactic matching: names must subsume, pointers and iargs must be
    syntactically equal.

    Corresponds to: predicate_request_scan in resourceInference.ml lines 169-226 -/
def predicateRequestScan (requested : Predicate) : TypingM ScanResult := do
  let resources ← TypingM.getResources

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

  -- Phase 2: Obligation-based matching (SMT slow path)
  -- If syntactic matching fails, look for resources with matching name/type
  -- but different pointers. Add a pointer equality obligation for SMT to check.
  -- Corresponds to: the solver path in cn/lib/resourceInference.ml
  let mut candidates : List (Nat × Predicate × Output) := []
  for h : idx in [:resources.length] do
    let r := resources[idx]
    match r.request with
    | .p p' =>
      if nameSubsumed requested.name p'.name then
        let iargsMatch := requested.iargs.length == p'.iargs.length &&
          (List.zip requested.iargs p'.iargs).all fun (a, b) => termSyntacticEq a b
        if iargsMatch then
          candidates := (idx, p', r.output) :: candidates
    | .q _ => pure ()

  match candidates with
  | [(idx, p', output)] =>
    -- Single candidate: use it and add pointer equality obligation
    TypingM.removeResourceAt idx
    let eqTerm : IndexTerm := AnnotTerm.mk (.binop .eq requested.pointer p'.pointer) .bool requested.pointer.loc
    TypingM.requireConstraint (.t eqTerm) requested.pointer.loc "resource pointer equality"
    return .found p' output
  | _ =>
    -- No match or ambiguous (multiple candidates) - fail
    return .notFound

/-! ## Struct Resource Repacking

Corresponds to: cn/lib/pack.ml lines 42-92 (packing_ft) for the Struct case.

When a struct resource is requested but not found directly (because it was unpacked),
we repack by requesting each field individually and combining them into a struct value.
-/

mutual

/-- Try to repack individual field resources into a struct resource.
    Given a request for `Owned<struct tag>(init)(p)`, looks up the struct definition,
    requests each field resource individually, and combines into a struct value.

    Corresponds to: packing_ft + ftyp_args_request_for_pack in resourceInference.ml:239-246
    for the Owned(Struct tag, init) case (pack.ml:52-92).

    Returns `none` if:
    - The request is not for Owned<struct>
    - Any field resource is missing -/
partial def tryRepackStruct (requested : Predicate) : TypingM (Option (Predicate × Output)) := do
  match requested.name with
  | .owned (some ct) initState =>
    match ct.ty with
    | .union_ tag =>
      -- CN does not support unions (check.ml:200, sctypes.ml:192-198)
      TypingM.fail (.other s!"union types are not supported (tag: {tag.name.getD "?"})")
    | .struct_ tag =>
      -- Look up the struct definition
      match ← TypingM.lookupTag tag with
      | some (.struct_ fields _) =>
        -- Try to request each field resource
        -- Corresponds to: ftyp_args_request_for_pack processing the LAT from packing_ft
        -- DIVERGES-FROM-CN: CN's packing_ft (pack.ml:62-91) also requests padding
        -- resources during struct repacking. We only request member resources,
        -- consistent with unpackStructResource which also skips padding.
        let mut fieldValues : List (Identifier × IndexTerm) := []
        for field in fields do
          let fieldPtr : IndexTerm := AnnotTerm.mk
            (.memberShift requested.pointer tag field.name) .loc requested.pointer.loc
          let fieldPred : Predicate := {
            name := .owned (some field.ty) initState
            pointer := fieldPtr
            iargs := []
          }
          match ← predicateRequest fieldPred with
          | some (_, output) =>
            fieldValues := (field.name, output.value) :: fieldValues
          | none =>
            -- A field resource is missing: repacking fails.
            -- We must restore any already-consumed field resources.
            -- CN uses functional backtracking via ftyp_args_request_for_pack;
            -- we use imperative rollback (re-add consumed resources).
            -- Note: if a consumed field was itself repacked from sub-resources,
            -- the rollback re-adds it in packed form (not the original unpacked
            -- sub-resources). This is safe because rollback leads to failure.
            for (fld, val) in fieldValues do
              -- Find the corresponding field definition to get the type
              match fields.find? (·.name == fld) with
              | some fDef =>
                let fPtr : IndexTerm := AnnotTerm.mk
                  (.memberShift requested.pointer tag fld) .loc requested.pointer.loc
                let fResource : Resource := {
                  request := .p {
                    name := .owned (some fDef.ty) initState
                    pointer := fPtr
                    iargs := []
                  }
                  output := { value := val }
                }
                TypingM.addR fResource
              | none => TypingM.fail (.other s!"internal error: field {fld.name} not found in struct definition during rollback")
            return none
        -- All fields found! Construct the struct value.
        -- Corresponds to: LAT.I (IT.struct_ (tag, value) loc) in pack.ml:91
        let structBt := BaseType.struct_ tag
        let structValue : IndexTerm := AnnotTerm.mk
          (.struct_ tag fieldValues.reverse) structBt requested.pointer.loc
        return some (requested, { value := structValue })
      | some (.union_ _) =>
        -- CN does not support unions (check.ml:200)
        TypingM.fail (.other s!"union types are not supported (tag: {tag.name.getD "?"})")
      | none =>
        -- DIVERGES-FROM-CN: CN's get_struct_members would fail here.
        -- We return none (can't repack), surfacing as "missing resource" upstream.
        return none
    | _ => return none  -- Not a struct type, no repacking needed
  | .owned none _ => TypingM.fail (.other "tryRepackStruct: unresolved resource type (should have been inferred during resolution)")
  | .pname _ => return none  -- Only Owned can be repacked

/-- Try to repack a QPredicate into an array resource.
    Given a request for `Owned<T[N]>(init)(p)`, constructs a QPredicate request
    and tries to satisfy it from QPredicate resources in the context.

    Corresponds to: packing_ft in pack.ml lines 47-51 (Array case) +
                    ftyp_args_request_for_pack in resourceInference.ml:378-397.

    Returns `none` if:
    - The request is not for `Owned<array(T, N)>`
    - The QPredicate resource cannot be found
    Audited: 2026-02-19 -/
partial def tryRepackArray (requested : Predicate) : TypingM (Option (Predicate × Output)) := do
  match requested.name with
  | .owned (some ct) initState =>
    match ct.ty with
    | .array elemTy (some length) =>
      -- CN ref: pack.ml:47-51 — packing_ft for Array case
      -- Build the QPredicate request matching what unpackArrayResource produces
      let uintptrBt : BaseType := .bits .unsigned 64
      let qSym ← TypingM.freshSym "i"
      let loc := requested.pointer.loc
      let qVar : IndexTerm := AnnotTerm.mk (.sym qSym) uintptrBt loc
      -- Build permission: 0 <= i && i < N
      let zero : IndexTerm := AnnotTerm.mk (.const (.bits .unsigned 64 0)) uintptrBt loc
      let len : IndexTerm := AnnotTerm.mk (.const (.bits .unsigned 64 length)) uintptrBt loc
      let leBound : IndexTerm := AnnotTerm.mk (.binop .le zero qVar) .bool loc
      let ltBound : IndexTerm := AnnotTerm.mk (.binop .lt qVar len) .bool loc
      let permission : IndexTerm := AnnotTerm.mk (.binop .and_ leBound ltBound) .bool loc
      let elemCtype : Ctype := Ctype.mk' elemTy
      let qpredReq : QPredicate := {
        name := .owned (some elemCtype) initState
        pointer := requested.pointer
        q := (qSym, uintptrBt)
        qLoc := loc
        step := elemCtype
        permission := permission
        iargs := []
      }
      -- Try to request the QPredicate resource
      match ← qpredicateRequest qpredReq with
      | some (_, output) =>
        -- Construct the array output value from the QPredicate output (a map)
        -- CN ref: pack.ml:49-50 — o_s fresh named with bt_of_sct ct, then LAT.Resource + LAT.I o
        return some (requested, output)
      | none => return none
    | .array _ none =>
      TypingM.fail (.other "tryRepackArray: array type has no size (unsized arrays cannot be repacked)")
    | _ => return none  -- Not an array type
  | .owned none _ => TypingM.fail (.other "tryRepackArray: unresolved resource type")
  | .pname _ => return none  -- Only Owned can be repacked

/-- Request a QPredicate resource at a specific index or as a whole.
    For `each (i; guard) { Owned<T>(arrayShift(p, T, i)) }`:
    Searches context for matching QPredicate resources.

    Corresponds to: qpredicate_request in resourceInference.ml lines 253-375.

    Note: This is a simplified implementation. CN's full qpredicate_request involves:
    - Matching Q resources by name, step type, and quantifier base type
    - Alpha-renaming the found QPredicate to use the requested quantifier variable
    - Using SMT to check permission intersection (provable/refuted)
    - Combining multiple partial Q resources via the General.cases_to_map mechanism
    - Handling movable_indices for extracting individual elements

    Our simplified version handles the common case of a single matching QPredicate
    that exactly covers the requested permission.
    Audited: 2026-02-19 -/
partial def qpredicateRequest (requested : QPredicate) : TypingM (Option (QPredicate × Output)) := do
  let resources ← TypingM.getResources
  -- Phase 1: Look for a matching QPredicate in context
  -- CN ref: resourceInference.ml:260-313 (map_and_fold_resources scanning Q resources)
  for h : idx in [:resources.length] do
    let r := resources[idx]
    match r.request with
    | .q qp =>
      -- Check name subsumption and step type equality
      -- CN ref: resourceInference.ml:270-272
      if nameSubsumed requested.name qp.name
        && ctypeEqualIgnoringAnnots requested.step qp.step
        && baseTypeReprEq requested.q.2 qp.q.2 then
        -- Check pointer equality syntactically
        -- CN ref: resourceInference.ml:278 — pmatch = eq_(requested.pointer, p'.pointer)
        if termSyntacticEq requested.pointer qp.pointer then
          -- Found a matching QPredicate. Consume it.
          -- DIVERGES-FROM-CN: CN's full algorithm uses alpha-renaming, permission
          -- intersection analysis, and partial consumption. We consume the entire
          -- QPredicate and return its output directly. This is correct when the
          -- requested permission is exactly equal to or subsumed by the found one.
          TypingM.removeResourceAt idx
          return some (qp, r.output)
    | .p _ => pure ()  -- Not a QPredicate
  -- No matching QPredicate found
  return none

/-- Request a predicate resource from the context.
    First tries direct scan, then tries "packing" for compound resources.
    When direct scan fails for a struct type, attempts repacking from field resources.
    When struct repacking fails for an array type, attempts array repacking.
    Returns the matched predicate and its output value.

    Corresponds to: predicate_request in resourceInference.ml lines 229-250 -/
partial def predicateRequest (requested : Predicate) : TypingM (Option (Predicate × Output)) := do
  match ← predicateRequestScan requested with
  | .found pred output => return some (pred, output)
  | .notFound =>
    -- Direct scan failed. Try packing for compound resources.
    -- Corresponds to: Pack.packing_ft call in resourceInference.ml:239
    match ← tryRepackStruct requested with
    | some result => return some result
    | none =>
      -- Struct repacking failed. Try array repacking.
      -- CN ref: pack.ml:47-51 — packing_ft Array case
      tryRepackArray requested

end -- mutual

/-! ## Resource Request

Corresponds to: cn/lib/resourceInference.ml lines 400-432 (resource_request)
-/

/-- Request a resource from the context.
    For simple predicates, delegates to predicateRequest.
    For quantified predicates, delegates to qpredicateRequest.

    Corresponds to: resource_request in resourceInference.ml lines 400-432
    Audited: 2026-02-19 -/
def resourceRequest (request : Request) : TypingM (Option (Request × Output)) := do
  match request with
  | .p pred =>
    match ← predicateRequest pred with
    | some (p', output) => return some (.p p', output)
    | none => return none
  | .q qpred =>
    -- CN ref: resourceInference.ml:430-432
    match ← qpredicateRequest qpred with
    | some (q', output) => return some (.q q', output)
    | none => return none

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
    let eqTerm : IndexTerm := AnnotTerm.mk (.binop .eq nameAsTerm output.value) .bool loc
    TypingM.addC (.t eqTerm)
  | none =>
    let ctx ← TypingM.getContext
    TypingM.fail (.missingResource resource.request ctx)

/-- Add a resource to the context with struct unpacking.
    Corresponds to: add_r + do_unfold_resources in typing.ml.

    For postconditions and resource production, this automatically unpacks
    struct resources into individual field resources. -/
def produceResource (resource : Resource) : TypingM Unit := do
  addResourceWithUnfold resource

end CerbLean.CN.TypeChecking
