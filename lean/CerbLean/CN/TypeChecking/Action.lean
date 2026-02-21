/-
  CN Memory Action Checking
  Corresponds to: cn/lib/check.ml (Eaction cases) lines 1778-1908

  Handles memory actions with resource tracking:
  - create → produce Owned<T>(Uninit)
  - kill → consume Owned<T>(Uninit)
  - store → consume Uninit, produce Init
  - load → consume/produce Init, return value

  Audited: 2026-01-20 against cn/lib/check.ml
-/

import CerbLean.CN.TypeChecking.Monad
import CerbLean.CN.TypeChecking.Inference
import CerbLean.CN.TypeChecking.Pexpr
import CerbLean.Core.Expr

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Paction AAction Action APexpr Ctype KillKind SymPrefix Value)
open CerbLean.CN.Types

/-! ## Type Extraction

Extract C types from type expressions.
In Core IR, types are represented as expressions that evaluate to Ctype values.
Corresponds to: act.ct access in check.ml
-/

/-- Extract Ctype from a type expression.
    The type expression should be a Pexpr.val (Value.ctype ct).
    Fails if the expression doesn't evaluate to a Ctype.

    Corresponds to: accessing act.ct in check.ml Eaction cases -/
def extractCtype (tyPe : APexpr) (loc : Core.Loc) : TypingM Ctype := do
  match tyPe.expr with
  | .val (.ctype ct) => return ct
  | .val _ =>
    TypingM.fail (.other s!"Expected Ctype value, got non-Ctype value")
  | _ =>
    -- For complex expressions, we would need to evaluate them
    -- For now, fail explicitly rather than using a default
    TypingM.fail (.other s!"Cannot extract Ctype from non-literal expression at {repr loc}")

/-! ## Fresh Symbol Generation

Generate fresh symbols for newly allocated memory.
Uses a counter in the typing state to ensure uniqueness.
Corresponds to: Sym.fresh_* functions in CN OCaml
-/

/-- Create a fresh symbol with the given prefix.
    Uses a counter to ensure unique IDs.

    Corresponds to: IT.fresh_named in check.ml line 1791 -/
def freshSym (prefix_ : SymPrefix) (_loc : Core.Loc) : TypingM Sym := do
  let state ← TypingM.getState
  let id := state.freshCounter
  TypingM.modifyState fun s => { s with freshCounter := s.freshCounter + 1 }
  return { id := id, name := some prefix_.val }

/-! ## Creating Resources

Helper functions to create Owned predicates.
-/

/-- Create an Owned resource predicate
    Corresponds to the creation of Owned<ct>(init)(ptr) with output value
    CN OCaml: (P { name = Owned (ct, init); pointer = ptr; iargs = [] }, O value) -/
def mkOwnedResource (ct : Ctype) (initState : Init) (ptr : IndexTerm) (value : IndexTerm)
    : Resource :=
  let pred : Predicate := {
    name := .owned (some ct) initState
    pointer := ptr
    iargs := []
  }
  { request := .p pred
  , output := { value := value } }

/-- Create a unit value as an IndexTerm -/
def mkUnitTerm (loc : Core.Loc) : IndexTerm :=
  AnnotTerm.mk (.const .unit) .unit loc

/-- Create a default (uninitialized) value for a type -/
def mkDefaultValue (bt : BaseType) (loc : Core.Loc) : IndexTerm :=
  AnnotTerm.mk (.const (.default bt)) bt loc

/-- Simplify a pointer expression for resource matching.
    Core IR wraps pointer dereferences in validity checks:
      if PtrValidForDeref then ptr else undef(...)
    CN's muCore transformation strips these wrappers since validity is
    ensured by the resource system (having Owned<T>(ptr) implies ptr is valid).
    Our lazy muCore approach simulates this by simplifying the ITE pattern.

    Corresponds to: core_to_mucore pointer dereference simplification -/
def simplifyPointerForResource (ptr : IndexTerm) : IndexTerm :=
  match ptr.term with
  | .ite _cond thenBranch elseBranch =>
    -- If else branch is an undef marker, strip the ITE wrapper
    -- Undef symbols are created in checkPexpr with id=0, name="undef"
    match elseBranch.term with
    | .sym s =>
      if isUndefSym s then thenBranch
      else ptr
    | _ => ptr
  | _ => ptr

/-- Convert Ctype to CN BaseType.
    Delegates to ctypeInnerToBaseType which correctly maps integer types to Bits
    (matching CN's Memory.bt_of_sct which returns Bits(sign, width) for integers).

    Corresponds to: Memory.bt_of_sct in CN OCaml (cn/lib/memory.ml) -/
def ctypeToBaseType (ct : Ctype) (_loc : Core.Loc) : TypingM BaseType := do
  return ctypeInnerToBaseType ct.ty

/-! ## Unspecified Value Detection

When storing `LVunspecified` values (uninitialized memory), we should NOT convert
Uninit→Init because reading such memory is undefined behavior. This helper
detects whether a pure expression evaluates to an unspecified value.

### Design Note: Deviation from CN's Mechanism

CN's documentation states: "CN does not permit reads of possibly uninitialised memory"
(cn/manual/logic.md lines 111-114).

However, CN's actual implementation has `assert false` for `LVunspecified` in multiple
places (wellTyped.ml:1499, wellTyped.ml:1536, mucore.ml:39, check.ml:251), which means
CN would crash during the WellTyped pass if it encountered `Store(ptr, LVunspecified)`.

We achieve the same SEMANTIC result through a different mechanism:
1. Detect `Store(ptr, LVunspecified)` via `isUnspecifiedValue`
2. Keep the resource as `Owned<T>(Uninit)` instead of converting to `Owned<T>(Init)`
3. Subsequent `Load` requires `Owned<T>(Init)`, so reading uninitialized memory fails

This achieves CN's stated goal ("no reads of uninitialised memory") without crashing.
The correctness of this approach will be validated when we prove type checking correct
with respect to the runtime semantics.

Audited: 2026-01-21 - investigated CN's handling of LVunspecified
-/

/-- Check if a pure expression evaluates to an unspecified value (LVunspecified).
    Used by handleStore to avoid converting Uninit→Init for uninitialized memory.

    Note: CN's check.ml has `assert false` for LVunspecified (line 251), so we can't
    directly match their mechanism. Instead, we detect unspecified values here and
    handle them specially in handleStore. -/
def isUnspecifiedValue (pe : APexpr) : Bool :=
  match pe.expr with
  -- Direct unspecified loaded value: Vloaded(LVunspecified)
  | .val (.loaded (.unspecified _)) => true
  -- Unspecified constructor: Unspecified(ctype)
  | .ctor .unspecified _ => true
  | _ => false

/-! ## Memory Action Handlers

Each handler implements the separation logic semantics for a memory action.
-/

/-- Handle create action: allocate memory, produce Owned<T>(Uninit).
    Returns a fresh pointer.

    Separation logic rule:
    {emp} create(size, align) {∃p. Owned<T>(Uninit)(p) * p ↦ default}

    Corresponds to: Eaction Create case in check.ml lines 1780-1822

    Note: In Core IR, Create doesn't directly include the C type like muCore does.
    We infer it's a void* allocation. For proper type tracking, the calling context
    should provide the type information, or we should examine the size expression. -/
def handleCreate (align : APexpr) (size : APexpr) (ct : Ctype) (prefix_ : SymPrefix) (loc : Core.Loc)
    : TypingM IndexTerm := do
  -- Evaluate alignment expression
  let alignVal ← checkPexpr align
  -- Evaluate size expression (for constraint generation)
  let _sizeVal ← checkPexpr size

  -- Create a fresh pointer symbol
  -- Corresponds to: IT.fresh_named BT.(Loc ()) ("&" ^ str) loc in check.ml line 1791
  let ptrSym ← freshSym prefix_ loc
  let ptrTerm := AnnotTerm.mk (.sym ptrSym) .loc loc

  -- Get the base type for the default value
  let bt ← ctypeToBaseType ct loc

  -- Create default (uninitialized) value
  -- Corresponds to: O (default_ (Memory.bt_of_sct act.ct) loc) in check.ml line 1805
  let defaultVal := mkDefaultValue bt loc

  -- Produce Owned<T>(Uninit) resource
  -- Corresponds to: add_r loc (P { name = Owned (act.ct, Uninit); ... }, O ...) in check.ml 1802-1806
  let resource := mkOwnedResource ct .uninit ptrTerm defaultVal
  addResourceWithUnfold resource

  -- Add alignment fact: the freshly created pointer is aligned
  -- Corresponds to: let align_v = cast_ Memory.uintptr_bt arg loc in
  --                  add_c loc (LC.T (alignedI_ ~align:align_v ~t:ret loc)) in check.ml:1799-1800
  -- CN casts alignment to uintptr_bt (Bits(Unsigned, 64)) before building the constraint.
  -- CN adds this as a constraint (assumption), NOT as an obligation to prove.
  -- The create operation guarantees the returned pointer is aligned.
  -- CN: cast_ Memory.uintptr_bt arg loc (indexTerms.ml:683-684)
  -- cast_ only wraps if types differ; uintptr_bt = Bits(Unsigned, 64)
  let uintptrBt : BaseType := .bits .unsigned 64
  let alignCast := match alignVal.bt with
    | .bits .unsigned 64 => alignVal
    | _ => AnnotTerm.mk (.cast uintptrBt alignVal) uintptrBt loc
  let alignedLc := AnnotTerm.mk (.aligned ptrTerm alignCast) .bool loc
  TypingM.addC (.t alignedLc)
  -- TODO: Add Alloc predicate (add_r loc (P (Req.make_alloc ret), O lookup))

  -- Return the new pointer
  return ptrTerm

/-- Handle kill action: deallocate memory, consume Owned<T>.

    Separation logic rule:
    {Owned<T>(_)(p)} kill(p) {emp}

    Note: Kill can consume either Init or Uninit - when memory is being freed,
    the initialization state doesn't matter. We try Uninit first (simpler case),
    then fall back to Init.

    Corresponds to: Eaction Kill (Static ct) case in check.ml lines 1831-1846 -/
def handleKill (kind : KillKind) (ptrPe : APexpr) (loc : Core.Loc)
    : TypingM IndexTerm := do
  -- Evaluate pointer expression
  let ptr ← checkPexpr ptrPe

  -- Get the C type from the kill kind
  let ct := match kind with
    | .static ct => ct
    | .dynamic => Ctype.void  -- Dynamic kill (free) - type determined at runtime

  -- Lazy muCore: check for parameter stack slot FIRST, before resource consumption.
  -- CN's muCore doesn't include param slot kills in the callee — the caller manages them.
  -- This MUST be checked before resource consumption because the SMT slow path
  -- in predicateRequest could incorrectly consume an unrelated resource when
  -- it finds a single name-matching candidate at a different pointer.
  match ptr.term with
  | .sym s =>
    if ← TypingM.isParamStackSlot s.id then
      return mkUnitTerm loc
  | _ => pure ()

  -- First try to consume Owned<T>(Uninit) for this pointer
  let uninitPred : Predicate := {
    name := .owned (some ct) .uninit
    pointer := ptr
    iargs := []
  }

  match ← predicateRequest uninitPred with
  | some _ =>
    -- Resource consumed successfully
    -- TODO: Also consume Alloc predicate (Req.make_alloc arg)
    return mkUnitTerm loc
  | none =>
    -- Try consuming Owned<T>(Init) instead - memory may have been initialized
    let initPred : Predicate := {
      name := .owned (some ct) .init
      pointer := ptr
      iargs := []
    }
    match ← predicateRequest initPred with
    | some _ =>
      -- Resource consumed successfully
      return mkUnitTerm loc
    | none =>
      TypingM.fail (.other "Kill: no Owned resource found for pointer (possible double-free or use-after-free)")

/-- Handle store action: write to memory.
    Consumes Owned<T>(Uninit) or Owned<T>(Init), produces Owned<T>(Init) with the stored value.

    Separation logic rule:
    {Owned<T>(Uninit)(p)} *p = v {Owned<T>(Init)(p) ∧ *p == v}

    IMPORTANT: When storing an unspecified value (LVunspecified), the resource
    remains as Uninit, not becoming Init. This is because reading unspecified
    values is undefined behavior. An `int x;` declaration stores LVunspecified,
    so the memory remains logically "uninitialized" for CN's purposes.

    See "Design Note: Deviation from CN's Mechanism" above for why we handle
    LVunspecified specially instead of matching CN's exact implementation.

    Corresponds to: Eaction Store case in check.ml lines 1847-1891 -/
def handleStore (_locking : Bool) (tyPe : APexpr) (ptrPe : APexpr) (valPe : APexpr)
    (_order : Core.MemoryOrder) (loc : Core.Loc) : TypingM IndexTerm := do
  -- Extract the C type from the type expression
  -- Corresponds to: act.ct in check.ml
  let ct ← extractCtype tyPe loc

  -- Evaluate pointer and value expressions
  -- Simplify pointer for resource matching (strip PtrValidForDeref wrappers)
  let ptrRaw ← checkPexpr ptrPe
  let ptr := simplifyPointerForResource ptrRaw
  let val ← checkPexpr valPe

  -- Track the store for ccall argument resolution (lazy muCore transformation).
  -- When Core IR passes a stack slot to ccall, we need to resolve it to the
  -- stored value. Record the mapping: slot_sym_id → stored_value.
  -- Corresponds to: core_to_mucore elimination of create+store+ccall+kill pattern.
  match ptr.term with
  | .sym s => TypingM.recordStore s.id val
  | _ => pure ()  -- Non-symbol pointers can't be tracked

  -- Check if we're storing an unspecified value (uninitialized memory)
  -- If so, we should keep the resource as Uninit, not Init
  let storeIsUnspecified := isUnspecifiedValue valPe

  -- Check representability of stored value
  -- Corresponds to: representable_ (act.ct, varg) in check.ml:1863-1877
  -- CN generates this for ALL store types (integer, pointer, struct, etc.)
  -- Skip for unspecified values: these come from dead PEundef branches where
  -- the unreachability obligation (C7) already proves the branch is dead.
  -- CN's inline solver would prune these branches before reaching the store.
  if !storeIsUnspecified then
    let repLc := AnnotTerm.mk (.representable ct val) .bool loc
    TypingM.requireConstraint (.t repLc) loc "Write value not representable in type"

  -- Request (consume) Owned<T>(Uninit) - we need writable permission
  -- Corresponds to: RI.Special.predicate_request ... ({ name = Owned (act.ct, Uninit); ... }, None)
  let uninitPred : Predicate := {
    name := .owned (some ct) .uninit
    pointer := ptr
    iargs := []
  }

  -- First try to consume Uninit
  let consumed ← predicateRequest uninitPred
  match consumed with
  | some _ =>
    -- Consumed Uninit
    if storeIsUnspecified then
      -- Storing unspecified value: keep as Uninit (memory still logically uninitialized)
      let resource := mkOwnedResource ct .uninit ptr val
      addResourceWithUnfold resource
    else
      -- Storing specified value: produce Init
      -- Corresponds to: add_r loc (P { name = Owned (act.ct, Init); ... }, O varg) in check.ml 1885-1888
      let resource := mkOwnedResource ct .init ptr val
      addResourceWithUnfold resource
    return mkUnitTerm loc
  | none =>
    -- Try consuming Init instead (overwriting initialized memory)
    -- This is valid in CN - you can write to already-initialized memory
    let initPred : Predicate := {
      name := .owned (some ct) .init
      pointer := ptr
      iargs := []
    }
    match ← predicateRequest initPred with
    | some _ =>
      -- Consumed Init
      if storeIsUnspecified then
        -- Storing unspecified value to initialized memory: produces Uninit
        -- (This is unusual but handles re-declaring uninitialized variables)
        let resource := mkOwnedResource ct .uninit ptr val
        addResourceWithUnfold resource
      else
        -- Consumed Init, produce Init with new value
        let resource := mkOwnedResource ct .init ptr val
        addResourceWithUnfold resource
      return mkUnitTerm loc
    | none =>
      -- Fallback: param stack slot check (only when no resource found)
      -- CN's muCore eliminates stores to parameter slots entirely (core_to_mucore.ml).
      -- We handle them lazily here by updating the param value map.
      match ptr.term with
      | .sym s =>
        if ← TypingM.isParamStackSlot s.id then
          if !storeIsUnspecified then
            TypingM.addParamValue s.id val
          return mkUnitTerm loc
        else
          let ctx ← TypingM.getContext
          TypingM.fail (.missingResource (.p uninitPred) ctx)
      | _ =>
        let ctx ← TypingM.getContext
        TypingM.fail (.missingResource (.p uninitPred) ctx)

/-- Handle load action: read from memory.
    Consumes Owned<T>(Init), produces it back, returns the loaded value.

    Separation logic rule:
    {Owned<T>(Init)(p) ∧ *p == v} x = *p {Owned<T>(Init)(p) ∧ *p == v ∧ x == v}

    **Lazy muCore transformation**: If the pointer is a parameter stack slot
    (or alias thereof), we return the parameter value directly without
    resource tracking. This corresponds to CN's C_vars.Value handling in
    cn/lib/compile.ml line 1305.

    Corresponds to: Eaction Load case in check.ml lines 1892-1898 -/
def handleLoad (tyPe : APexpr) (ptrPe : APexpr) (_order : Core.MemoryOrder) (loc : Core.Loc)
    : TypingM IndexTerm := do
  -- Check if this is a load from a parameter stack slot (lazy muCore transformation)
  -- Corresponds to: C_vars.Value case in compile.ml line 1305
  match ptrPe.expr with
  | .sym s =>
    -- Check if this symbol (or what it aliases to) is a parameter stack slot
    match ← TypingM.lookupParamValue s.id with
    | some valueTerm =>
      -- This is a parameter load - return the value directly, no resource tracking
      -- This is the lazy equivalent of CN's Core-to-muCore transformation
      return valueTerm
    | none =>
      -- Not a parameter - fall through to normal resource-based load
      pure ()
  | _ =>
    -- Complex pointer expression - fall through to normal load
    pure ()

  -- Normal resource-based load
  -- Extract the C type from the type expression
  -- Corresponds to: act.ct in check.ml
  let ct ← extractCtype tyPe loc

  -- Evaluate pointer expression and simplify for resource matching
  -- Core IR wraps pointers in ite(PtrValidForDeref, ptr, undef) — strip this
  let ptrRaw ← checkPexpr ptrPe
  let ptr := simplifyPointerForResource ptrRaw

  -- Request (consume) Owned<T>(Init) - we need readable permission
  -- Load requires initialized memory (reading uninitialized is UB)
  let pred : Predicate := {
    name := .owned (some ct) .init
    pointer := ptr
    iargs := []
  }

  match ← predicateRequest pred with
  | some (_, output) =>
    -- Got the value, produce the resource back (non-destructive read)
    let resource := mkOwnedResource ct .init ptr output.value
    addResourceWithUnfold resource

    -- Return the loaded value
    return output.value
  | none =>
    -- No matching resource found - either no ownership or uninitialized
    let ctx ← TypingM.getContext
    TypingM.fail (.missingResource (.p pred) ctx)

/-! ## Main Action Checker

Dispatch to appropriate handler based on action type.
-/

/-- Infer Ctype from a size/type expression if possible.
    In Core IR, the type information can appear in different forms:
    1. As a Ctype value directly: `'signed int'` (parsed as .val (.ctype ct))
    2. As sizeof: `sizeof('signed int')` (parsed as .impl (.sizeof_ ct))

    Note: In muCore (which CN works on), the type is directly available as act.ct.
    Core IR encodes it differently, so we extract it from the expression. -/
def inferCtypeFromSize (size : APexpr) (loc : Core.Loc) : TypingM Ctype := do
  match size.expr with
  -- Pattern 1: Direct Ctype value (e.g., 'signed int')
  | .val (.ctype ct) => return ct
  -- Pattern 2: sizeof expression (e.g., sizeof('signed int'))
  | .impl (.sizeof_ ct) => return ct
  | _ =>
    -- Cannot infer type - this is a known limitation
    TypingM.fail (.other s!"Cannot infer C type from size expression at {repr loc}. Create/Alloc requires type context from muCore.")

/-- Check a memory action, consuming/producing resources as appropriate.
    Returns the result value of the action.

    Corresponds to: Eaction cases in check.ml lines 1778-1908 -/
def checkAction (pact : Paction) : TypingM IndexTerm := do
  let loc := pact.action.loc
  match pact.action.action with
  -- Memory allocation
  -- Corresponds to: Eaction Create case in check.ml lines 1780-1822
  | .create align size prefix_ =>
    -- Try to infer the type from the size expression
    let ct ← inferCtypeFromSize size loc
    handleCreate align size ct prefix_ loc

  -- Corresponds to: Eaction CreateReadOnly case in check.ml line 1823-1824
  | .createReadonly _align size init prefix_ =>
    -- Try to infer the type from the size expression
    let ct ← inferCtypeFromSize size loc
    -- First evaluate the init value
    let initVal ← checkPexpr init
    -- Create a fresh pointer
    let ptrSym ← freshSym prefix_ loc
    let ptrTerm := AnnotTerm.mk (.sym ptrSym) .loc loc
    -- Produce Owned<T>(Init) with the init value
    let resource := mkOwnedResource ct .init ptrTerm initVal
    addResourceWithUnfold resource
    return ptrTerm

  -- Corresponds to: Eaction Alloc case in check.ml lines 1825-1827
  | .alloc align size prefix_ =>
    -- alloc is similar to create (malloc-style allocation)
    let ct ← inferCtypeFromSize size loc
    handleCreate align size ct prefix_ loc

  -- Memory deallocation
  -- Corresponds to: Eaction Kill case in check.ml lines 1828-1846
  | .kill kind ptr =>
    handleKill kind ptr loc

  -- Memory write
  -- Corresponds to: Eaction Store case in check.ml lines 1847-1891
  | .store locking ty ptr val order =>
    handleStore locking ty ptr val order loc

  -- Memory read
  -- Corresponds to: Eaction Load case in check.ml lines 1892-1898
  | .load ty ptr order =>
    handleLoad ty ptr order loc

  -- Atomic read-modify-write
  -- Corresponds to: Eaction RMW case in check.ml line 1899
  | .rmw _ty _ptr _expected _desired _successOrd _failOrd =>
    -- RMW is not fully implemented in CN either
    TypingM.fail (.other s!"RMW operations not yet supported at {repr loc}")

  -- Memory fence (no resource changes)
  -- Corresponds to: Eaction Fence case in check.ml line 1900
  | .fence _order =>
    return mkUnitTerm loc

  -- Compare-exchange operations
  -- Corresponds to: Eaction CompareExchangeStrong/Weak cases in check.ml lines 1901-1904
  | .compareExchangeStrong _ty _ptr _expected _desired _successOrd _failOrd =>
    TypingM.fail (.other s!"CompareExchangeStrong not yet supported at {repr loc}")

  | .compareExchangeWeak _ty _ptr _expected _desired _successOrd _failOrd =>
    TypingM.fail (.other s!"CompareExchangeWeak not yet supported at {repr loc}")

  -- Sequential RMW: atomic load + compute + store (pre/post-increment)
  -- isUpdate=true: return NEW value (pre-increment ++i)
  -- isUpdate=false: return OLD value (post-increment i++)
  -- Corresponds to: core_reduction.lem:1214-1276
  -- DIVERGES-FROM-CN: CN's core_to_mucore doesn't support SeqRMW (assert_error).
  -- We implement it as load + eval + store since it's needed for C pre/post-increment.
  -- Audited: 2026-02-19
  | .seqRmw isUpdate tyPe ptrPe sym valPe =>
    -- Step 1: Extract type and pointer
    let ct ← extractCtype tyPe loc
    let ptrRaw ← checkPexpr ptrPe
    let ptr := simplifyPointerForResource ptrRaw

    -- Check if this is a SeqRMW on a parameter stack slot (lazy muCore transformation).
    -- In CN's muCore, SeqRMW doesn't exist (assert_error). For parameter slots,
    -- we handle it by reading/updating the param value map instead of resources.
    match ptr.term with
    | .sym s =>
      if ← TypingM.isParamStackSlot s.id then
        -- Parameter slot SeqRMW: read old value from param map, compute new, update map
        match ← TypingM.lookupParamValue s.id with
        | some oldValue =>
          -- Bind sym to old value and evaluate update expression
          TypingM.addAValue sym oldValue loc "seqRmw param loaded value"
          let newValue ← checkPexpr valPe
          -- Representability check
          let repLc := AnnotTerm.mk (.representable ct newValue) .bool loc
          TypingM.requireConstraint (.t repLc) loc "SeqRMW value not representable in type"
          -- Update param value
          TypingM.addParamValue s.id newValue
          -- Return old or new value
          if isUpdate then return newValue else return oldValue
        | none =>
          TypingM.fail (.other s!"SeqRMW: parameter slot has no value")
      else pure ()
    | _ => pure ()

    -- Step 2: Load - consume Owned<T>(Init), get old value
    let loadPred : Predicate := {
      name := .owned (some ct) .init
      pointer := ptr
      iargs := []
    }
    match ← predicateRequest loadPred with
    | none =>
      let ctx ← TypingM.getContext
      TypingM.fail (.missingResource (.p loadPred) ctx)
    | some (_, output) =>
      let oldValue := output.value

      -- Step 3: Bind sym to old value and evaluate update expression
      TypingM.addAValue sym oldValue loc "seqRmw loaded value"
      let newValue ← checkPexpr valPe

      -- Step 4: Store - produce Owned<T>(Init) with new value
      -- (The old Owned was consumed by the load above)
      let repLc := AnnotTerm.mk (.representable ct newValue) .bool loc
      TypingM.requireConstraint (.t repLc) loc "SeqRMW value not representable in type"
      let resource := mkOwnedResource ct .init ptr newValue
      addResourceWithUnfold resource

      -- Step 5: Return old value (post-inc) or new value (pre-inc)
      if isUpdate then
        return newValue
      else
        return oldValue

/-! ## CPS Version

For consistency with the CPS-style expression checking, we provide
a continuation-passing version of checkAction.
-/

/-- Check a memory action using continuation-passing style.

    For actions, we call the original checkAction and pass
    the result to the continuation. This provides a uniform interface
    with checkExprK.

    Corresponds to: Eaction continuation handling in check.ml -/
def checkActionK (pact : Paction) (k : IndexTerm → TypingM Unit) : TypingM Unit := do
  let result ← checkAction pact
  k result

end CerbLean.CN.TypeChecking
