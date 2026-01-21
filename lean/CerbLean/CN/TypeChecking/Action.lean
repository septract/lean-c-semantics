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
    name := .owned ct initState
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

/-- Convert Ctype to CN BaseType.
    Fails on unsupported types rather than silently returning a default.

    Corresponds to: Memory.bt_of_sct in CN OCaml -/
def ctypeToBaseType (ct : Ctype) (loc : Core.Loc) : TypingM BaseType := do
  match ct.ty with
  | .void => return .unit
  | .basic (.integer _) => return .integer
  | .basic (.floating _) => return .real
  | .pointer _ _ => return .loc
  | .struct_ tag => return .struct_ tag
  | .array _ _ =>
    -- Arrays require proper handling - fail explicitly
    TypingM.fail (.other s!"Array types not yet supported in ctypeToBaseType at {repr loc}")
  | .union_ tag =>
    TypingM.fail (.other s!"Union type {repr tag} not yet supported at {repr loc}")
  | .function _ _ _ _ =>
    TypingM.fail (.other s!"Function types not supported in ctypeToBaseType at {repr loc}")
  | .functionNoParams _ _ =>
    TypingM.fail (.other s!"Function types not supported in ctypeToBaseType at {repr loc}")
  | .atomic _ =>
    TypingM.fail (.other s!"Atomic types not yet supported in ctypeToBaseType at {repr loc}")
  | .byte =>
    -- Byte is an internal type, maps to memory byte
    return .memByte

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
  -- Evaluate alignment expression (for constraint generation)
  let _alignVal ← checkPexpr align
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
  TypingM.addR resource

  -- TODO: Add alignment constraint (LC.T (alignedI_ ~align:align_v ~t:ret loc))
  -- TODO: Add Alloc predicate (add_r loc (P (Req.make_alloc ret), O lookup))

  -- Return the new pointer
  return ptrTerm

/-- Handle kill action: deallocate memory, consume Owned<T>(Uninit).

    Separation logic rule:
    {Owned<T>(Uninit)(p)} kill(p) {emp}

    Corresponds to: Eaction Kill (Static ct) case in check.ml lines 1831-1846 -/
def handleKill (kind : KillKind) (ptrPe : APexpr) (loc : Core.Loc)
    : TypingM IndexTerm := do
  -- Evaluate pointer expression
  let ptr ← checkPexpr ptrPe

  -- Get the C type from the kill kind
  let ct := match kind with
    | .static ct => ct
    | .dynamic => Ctype.void  -- Dynamic kill (free) - type determined at runtime

  -- Request (consume) Owned<T>(Uninit) for this pointer
  -- Corresponds to: RI.Special.predicate_request ... ({ name = Owned (ct, Uninit); ... }, None)
  let pred : Predicate := {
    name := .owned ct .uninit
    pointer := ptr
    iargs := []
  }

  match ← predicateRequest pred with
  | some _ =>
    -- Resource consumed successfully
    -- TODO: Also consume Alloc predicate (Req.make_alloc arg)
    return mkUnitTerm loc
  | none =>
    -- No matching resource found
    let ctx ← TypingM.getContext
    TypingM.fail (.missingResource (.p pred) ctx)

/-- Handle store action: write to memory.
    Consumes Owned<T>(Uninit) or Owned<T>(Init), produces Owned<T>(Init) with the stored value.

    Separation logic rule:
    {Owned<T>(Uninit)(p)} *p = v {Owned<T>(Init)(p) ∧ *p == v}

    Corresponds to: Eaction Store case in check.ml lines 1847-1891 -/
def handleStore (_locking : Bool) (tyPe : APexpr) (ptrPe : APexpr) (valPe : APexpr)
    (_order : Core.MemoryOrder) (loc : Core.Loc) : TypingM IndexTerm := do
  -- Extract the C type from the type expression
  -- Corresponds to: act.ct in check.ml
  let ct ← extractCtype tyPe loc

  -- Evaluate pointer and value expressions
  let ptr ← checkPexpr ptrPe
  let val ← checkPexpr valPe

  -- TODO: Check representability of the value
  -- Corresponds to: representable_ (act.ct, varg) in check.ml lines 1863-1877
  -- let in_range_lc := representable ct val
  -- TypingM.ensureProvable in_range_lc

  -- Request (consume) Owned<T>(Uninit) - we need writable permission
  -- Corresponds to: RI.Special.predicate_request ... ({ name = Owned (act.ct, Uninit); ... }, None)
  let uninitPred : Predicate := {
    name := .owned ct .uninit
    pointer := ptr
    iargs := []
  }

  -- First try to consume Uninit
  let consumed ← predicateRequest uninitPred
  match consumed with
  | some _ =>
    -- Consumed Uninit, now produce Init with the stored value
    -- Corresponds to: add_r loc (P { name = Owned (act.ct, Init); ... }, O varg) in check.ml 1885-1888
    let resource := mkOwnedResource ct .init ptr val
    TypingM.addR resource
    return mkUnitTerm loc
  | none =>
    -- Try consuming Init instead (overwriting initialized memory)
    -- This is valid in CN - you can write to already-initialized memory
    let initPred : Predicate := {
      name := .owned ct .init
      pointer := ptr
      iargs := []
    }
    match ← predicateRequest initPred with
    | some _ =>
      -- Consumed Init, produce Init with new value
      let resource := mkOwnedResource ct .init ptr val
      TypingM.addR resource
      return mkUnitTerm loc
    | none =>
      -- No matching resource found
      let ctx ← TypingM.getContext
      TypingM.fail (.missingResource (.p uninitPred) ctx)

/-- Handle load action: read from memory.
    Consumes Owned<T>(Init), produces it back, returns the loaded value.

    Separation logic rule:
    {Owned<T>(Init)(p) ∧ *p == v} x = *p {Owned<T>(Init)(p) ∧ *p == v ∧ x == v}

    Corresponds to: Eaction Load case in check.ml lines 1892-1898 -/
def handleLoad (tyPe : APexpr) (ptrPe : APexpr) (_order : Core.MemoryOrder) (loc : Core.Loc)
    : TypingM IndexTerm := do
  -- Extract the C type from the type expression
  -- Corresponds to: act.ct in check.ml
  let ct ← extractCtype tyPe loc

  -- Evaluate pointer expression
  let ptr ← checkPexpr ptrPe

  -- Request (consume) Owned<T>(Init) - we need readable permission
  -- Load requires initialized memory (reading uninitialized is UB)
  let pred : Predicate := {
    name := .owned ct .init
    pointer := ptr
    iargs := []
  }

  match ← predicateRequest pred with
  | some (_, output) =>
    -- Got the value, produce the resource back (non-destructive read)
    let resource := mkOwnedResource ct .init ptr output.value
    TypingM.addR resource

    -- Return the loaded value
    return output.value
  | none =>
    -- No matching resource found - either no ownership or uninitialized
    let ctx ← TypingM.getContext
    TypingM.fail (.missingResource (.p pred) ctx)

/-! ## Main Action Checker

Dispatch to appropriate handler based on action type.
-/

/-- Infer Ctype from a size expression if possible.
    In Core IR, the size expression often contains type information.
    Returns void if type cannot be inferred (with a note that this is a limitation).

    Note: In muCore (which CN works on), the type is directly available as act.ct.
    Core IR doesn't have this, so we must infer it or accept the limitation. -/
def inferCtypeFromSize (size : APexpr) (loc : Core.Loc) : TypingM Ctype := do
  -- Try to extract type from size expression
  -- Common pattern: size is `sizeof(T)` which contains the type
  match size.expr with
  | .impl (.sizeof_ ct) => return ct
  | _ =>
    -- Cannot infer type from size - this is a known limitation
    -- In a production system, we would need type annotations from the context
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
    TypingM.addR resource
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

  -- Sequential RMW (for BMC)
  | .seqRmw _isUpdate _ty _ptr _sym _val =>
    TypingM.fail (.other s!"SeqRMW not yet supported at {repr loc}")

end CerbLean.CN.TypeChecking
