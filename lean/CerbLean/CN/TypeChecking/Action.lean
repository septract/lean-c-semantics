/-
  CN Memory Action Checking
  Corresponds to: cn/lib/check.ml (Eaction cases)

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

open CerbLean.Core (Sym Paction AAction Action APexpr Ctype KillKind SymPrefix)
open CerbLean.CN.Types

/-! ## Fresh Symbol Generation

Generate fresh symbols for newly allocated memory.
In a full implementation, this would use a counter in the state.
-/

/-- Simple counter state for fresh symbols -/
private def freshSymCounter : IO (IO.Ref Nat) :=
  IO.mkRef 0

/-- Create a fresh symbol with the given prefix -/
def freshSym (prefix_ : SymPrefix) (_loc : Core.Loc) : TypingM Sym := do
  -- For now, use a simple deterministic approach based on prefix
  -- In a full implementation, we'd have a proper fresh name generator
  return { id := 0, name := some prefix_.val }

/-! ## Creating Resources

Helper functions to create Owned predicates.
-/

/-- Create an Owned resource predicate
    Corresponds to the creation of Owned<ct>(init)(ptr) with output value -/
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

/-- Convert Ctype to CN BaseType (simplified) -/
def ctypeToBaseType (ct : Ctype) : BaseType :=
  match ct.ty with
  | .void => .unit
  | .basic (.integer _) => .integer
  | .basic (.floating _) => .real
  | .pointer _ _ => .loc
  | .struct_ tag => .struct_ tag
  | .array _ _ => .unit  -- TODO: proper array type
  | _ => .unit  -- Default for unsupported types

/-! ## Memory Action Handlers

Each handler implements the separation logic semantics for a memory action.
-/

/-- Handle create action: allocate memory, produce Owned<T>(Uninit).
    Returns a fresh pointer.

    Separation logic rule:
    {emp} create(size, align) {∃p. Owned<T>(Uninit)(p) * p ↦ default}

    Corresponds to: Eaction Create case in check.ml -/
def handleCreate (align : APexpr) (size : APexpr) (prefix_ : SymPrefix) (loc : Core.Loc)
    : TypingM IndexTerm := do
  -- Evaluate size expression to get the C type
  let _sizeVal ← checkPexpr size

  -- Create a fresh pointer symbol
  let ptrSym ← freshSym prefix_ loc
  let ptrTerm := AnnotTerm.mk (.sym ptrSym) .loc loc

  -- We need the C type to create the resource
  -- For now, assume void* and produce a generic Owned resource
  let ct := Ctype.void
  let bt := ctypeToBaseType ct

  -- Create default (uninitialized) value
  let defaultVal := mkDefaultValue bt loc

  -- Produce Owned<T>(Uninit) resource
  let resource := mkOwnedResource ct .uninit ptrTerm defaultVal
  TypingM.addR resource

  -- Return the new pointer
  return ptrTerm

/-- Handle kill action: deallocate memory, consume Owned<T>(Uninit).

    Separation logic rule:
    {Owned<T>(Uninit)(p)} kill(p) {emp}

    Corresponds to: Eaction Kill case in check.ml -/
def handleKill (_kind : KillKind) (ptrPe : APexpr) (loc : Core.Loc)
    : TypingM IndexTerm := do
  -- Evaluate pointer expression
  let ptr ← checkPexpr ptrPe

  -- Request (consume) Owned<T>(Uninit) for this pointer
  -- We need to find a matching resource in the context
  let ct := Ctype.void  -- TODO: get actual type
  let pred : Predicate := {
    name := .owned ct .uninit
    pointer := ptr
    iargs := []
  }

  match ← predicateRequest pred with
  | some _ =>
    -- Resource consumed successfully
    return mkUnitTerm loc
  | none =>
    -- No matching resource found
    let ctx ← TypingM.getContext
    TypingM.fail (.missingResource (.p pred) ctx)

/-- Handle store action: write to memory.
    Consumes Owned<T>(Uninit), produces Owned<T>(Init) with the stored value.

    Separation logic rule:
    {Owned<T>(Uninit)(p)} *p = v {Owned<T>(Init)(p) ∧ *p == v}

    Corresponds to: Eaction Store case in check.ml -/
def handleStore (_locking : Bool) (tyPe : APexpr) (ptrPe : APexpr) (valPe : APexpr)
    (_order : Core.MemoryOrder) (loc : Core.Loc) : TypingM IndexTerm := do
  -- Evaluate pointer and value expressions
  let ptr ← checkPexpr ptrPe
  let val ← checkPexpr valPe

  -- Get the C type from the type expression
  -- For now, use a simplified approach
  let _tyTerm ← checkPexpr tyPe
  let ct := Ctype.integer (.signed .int_)  -- TODO: extract actual type

  -- Request (consume) Owned<T>(Uninit) - we need writable permission
  -- In CN, we can write to either Uninit or Init memory
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
    let resource := mkOwnedResource ct .init ptr val
    TypingM.addR resource
    return mkUnitTerm loc
  | none =>
    -- Try consuming Init instead (overwriting initialized memory)
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

    Corresponds to: Eaction Load case in check.ml -/
def handleLoad (tyPe : APexpr) (ptrPe : APexpr) (_order : Core.MemoryOrder) (loc : Core.Loc)
    : TypingM IndexTerm := do
  -- Evaluate pointer expression
  let ptr ← checkPexpr ptrPe

  -- Get the C type from the type expression
  let _tyTerm ← checkPexpr tyPe
  let ct := Ctype.integer (.signed .int_)  -- TODO: extract actual type

  -- Request (consume) Owned<T>(Init) - we need readable permission
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
    -- No matching resource found
    let ctx ← TypingM.getContext
    TypingM.fail (.missingResource (.p pred) ctx)

/-! ## Main Action Checker

Dispatch to appropriate handler based on action type.
-/

/-- Check a memory action, consuming/producing resources as appropriate.
    Returns the result value of the action.

    Corresponds to: Eaction cases in check.ml lines 1778-1908 -/
def checkAction (pact : Paction) : TypingM IndexTerm := do
  let loc := pact.action.loc
  match pact.action.action with
  -- Memory allocation
  | .create align size prefix_ =>
    handleCreate align size prefix_ loc

  | .createReadonly align size init prefix_ =>
    -- For readonly, we still create but with Init state
    -- First evaluate the init value
    let initVal ← checkPexpr init
    -- Create a fresh pointer
    let ptrSym ← freshSym prefix_ loc
    let ptrTerm := AnnotTerm.mk (.sym ptrSym) .loc loc
    -- Produce Owned<T>(Init) with the init value
    let ct := Ctype.void  -- TODO: get actual type
    let resource := mkOwnedResource ct .init ptrTerm initVal
    TypingM.addR resource
    return ptrTerm

  | .alloc align size prefix_ =>
    -- alloc is similar to create (malloc-style allocation)
    handleCreate align size prefix_ loc

  -- Memory deallocation
  | .kill kind ptr =>
    handleKill kind ptr loc

  -- Memory write
  | .store locking ty ptr val order =>
    handleStore locking ty ptr val order loc

  -- Memory read
  | .load ty ptr order =>
    handleLoad ty ptr order loc

  -- Atomic read-modify-write (not fully implemented)
  | .rmw ty ptr _expected _desired _successOrd _failOrd =>
    -- Simplified: just load the value
    handleLoad ty ptr .seqCst loc

  -- Memory fence (no resource changes)
  | .fence _order =>
    return mkUnitTerm loc

  -- Compare-exchange operations (simplified)
  | .compareExchangeStrong ty ptr _expected _desired _successOrd _failOrd =>
    handleLoad ty ptr .seqCst loc

  | .compareExchangeWeak ty ptr _expected _desired _successOrd _failOrd =>
    handleLoad ty ptr .seqCst loc

  -- Sequential RMW (for BMC)
  | .seqRmw _isUpdate ty ptr _sym val =>
    -- Simplified: just do a store
    let loc' := pact.action.loc
    let valPe : APexpr := ⟨[], none, .val .unit⟩  -- Placeholder
    handleStore false ty ptr valPe .seqCst loc'

end CerbLean.CN.TypeChecking
