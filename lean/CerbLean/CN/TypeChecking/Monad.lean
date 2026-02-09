/-
  CN Typing Monad
  Corresponds to: cn/lib/typing.ml

  The typing monad is a state monad that tracks:
  - The typing context (variables, resources, constraints)
  - Accumulated proof obligations for post-hoc SMT discharge

  Key design decision: All proof queries go through obligation accumulation.
  Type checking produces a list of obligations (implications: assumptions → constraint)
  that are discharged by an external SMT solver after type checking completes.
  This clean separation supports a soundness theorem:
    if type checking succeeds AND all obligations are valid, then the program is safe.

  Audited: 2026-01-20 against cn/lib/typing.ml
-/

import CerbLean.CN.TypeChecking.Context
import CerbLean.CN.Types
import CerbLean.CN.Verification.Obligation
import CerbLean.Core.MuCore
import CerbLean.Core.File
import Std.Data.HashMap

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc Identifier FieldDef TagDef TagDefs)
open CerbLean.Core.MuCore (LabelDefs LabelDef LabelInfo)
open CerbLean.CN.Types
open CerbLean.CN.Verification

/-! ## Type Errors

Corresponds to: cn/lib/typeErrors.ml
-/

/-- Type checking errors
    Corresponds to: TypeErrors.t in cn/lib/typeErrors.ml -/
inductive TypeError where
  /-- Missing resource that was requested -/
  | missingResource (request : Request) (context : Context)
  /-- Constraint could not be proved -/
  | unprovableConstraint (constraint : LogicalConstraint) (context : Context)
  /-- Variable not in scope -/
  | unboundVariable (sym : Sym)
  /-- Generic error with message -/
  | other (msg : String)
  deriving Inhabited

instance : ToString TypeError where
  toString
    | .missingResource req ctx =>
      let reqStr := match req with
        | .p pred => s!"predicate {repr pred.name}"
        | .q qpred => s!"quantified predicate {repr qpred.name}"
      let ctxStr := if ctx.resources.isEmpty then "  (context has no resources)"
        else ctx.resources.foldl (init := "") fun acc r =>
          let rName := match r.request with
            | .p p => s!"predicate {repr p.name}"
            | .q q => s!"quantified predicate {repr q.name}"
          acc ++ s!"\n    - {rName}"
      s!"missing resource: {reqStr}\n  Available resources:{ctxStr}"
    | .unprovableConstraint _lc _ctx => "unprovable constraint"
    | .unboundVariable sym => s!"unbound variable: {sym.name.getD "?"}"
    | .other msg => msg

/-! ## Conditional Failures

A conditional failure represents a type error from a branch that may be dead.
Instead of propagating the error immediately (which would block checking of
live branches), we catch it and create an obligation proving the branch is dead.

Post-hoc, the SMT solver checks: assumptions → ¬branchCondition.
If valid (branch IS dead): error is vacuous, discard.
If invalid (branch is live): error is genuine, report.

This is our equivalent of CN's inline `provable(false)` dead-branch detection
(check.ml:1985-2002), deferred to post-hoc SMT discharge.

Nesting works because each conditional failure captures the FULL assumption set
(all enclosing branch conditions via addC). If an outer path is contradictory,
all inner CFs under that path are vacuously true.
-/

/-- A type error conditional on a branch being taken.
    If the obligation is valid (branch is dead), the error is vacuous.
    If invalid (branch is live), the error is genuine. -/
structure ConditionalFailure where
  /-- Obligation: assumptions → ¬branchCondition (prove branch is dead) -/
  obligation : Obligation
  /-- The original type error from checking the branch -/
  originalError : TypeError

/-! ## Typing Monad State

Corresponds to: cn/lib/typing.ml lines 11-17
```ocaml
type s =
  { typing_context : Context.t;
    solver : solver option;
    sym_eqs : IT.t Sym.Map.t;
    movable_indices : (Req.name * IT.t) list;
    log : Explain.log
  }
```
-/

/-! ## Function Specification Map

Corresponds to: fun_decls in cn/lib/global.ml lines 11
  fun_decls : (Locations.t * AT.ft option * Sctypes.c_concrete_sig) Sym.Map.t

Pre-built function types for resolving C function calls (Eccall).
Each function with a CN spec gets its type pre-built during initialization.
-/

/-- Pre-built function type map for callee spec lookup.
    Keyed by function symbol ID.
    Corresponds to: AT.ft option in Global.fun_decls -/
abbrev FunctionSpecMap := Std.HashMap Nat (Types.AT Types.ReturnType)

/-! ## Parameter Value Map

Corresponds to: C_vars.Value in cn/lib/compile.ml lines 332-333.

In Core IR, function parameters are stored in stack slots. The value is
obtained by loading from the slot. CN's core_to_mucore transformation
maps stack slot symbols to their value symbols, so that loads from
parameter stack slots are replaced with direct value references.

We track this mapping in the typing state to implement the same transformation
at type-checking time.
-/

/-- Maps stack slot symbol ID → value IndexTerm
    When a load is performed from a symbol in this map, we return the
    value term directly without consuming any resources.

    Corresponds to: C_vars.Value (sym, sbt) in compile.ml -/
abbrev ParamValueMap := Std.HashMap Nat IndexTerm

/-- Typing monad state
    Corresponds to: s in typing.ml lines 11-17
    Simplified: we omit sym_eqs, movable_indices, log for now

    All proof queries go through obligation accumulation. Type checking
    produces obligations that are discharged by an external SMT solver. -/
structure TypingState where
  /-- Current typing context -/
  context : Context
  /-- Counter for generating fresh symbols -/
  freshCounter : Nat := 0
  /-- Parameter value mapping: stack slot ID → value term
      Corresponds to: C_vars state in cn/lib/compile.ml -/
  paramValues : ParamValueMap := {}
  /-- Label definitions from muCore transformation.
      Maps label symbols to their definitions (return vs regular).
      Corresponds to: mi_label_defs in milicore.ml -/
  labelDefs : LabelDefs := []
  /-- Function specification map for resolving ccall.
      Pre-built function types keyed by symbol ID.
      Corresponds to: fun_decls in cn/lib/global.ml -/
  functionSpecs : FunctionSpecMap := {}
  /-- Function info map for looking up C-level function signatures.
      Used by cfunction(), params_length, etc. for concrete evaluation.
      Corresponds to: funinfo in Core file -/
  funInfoMap : Core.FunInfoMap := {}
  /-- Store value tracking: slot symbol ID → most recently stored value.
      Used for lazy muCore transformation of ccall argument slots.
      Corresponds to: core_to_mucore function call argument transformation -/
  storeValues : Std.HashMap Nat IndexTerm := {}
  /-- Tag definitions for struct/union layout lookup.
      Used by struct resource unpacking (do_unfold_resources in CN).
      Corresponds to: Global.struct_decls in cn/lib/global.ml -/
  tagDefs : TagDefs := []
  /-- Accumulated proof obligations for post-hoc SMT discharge -/
  obligations : ObligationSet := []
  /-- Conditional failures: type errors from branches that may be dead.
      Each pairs an obligation (prove branch is dead) with the original error.
      Discharged post-hoc by SMT. -/
  conditionalFailures : List ConditionalFailure := []
  /-- Whether this execution path has returned.
      When true, subsequent code should be skipped (return is terminal). -/
  hasReturned : Bool := false
  deriving Inhabited

namespace TypingState

def empty : TypingState :=
  { context := Context.empty, freshCounter := 0 }

def withContext (ctx : Context) : TypingState :=
  { context := ctx, freshCounter := 0 }

end TypingState

/-! ## Typing Monad

Corresponds to: cn/lib/typing.ml lines 28-30
```ocaml
type 'a t = s -> ('a * s, TypeErrors.t) Result.t
```
-/

/-- The typing monad: state + error
    Corresponds to: 'a t in typing.ml line 30 -/
abbrev TypingM (α : Type) := StateT TypingState (Except TypeError) α

namespace TypingM

/-! ### Basic Operations

Corresponds to: typing.ml lines 36-54
-/

/-- Get the current state -/
def getState : TypingM TypingState := StateT.get

/-- Set the state -/
def setState (s : TypingState) : TypingM Unit := StateT.set s

/-- Modify the state -/
def modifyState (f : TypingState → TypingState) : TypingM Unit := do
  let s ← getState
  setState (f s)

/-- Get the typing context -/
def getContext : TypingM Context := do
  let s ← getState
  return s.context

/-- Get the label definitions -/
def getLabelDefs : TypingM LabelDefs := do
  let s ← getState
  return s.labelDefs

/-- Look up a function spec by symbol ID.
    Corresponds to: Global.get_fun_decl in cn/lib/global.ml -/
def lookupFunctionSpec (symId : Nat) : TypingM (Option (Types.AT Types.ReturnType)) := do
  let s ← getState
  return s.functionSpecs.get? symId

/-- Generate a fresh symbol with a descriptive name.
    Corresponds to: Sym.fresh_make_uniq_kind in CN -/
def freshSym (name : String) : TypingM Core.Sym := do
  let s ← getState
  let id := s.freshCounter
  modifyState fun s => { s with freshCounter := s.freshCounter + 1 }
  return { id := id, name := some name, digest := "", description := .none_ }

/-- Check if the current path has returned -/
def hasReturned : TypingM Bool := do
  let s ← getState
  return s.hasReturned

/-- Mark the current path as having returned -/
def setReturned : TypingM Unit := do
  modifyState fun s => { s with hasReturned := true }

/-- Set the typing context -/
def setContext (ctx : Context) : TypingM Unit := do
  modifyState fun s => { s with context := ctx }

/-- Modify the typing context -/
def modifyContext (f : Context → Context) : TypingM Unit := do
  modifyState fun s => { s with context := f s.context }

/-- Fail with a type error -/
def fail (err : TypeError) : TypingM α :=
  throw err

/-- Run the typing monad -/
def run (m : TypingM α) (s : TypingState) : Except TypeError (α × TypingState) :=
  StateT.run m s

/-- Run the typing monad, discarding final state -/
def run' (m : TypingM α) (s : TypingState) : Except TypeError α :=
  StateT.run' m s

/-! ### Context Operations

These mirror the operations in cn/lib/typing.ml lines 141-178
-/

/-- Add a computational variable
    Corresponds to: add_a in typing.ml -/
def addA (s : Sym) (bt : BaseType) (loc : Loc) (desc : String) : TypingM Unit := do
  modifyContext (Context.addA s bt ⟨loc, desc⟩)

/-- Add a computational variable with a value
    Corresponds to: add_a_value in typing.ml -/
def addAValue (s : Sym) (v : IndexTerm) (loc : Loc) (desc : String) : TypingM Unit := do
  modifyContext (Context.addAValue s v ⟨loc, desc⟩)

/-- Add a logical variable
    Corresponds to: add_l in typing.ml -/
def addL (s : Sym) (bt : BaseType) (loc : Loc) (desc : String) : TypingM Unit := do
  modifyContext (Context.addL s bt ⟨loc, desc⟩)

/-- Add a logical variable with a value
    Corresponds to: add_l_value in typing.ml -/
def addLValue (s : Sym) (v : IndexTerm) (loc : Loc) (desc : String) : TypingM Unit := do
  modifyContext (Context.addLValue s v ⟨loc, desc⟩)

/-- Add a constraint
    Corresponds to: add_c in typing.ml -/
def addC (lc : LogicalConstraint) : TypingM Unit := do
  modifyContext (Context.addC lc)

/-- Look up a tag definition from the state.
    Corresponds to: Sym.Map.find tag global.struct_decls -/
def lookupTag (tag : Sym) : TypingM (Option TagDef) := do
  let s ← getState
  return s.tagDefs.find? (·.1 == tag) |>.map (·.2.2)

/-- Add a resource
    Corresponds to: add_r in typing.ml -/
def addR (r : Resource) : TypingM Unit := do
  modifyContext (Context.addR r)

/-- Get all resources
    Corresponds to: all_resources in typing.ml -/
def getResources : TypingM (List Resource) := do
  let ctx ← getContext
  return ctx.resources

/-- Get all constraints (assumptions) -/
def getConstraints : TypingM LCSet := do
  let ctx ← getContext
  return ctx.constraints

/-! ### Proof Obligation Operations

All proof queries go through obligation accumulation. Type checking produces
a list of obligations (implications: assumptions → constraint) that are
discharged by an external SMT solver after type checking completes.
-/

/-- Get accumulated obligations -/
def getObligations : TypingM ObligationSet := do
  let s ← getState
  return s.obligations

/-- Add a proof obligation -/
def addObligation (ob : Obligation) : TypingM Unit := do
  modifyState fun s => { s with obligations := ObligationSet.add ob s.obligations }

/-- Add a constraint as a proof obligation for post-hoc SMT discharge.
    Captures the current constraints as assumptions: the obligation semantically
    means "under the current assumptions, the constraint holds".

    Corresponds to: requireConstraint pattern in CN type checking -/
def requireConstraint (lc : LogicalConstraint) (loc : Loc) (desc : String := "constraint") : TypingM Unit := do
  let assumptions ← getConstraints
  let ob := Obligation.arithmetic desc lc assumptions loc
  addObligation ob

/-- Add multiple constraints as obligations.
    All obligations capture the same assumptions (current constraints). -/
def requireConstraints (lcs : LCSet) (loc : Loc) : TypingM Unit := do
  for lc in lcs do
    requireConstraint lc loc

/-! ### Resource Manipulation -/

/-- Update resources with a transformation function -/
def mapResources (f : Resource → Resource) : TypingM Unit := do
  modifyContext fun ctx => { ctx with resources := ctx.resources.map f }

/-- Filter resources, keeping those that satisfy predicate -/
def filterResources (p : Resource → Bool) : TypingM Unit := do
  modifyContext fun ctx => { ctx with resources := ctx.resources.filter p }

/-- Replace all resources -/
def setResources (rs : List Resource) : TypingM Unit := do
  modifyContext (Context.setResources rs)

/-- Remove a resource at the given index (for consumption) -/
def removeResourceAt (idx : Nat) : TypingM Unit := do
  modifyContext (Context.removeRAt idx)

/-! ### Parameter Value Mapping

These functions manage the lazy muCore transformation for function parameters.
Corresponds to: C_vars operations in cn/lib/compile.ml

In CN, Core-to-muCore translation maps stack slot symbols to value terms
so that `load(T, stack_slot)` becomes `pure(value)`. We do this lazily
during type checking by maintaining a ParamValueMap.
-/

/-- Add a parameter value mapping: stack_slot_id → value_term
    Corresponds to: C_vars.add [(mut_arg, Value(pure_arg, sbt))] in
    cn/lib/core_to_mucore.ml line 755 -/
def addParamValue (stackSlotId : Nat) (valueTerm : IndexTerm) : TypingM Unit := do
  modifyState fun s => { s with paramValues := s.paramValues.insert stackSlotId valueTerm }

/-- Look up a parameter value by stack slot symbol ID.
    Returns the value term if this is a known parameter stack slot.
    Corresponds to: looking up in C_vars and finding Value(sym, bt)
    in cn/lib/compile.ml line 1305 -/
def lookupParamValue (stackSlotId : Nat) : TypingM (Option IndexTerm) := do
  let s ← getState
  return s.paramValues.get? stackSlotId

/-- Check if a symbol ID corresponds to a parameter stack slot -/
def isParamStackSlot (symId : Nat) : TypingM Bool := do
  let s ← getState
  return s.paramValues.contains symId

/-- Get the full parameter value map -/
def getParamValues : TypingM ParamValueMap := do
  let s ← getState
  return s.paramValues

/-! ### Store Value Tracking

These functions track what values are stored in stack slots.
Used for lazy muCore transformation of ccall argument slots.
In Core IR, ccall passes stack slot addresses; CN expects actual values.
-/

/-- Record a store: slot_sym_id → stored value.
    Called from handleStore when a value is written to a stack slot.
    Corresponds to: core_to_mucore tracking of ccall argument values -/
def recordStore (slotSymId : Nat) (value : IndexTerm) : TypingM Unit := do
  modifyState fun s => { s with storeValues := s.storeValues.insert slotSymId value }

/-- Look up the most recently stored value for a stack slot.
    Used by ccall argument resolution to map slot addresses to actual values.
    Corresponds to: core_to_mucore ccall argument transformation -/
def lookupStore (slotSymId : Nat) : TypingM (Option IndexTerm) := do
  let s ← getState
  return s.storeValues.get? slotSymId

/-! ### Scoped Operations

Corresponds to: pure in typing.ml lines 67-72
-/

/-- Run a computation without modifying most state (for speculative checking).
    The computation is executed and its result returned, but most state changes
    are discarded. Errors still propagate.

    IMPORTANT: Obligations AND conditional failures are PRESERVED even when
    state is restored. This is crucial for CPS-style checking where branches
    call the same continuation independently.

    Used for branch checking in CPS: each branch is checked speculatively
    with state restored afterward, but obligations from all branches accumulate.

    Corresponds to: pure in typing.ml lines 67-72 -/
def pure_ (m : TypingM α) : TypingM α := do
  let s ← getState
  let result ← m
  -- Preserve obligations and conditional failures, restore everything else
  let newState ← getState
  setState { s with
    obligations := newState.obligations
    conditionalFailures := newState.conditionalFailures
  }
  return result

/-- Run a computation in an isolated copy of the current state.
    Returns either the successful result with its FULL final state,
    or the error. The CALLER'S state is NOT modified — the caller must
    explicitly decide what to do with the returned state.

    This is critical for Eif handling: both branches are tried independently
    from the same starting state, and the caller merges/picks the right state.

    TypingM = StateT TypingState (Except TypeError), so m s gives us
    Except TypeError (α × TypingState) which we match on directly.

    Corresponds to: CN's pure + provable(false) pattern in check.ml:1985-2002 -/
def tryBranch (m : TypingM α) : TypingM (Except TypeError (α × TypingState)) := fun s =>
  match m s with
  | .ok (val, newState) =>
    .ok (.ok (val, newState), s)  -- Return result+state, caller's state unchanged
  | .error e =>
    .ok (.error e, s)  -- Return error, caller's state unchanged

/-- Add a conditional failure: a type error from a branch that may be dead.
    Creates an obligation to prove ¬branchCondition under the given assumptions.

    Post-hoc, the SMT solver checks: assumptions → ¬branchCondition.
    If valid (branch IS dead), the error is vacuous.
    If invalid (branch is live), the error is genuine and will be reported. -/
def addConditionalFailure (branchCond : IndexTerm) (err : TypeError)
    (assumptions : LCSet) (loc : Loc) : TypingM Unit :=
  modifyState fun s => { s with
    conditionalFailures := s.conditionalFailures ++ [{
      obligation := {
        description := s!"Branch must be dead (error: {err})"
        constraint := .t (AnnotTerm.mk (.unop .not branchCond) .bool branchCond.loc)
        assumptions := assumptions
        loc := loc
        category := .branchDead
      }
      originalError := err
    }]
  }

/-! ### Function Info Lookup -/

/-- Look up function info by symbol.
    Uses full Sym (digest + id) for HashMap lookup, avoiding collisions
    from different compilation units sharing the same numeric id.
    Used by cfunction(), params_length, etc. for concrete evaluation.
    Corresponds to: looking up function info in Core file -/
def lookupFunInfo (sym : Core.Sym) : TypingM (Option Core.FunInfo) := do
  let s ← getState
  return s.funInfoMap.get? sym

end TypingM

end CerbLean.CN.TypeChecking
