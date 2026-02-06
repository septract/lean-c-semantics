/-
  CN Typing Monad
  Corresponds to: cn/lib/typing.ml

  The typing monad is a state monad that tracks:
  - The typing context (variables, resources, constraints)
  - A proof oracle for checking constraints

  Key design decision: We abstract constraint proving via ProofOracle.
  This allows:
  - Testing with a trivial oracle that accepts everything
  - Using SMT solvers (e.g., LeanSMT)
  - Manual Lean proofs
  - Mixing strategies

  Audited: 2026-01-20 against cn/lib/typing.ml
-/

import CerbLean.CN.TypeChecking.Context
import CerbLean.CN.Types
import CerbLean.CN.Verification.Obligation
import CerbLean.Core.MuCore
import Std.Data.HashMap

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc)
open CerbLean.Core.MuCore (LabelDefs LabelDef LabelInfo)
open CerbLean.CN.Types
open CerbLean.CN.Verification

/-! ## Proof Oracle

The proof oracle abstracts constraint solving. Different implementations:
- Trivial: accepts all constraints (for testing)
- Decide: uses decidable instances
- SMT: external solver
- Manual: requires Lean proofs
-/

/-- Result of a provability check -/
inductive ProvableResult where
  /-- Constraint is provable -/
  | true_
  /-- Constraint is not provable (with optional counterexample info) -/
  | false_ (info : Option String := none)
  deriving Repr, Inhabited

/-- A proof oracle can attempt to prove constraints.
    Corresponds to: Solver.provable in cn/lib/solver.ml

    The oracle is called with:
    - Current constraints (assumptions)
    - Constraint to prove
    Returns whether the constraint is provable. -/
structure ProofOracle where
  /-- Try to prove a constraint given current assumptions -/
  tryProve : LCSet → LogicalConstraint → ProvableResult
  /-- Name for debugging -/
  name : String := "unnamed"

namespace ProofOracle

/-- Trivial oracle that accepts all constraints.
    Use for testing and development. -/
def trivial : ProofOracle where
  tryProve _ _ := .true_
  name := "trivial"

/-- Oracle that rejects all constraints.
    Useful for testing that we generate the right constraints. -/
def reject : ProofOracle where
  tryProve _ _ := .false_
  name := "reject"

/-- Combine oracles: try first, fall back to second -/
def orElse (o1 : ProofOracle) (o2 : Unit → ProofOracle) : ProofOracle where
  tryProve assumptions lc :=
    match o1.tryProve assumptions lc with
    | .true_ => .true_
    | .false_ _ => (o2 ()).tryProve assumptions lc
  name := s!"{o1.name} || {(o2 ()).name}"

instance : OrElse ProofOracle := ⟨orElse⟩

instance : Inhabited ProofOracle := ⟨trivial⟩

end ProofOracle

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

/-! ## Parameter Value Mapping

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

    Extended for proof obligations: accumulates obligations during type checking
    instead of (or in addition to) checking constraints immediately. -/
structure TypingState where
  /-- Current typing context -/
  context : Context
  /-- Proof oracle for constraint checking (for backward compatibility) -/
  oracle : ProofOracle
  /-- Counter for generating fresh symbols -/
  freshCounter : Nat := 0
  /-- Parameter value mapping: stack slot ID → value term
      Corresponds to: C_vars state in cn/lib/compile.ml -/
  paramValues : ParamValueMap := {}
  /-- Label definitions from muCore transformation.
      Maps label symbols to their definitions (return vs regular).
      Corresponds to: mi_label_defs in milicore.ml -/
  labelDefs : LabelDefs := []
  /-- Accumulated proof obligations (new: for post-hoc discharge) -/
  obligations : ObligationSet := []
  /-- Whether to accumulate obligations instead of checking immediately -/
  accumulateObligations : Bool := false
  /-- Whether this execution path has returned.
      When true, subsequent code should be skipped (return is terminal). -/
  hasReturned : Bool := false
  deriving Inhabited

namespace TypingState

def empty (oracle : ProofOracle := .trivial) : TypingState :=
  { context := Context.empty, oracle := oracle, freshCounter := 0 }

def withContext (ctx : Context) (oracle : ProofOracle := .trivial) : TypingState :=
  { context := ctx, oracle := oracle, freshCounter := 0 }

/-- Create state for obligation accumulation (no oracle checking) -/
def forObligations : TypingState :=
  { context := Context.empty
  , oracle := .trivial  -- Not used when accumulating
  , freshCounter := 0
  , accumulateObligations := true }

/-- Create state for obligation accumulation with initial context -/
def forObligationsWithContext (ctx : Context) : TypingState :=
  { context := ctx
  , oracle := .trivial
  , freshCounter := 0
  , accumulateObligations := true }

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

/-! ### Provability

Corresponds to: make_provable in typing.ml lines 122-133
-/

/-- Check if a constraint is provable given current assumptions
    Corresponds to: provable in typing.ml -/
def provable (lc : LogicalConstraint) : TypingM ProvableResult := do
  let s ← getState
  let ctx ← getContext
  return s.oracle.tryProve ctx.constraints lc

/-- Check if a constraint is provable, failing if not
    Corresponds to: pattern matching on provable result in resourceInference.ml -/
def ensureProvable (lc : LogicalConstraint) : TypingM Unit := do
  match ← provable lc with
  | .true_ => pure ()
  | .false_ _ =>
    let ctx ← getContext
    fail (.unprovableConstraint lc ctx)

/-! ### Proof Obligation Operations

These functions support the new proof obligation architecture where
constraints are accumulated during type checking and discharged afterward.
-/

/-- Get accumulated obligations -/
def getObligations : TypingM ObligationSet := do
  let s ← getState
  return s.obligations

/-- Add a proof obligation -/
def addObligation (ob : Obligation) : TypingM Unit := do
  modifyState fun s => { s with obligations := ObligationSet.add ob s.obligations }

/-- Add a constraint as a proof obligation.
    If accumulateObligations is true, adds to the obligation set.
    Otherwise, checks immediately with the oracle (legacy behavior).

    When accumulating, the obligation captures the current constraints as
    assumptions. This is crucial: the obligation semantically means
    "under the current assumptions, the constraint holds". -/
def requireConstraint (lc : LogicalConstraint) (loc : Loc) (desc : String := "constraint") : TypingM Unit := do
  let s ← getState
  if s.accumulateObligations then
    -- New behavior: accumulate obligation for post-hoc discharge
    -- Capture current constraints as assumptions
    let assumptions ← getConstraints
    let ob := Obligation.arithmetic desc lc assumptions loc
    addObligation ob
  else
    -- Legacy behavior: check immediately
    ensureProvable lc

/-- Add multiple constraints as obligations.
    All obligations capture the same assumptions (current constraints). -/
def requireConstraints (lcs : LCSet) (loc : Loc) : TypingM Unit := do
  for lc in lcs do
    requireConstraint lc loc

/-- Check if we're in obligation accumulation mode -/
def isAccumulatingObligations : TypingM Bool := do
  let s ← getState
  return s.accumulateObligations

/-- Enable obligation accumulation mode -/
def enableObligationAccumulation : TypingM Unit := do
  modifyState fun s => { s with accumulateObligations := true }

/-- Disable obligation accumulation mode (use oracle instead) -/
def disableObligationAccumulation : TypingM Unit := do
  modifyState fun s => { s with accumulateObligations := false }

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

/-! ### Scoped Operations

Corresponds to: pure in typing.ml lines 67-72
-/

/-- Run a computation without modifying most state (for speculative checking).
    The computation is executed and its result returned, but most state changes
    are discarded. Errors still propagate.

    IMPORTANT: Obligations are PRESERVED even when state is restored.
    This is crucial for CPS-style checking where branches call the same
    continuation independently. Each branch may generate obligations that
    must all be checked.

    Used for branch checking in CPS: each branch is checked speculatively
    with state restored afterward, but obligations from all branches accumulate.

    Corresponds to: pure in typing.ml lines 67-72 -/
def pure_ (m : TypingM α) : TypingM α := do
  let s ← getState
  let result ← m
  -- Preserve obligations from the branch, restore everything else
  let newObligations ← getObligations
  setState { s with obligations := newObligations }
  return result

end TypingM

end CerbLean.CN.TypeChecking
