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
import Std.Data.HashMap

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types

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
    Simplified: we omit sym_eqs, movable_indices, log for now -/
structure TypingState where
  /-- Current typing context -/
  context : Context
  /-- Proof oracle for constraint checking -/
  oracle : ProofOracle
  /-- Counter for generating fresh symbols -/
  freshCounter : Nat := 0
  /-- Parameter value mapping: stack slot ID → value term
      Corresponds to: C_vars state in cn/lib/compile.ml -/
  paramValues : ParamValueMap := {}
  deriving Inhabited

namespace TypingState

def empty (oracle : ProofOracle := .trivial) : TypingState :=
  { context := Context.empty, oracle := oracle, freshCounter := 0 }

def withContext (ctx : Context) (oracle : ProofOracle := .trivial) : TypingState :=
  { context := ctx, oracle := oracle, freshCounter := 0 }

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

/-- Run a computation without modifying the state (for speculative checking).
    The computation is executed and its result returned, but state changes
    are discarded. Errors still propagate.

    Used for branch checking in CPS: each branch is checked speculatively
    with state restored afterward.

    Corresponds to: pure in typing.ml lines 67-72 -/
def pure_ (m : TypingM α) : TypingM α := do
  let s ← getState
  let result ← m
  setState s
  return result

end TypingM

end CerbLean.CN.TypeChecking
