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
import CerbLean.CN.TypeChecking.Simplify
import CerbLean.CN.TypeChecking.DerivedConstraints
import CerbLean.CN.Types
import CerbLean.CN.Verification.Obligation
import CerbLean.CN.Verification.SmtLib
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
    Simplified: we omit movable_indices, log for now

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
  /-- Symbol equality map: tracks sym = value bindings extracted from constraints.
      Corresponds to: sym_eqs in typing.ml:14.
      CN uses this for term simplification (make_simp_ctxt, typing.ml:112-114).
      Used to build SimCtxt for simplification: when the simplifier encounters
      a symbol, it substitutes the known value from this map. -/
  symEqs : Std.HashMap Nat IndexTerm := {}
  /-- Accumulated proof obligations for post-hoc SMT discharge -/
  obligations : ObligationSet := []
  /-- Conditional failures: type errors from branches that may be dead.
      Each pairs an obligation (prove branch is dead) with the original error.
      Discharged post-hoc by SMT. -/
  conditionalFailures : List ConditionalFailure := []
  /-- Whether this execution path has returned.
      When true, subsequent code should be skipped (return is terminal). -/
  hasReturned : Bool := false
  /-- Inline SMT solver I/O handles, if initialized.
      Used for inline provable/assume queries during type checking (H5).
      Stores just stdin/stdout handles (process lifecycle managed by caller).
      Corresponds to: solver : solver option in typing.ml:13 -/
  solverStdin : Option IO.FS.Handle := none
  solverStdout : Option IO.FS.Handle := none
  deriving Inhabited

namespace TypingState

def empty (freshCounter : Nat := 0) : TypingState :=
  { context := Context.empty, freshCounter := freshCounter }

def withContext (ctx : Context) (freshCounter : Nat := 0) : TypingState :=
  { context := ctx, freshCounter := freshCounter }

end TypingState

/-! ## Typing Monad

Corresponds to: cn/lib/typing.ml lines 28-30
```ocaml
type 'a t = s -> ('a * s, TypeErrors.t) Result.t
```
-/

/-- The typing monad: state + error + IO.
    IO capability is needed for the inline SMT solver process (H5).
    Corresponds to: 'a t in typing.ml line 30 -/
abbrev TypingM (α : Type) := StateT TypingState (ExceptT TypeError IO) α

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
def run (m : TypingM α) (s : TypingState) : IO (Except TypeError (α × TypingState)) :=
  ExceptT.run (StateT.run m s)

/-- Run the typing monad, discarding final state -/
def run' (m : TypingM α) (s : TypingState) : IO (Except TypeError α) :=
  ExceptT.run (StateT.run' m s)

/-! ### Inline SMT Solver Operations

These provide raw access to the inline solver process for push/pop,
declare, assume, and provable queries. The inline solver is UNTRUSTED —
it guides type checking decisions (branch pruning, resource matching)
but every decision is backed by a post-hoc proof obligation.

Corresponds to: solver operations in cn/lib/typing.ml:383-412 and
solver.ml:1367-1404
-/

/-- Write a raw SMT-LIB2 string to the inline solver's stdin.
    No-op if no solver is active. -/
def solverWrite (s : String) : TypingM Unit := do
  let st ← getState
  match st.solverStdin with
  | none => pure ()
  | some handle =>
    (handle.putStr s : IO Unit)
    (handle.flush : IO Unit)

/-- Read a single line response from the inline solver's stdout.
    Returns the trimmed response string.
    Throws if no solver is active. -/
def readSolverResponse : TypingM String := do
  let st ← getState
  match st.solverStdout with
  | none => throw (.other "readSolverResponse: no solver process")
  | some handle =>
    let line ← (handle.getLine : IO String)
    return line.trim

/-- Push a solver scope level.
    Corresponds to: Solver.push in solver.ml -/
def solverPush : TypingM Unit := solverWrite "(push 1)\n"

/-- Pop a solver scope level.
    Corresponds to: Solver.pop in solver.ml -/
def solverPop : TypingM Unit := solverWrite "(pop 1)\n"

/-- Declare a variable to the inline solver.
    Writes `(declare-const name sort)` for the given symbol and base type.
    No-op if no solver is active or if the type is unsupported.
    Corresponds to: variable declarations in init_solver (typing.ml:383-396) -/
def solverDeclare (s : Sym) (bt : BaseType) : TypingM Unit := do
  let st ← getState
  if st.solverStdin.isNone then return
  let name := SmtLib.symToSmtName s
  match SmtLib.baseTypeToSort bt with
  | .ok sort => solverWrite s!"(declare-const {name} {sort})\n"
  | .unsupported _ => pure ()  -- Skip unsupported types silently

/-- Assume a logical constraint to the inline solver.
    Translates the constraint to SMT-LIB2 and writes `(assert term)`.
    No-op if no solver is active.
    Quantified (Forall) constraints are SKIPPED, matching CN's Solver.assume
    (solver.ml:1352) which ignores `Forall` variants.
    Corresponds to: Solver.assume in typing.ml:407 -/
def solverAssume (lc : LogicalConstraint) : TypingM Unit := do
  let st ← getState
  if st.solverStdin.isNone then return
  match lc with
  | .forall_ _ _ => pure ()  -- CN's Solver.assume skips Forall constraints
  | .t _ =>
    match SmtLib.constraintToSmtTerm none lc with
    | .ok term => solverWrite s!"(assert {term})\n"
    | .unsupported _ => pure ()  -- Untranslatable: solver gets incomplete info (conservative)

/-- Result of a provability query.
    Corresponds to: the three-valued result from SMT check-sat -/
inductive Provable where
  | proved     -- Constraint is provable (¬φ is unsat)
  | refuted    -- Constraint is refutable (¬φ is sat)
  | unknown    -- Solver couldn't determine (timeout, no solver, unsupported)
  deriving Inhabited, BEq

/-- Check if a constraint is provable under current assumptions.
    Protocol: push → assert(¬φ) → check-sat → pop.
    Returns `.proved` if ¬φ is unsatisfiable (i.e., φ follows from assumptions).

    Quick syntactic checks are done first for trivial cases.

    If no solver is active, returns `.unknown` (conservative).

    Corresponds to: Solver.provable in solver.ml:1367-1404 -/
def provable (lc : LogicalConstraint) : TypingM Provable := do
  -- Build simplification context from typing state
  -- CN ref: make_simp_ctxt (typing.ml:112-114) builds from sym_eqs + memory model
  let st ← getState
  let simpCtxt : Simplify.SimCtxt := {
    symEqs := st.symEqs
    typeEnv := some (CerbLean.Memory.TypeEnv.mk st.tagDefs)
  }
  -- Simplify constraint before checking (CN does this in solver.ml via simplify)
  -- CN ref: solver.ml:1375-1376 (simplify before provable query)
  let lc := Simplify.simplifyConstraint simpCtxt lc
  -- Quick syntactic checks (CN does these too)
  match lc with
  | .t t =>
    match t.term with
    | .const (.bool true) => return .proved
    | .const (.bool false) => return .refuted
    | _ => pure ()
  | _ => pure ()
  -- Check if solver is available
  let st ← getState
  if st.solverStdin.isNone then return .unknown
  -- Translate constraint to SMT
  match SmtLib.constraintToSmtTerm none lc with
  | .unsupported _ => return .unknown
  | .ok term =>
    -- SMT query: push → assert(¬φ) → check-sat → pop
    solverPush
    solverWrite s!"(assert (not {term}))\n"
    solverWrite "(check-sat)\n"
    let response ← readSolverResponse
    solverPop
    match response with
    | "unsat"   => return .proved    -- ¬φ unsatisfiable ⟹ φ is provable
    | "sat"     => return .refuted   -- ¬φ satisfiable ⟹ φ is not provable
    | _         => return .unknown   -- timeout, unknown, or unexpected

/-! ### Context Operations

These mirror the operations in cn/lib/typing.ml lines 141-178
-/

/-- Add a computational variable.
    Declares the variable to the inline solver.
    Corresponds to: add_a in typing.ml -/
def addA (s : Sym) (bt : BaseType) (loc : Loc) (desc : String) : TypingM Unit := do
  modifyContext (Context.addA s bt ⟨loc, desc⟩)
  solverDeclare s bt

/-- Add a computational variable with a value.
    Declares the variable and assumes its equality to the inline solver.
    Corresponds to: add_a_value in typing.ml -/
def addAValue (s : Sym) (v : IndexTerm) (loc : Loc) (desc : String) : TypingM Unit := do
  modifyContext (Context.addAValue s v ⟨loc, desc⟩)
  solverDeclare s v.bt
  -- Assume sym = value to solver so it can use this binding
  let symTerm := AnnotTerm.mk (.sym s) v.bt loc
  let eqTerm := AnnotTerm.mk (.binop .eq symTerm v) .bool loc
  solverAssume (.t eqTerm)

/-- Add a logical variable.
    Declares the variable to the inline solver.
    Corresponds to: add_l in typing.ml -/
def addL (s : Sym) (bt : BaseType) (loc : Loc) (desc : String) : TypingM Unit := do
  modifyContext (Context.addL s bt ⟨loc, desc⟩)
  solverDeclare s bt

/-- Add a logical variable with a value.
    Corresponds to: add_l_value in typing.ml:349-354.
    Records sym = value in symEqs (CN's add_sym_eqs, typing.ml:352-354),
    declares variable and assumes equality to the inline solver,
    and adds equality constraint so it's available as an SMT assumption. -/
def addLValue (s : Sym) (v : IndexTerm) (loc : Loc) (desc : String) : TypingM Unit := do
  modifyContext (Context.addLValue s v ⟨loc, desc⟩)
  solverDeclare s v.bt
  -- CN typing.ml:352-354: add_sym_eqs [(sym, value)]
  modifyState fun st => { st with symEqs := st.symEqs.insert s.id v }
  -- Add equality constraint so SMT solver knows sym = value.
  -- CN achieves this via term substitution in make_simp_ctxt (typing.ml:112-114);
  -- we also add an explicit context constraint for the SMT solver obligation encoding.
  -- Uses modifyContext directly (not TypingM.addC) to avoid redundant symEqs insertion.
  let symTerm := AnnotTerm.mk (.sym s) v.bt loc
  let eqTerm := AnnotTerm.mk (.binop .eq symTerm v) .bool loc
  modifyContext (Context.addC (.t eqTerm))
  solverAssume (.t eqTerm)

/-- Extract symbol equality from constraint if it's of form `sym == expr`.
    Corresponds to: LC.is_sym_lhs_equality in logicalConstraints.ml:61-67 -/
def isSymLhsEquality (lc : LogicalConstraint) : Option (Sym × IndexTerm) :=
  match lc with
  | .t t =>
    match t.term with
    | .binop .eq lhs rhs =>
      match lhs.term with
      | .sym s => some (s, rhs)
      | _ => none
    | _ => none
  | _ => none

/-- Add a constraint.
    Corresponds to: add_c in typing.ml:403-412.
    Adds the constraint to context, assumes it to the inline solver,
    and extracts symbol equalities (CN's add_sym_eqs, typing.ml:410). -/
def addC (lc : LogicalConstraint) : TypingM Unit := do
  modifyContext (Context.addC lc)
  -- CN typing.ml:407: Solver.assume solver lc
  solverAssume lc
  -- CN typing.ml:410: add_sym_eqs (List.filter_map LC.is_sym_lhs_equality [lc])
  -- If the constraint is of form `sym == expr`, record sym = expr in symEqs map.
  -- CN uses sym_eqs for term simplification (make_simp_ctxt, typing.ml:112-114).
  match isSymLhsEquality lc with
  | some (s, v) =>
    modifyState fun st => { st with symEqs := st.symEqs.insert s.id v }
  | none => pure ()

/-- Look up a tag definition from the state.
    Corresponds to: Sym.Map.find tag global.struct_decls -/
def lookupTag (tag : Sym) : TypingM (Option TagDef) := do
  let s ← getState
  return s.tagDefs.find? (·.1 == tag) |>.map (·.2.2)

/-- Add a resource with derived constraints (pointer_facts).
    Corresponds to: add_r in typing.ml + pointer_facts in resource.ml:67-71.
    When a resource is added, CN derives logical constraints:
    - Single-resource: hasAllocId, address range no-overflow
    - Pairwise: non-overlap with all existing Owned resources (SEPARATION)
    Audited: 2026-02-18 -/
def addR (r : Resource) : TypingM Unit := do
  let ctx ← getContext
  let existingResources := ctx.resources
  modifyContext (Context.addR r)
  -- Derive and add pointer_facts constraints
  -- CN ref: typing.ml:415-427 (add_r calls pointer_facts then add_cs)
  let derivedLcs := DerivedConstraints.deriveConstraints r existingResources
  for lc in derivedLcs do
    addC lc

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
    If the entry is an alias (symbolic reference to another param slot),
    follows the reference to get the current value. This handles the case
    where a param value is updated (e.g., via `++i`) but alias entries
    in the map still hold stale copies of the original symbolic reference.
    Corresponds to: looking up in C_vars and finding Value(sym, bt)
    in cn/lib/compile.ml line 1305 -/
def lookupParamValue (stackSlotId : Nat) : TypingM (Option IndexTerm) := do
  let s ← getState
  match s.paramValues.get? stackSlotId with
  | some v =>
    -- If the value is a symbolic reference to a different param slot,
    -- follow the reference to get the potentially-updated value.
    -- This handles alias entries that weren't updated when the primary was.
    match v.term with
    | .sym refSym =>
      if refSym.id != stackSlotId then
        match s.paramValues.get? refSym.id with
        | some primaryVal => return some primaryVal
        | none => return some v
      else return some v
    | _ => return some v
  | none => return none

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

    The inline solver state is scoped with push/pop so that constraints
    assumed during the computation are undone when it completes.

    Corresponds to: pure in typing.ml lines 67-72 -/
def pure_ (m : TypingM α) : TypingM α := do
  let s ← getState
  solverPush
  -- Run m, ensuring solverPop runs even on error
  let innerResult ← (ExceptT.run (StateT.run m s) : IO _)
  match innerResult with
  | .error e =>
    solverPop
    -- CN's `pure` (typing.ml:67-72) returns Error directly without restoring state.
    -- The throw discards the state, so setState would be dead code here.
    throw e
  | .ok (result, newState) =>
    solverPop
    -- Preserve obligations and conditional failures, restore everything else
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

    The inline solver state is scoped with push/pop so that constraints
    assumed during the computation are undone when it completes.

    Corresponds to: CN's pure + provable(false) pattern in check.ml:1985-2002 -/
def tryBranch (m : TypingM α) : TypingM (Except TypeError (α × TypingState)) := do
  let s ← getState
  solverPush
  -- Run m and capture the result as data (errors become .error values, not propagated)
  let result ← (ExceptT.run (StateT.run m s) : IO _)
  solverPop
  setState s  -- Restore caller's state unchanged
  return result

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
