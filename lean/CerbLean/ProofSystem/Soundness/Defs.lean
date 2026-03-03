/-
  Soundness Theorem Definitions

  Correspondence relations between the separation-logic type system
  (HasType) and the interpreter (runUntilDone). These definitions
  bridge the proof system's abstract world (Ctx, Valuation, SLProp)
  with the interpreter's concrete world (ThreadState, InterpState, env).

  Created: 2026-03-02
-/

import CerbLean.ProofSystem.HasType
import CerbLean.Semantics.Step
import Std.Data.HashMap

namespace CerbLean.ProofSystem.Soundness

open CerbLean.Core (Sym Ctype Identifier AExpr APexpr Pexpr Value MemValue
                     IntegerType File FunDecl PointerValue Loc)
open CerbLean.CN.Types (IndexTerm LogicalConstraint FunctionSpec Precondition
                         Postcondition Init QPredicate Subst BaseType AnnotTerm Term)
open CerbLean.CN.Semantics (HeapValue HeapFragment Valuation Location)
open CerbLean.Semantics (InterpM InterpState InterpEnv InterpError ThreadState
                          Stack StepResult LabeledCont LabeledConts AllLabeledConts
                          runUntilDone step callProc collectAllLabeledContinuations)
open CerbLean.Memory (TypeEnv MemState)
open CerbLean.ProofSystem (Ctx LabelInv SLProp HasType PureHasType
                            valueHasType heapValueHasType evalIndexTerm
                            evalConstraint stateModels models heapFragmentOf
                            envValuationCompat pexprEnvLookup)
open Std (HashMap)

/-! ## Environment Correspondence -/

/-- Look up a symbol in the interpreter's scoped environment
    (list of HashMaps, innermost scope first).
    Standalone version of `ThreadState.lookupSym` (State.lean:385)
    for use in theorem statements without depending on ThreadState. -/
def envLookup (env : List (HashMap Sym Value)) (s : Sym) : Option Value :=
  env.findSome? (fun hm => hm[s]?)

/-- Flatten the scoped env (list of HashMaps) to a flat assoc list.
    Inner scopes come first in the list, matching `envLookup`'s
    search order. Used with `envValuationCompat` and `pexprEnvLookup`. -/
def flattenEnv (env : List (HashMap Sym Value)) : List (Sym × Value) :=
  env.flatMap (fun hm => hm.toList)

/-- Relates the interpreter's scoped environment to `Ctx.vars` and
    the logical `Valuation`. For every typed variable in the context,
    the env has a value with the right type, and the valuation has a
    corresponding heap value that is type-compatible.

    This is strictly stronger than `envValuationCompat` because it also
    requires `Ctx.vars` membership and `valueHasType`. -/
def EnvCompat (env : List (HashMap Sym Value)) (vars : List (Sym × BaseType))
    (ρ : Valuation) : Prop :=
  ∀ s τ, (s, τ) ∈ vars →
    ∃ v, envLookup env s = some v ∧ valueHasType v τ ∧
    ∃ hv, ρ.lookup s = some hv ∧
      (∀ τ', valueHasType v τ' → heapValueHasType hv τ')

/-! ## Context Conditions -/

/-- All path conditions in the context are satisfied under the valuation. -/
def PathCondsHold (ρ : Valuation) (pathConds : List LogicalConstraint) : Prop :=
  ∀ c, c ∈ pathConds → evalConstraint ρ c

/-- Tag definitions in the context match those in the file and type environment.
    Ensures sizeof/alignof queries will succeed for all tags the type system
    knows about.

    `File.tagDefs` is `List (Sym × (Loc × TagDef))`.
    `Ctx.tagDefs` is `List (Sym × List (Identifier × Ctype))`.
    `TypeEnv.lookupTag` checks `typeEnv.tagDefs`. -/
def TagDefsCompat (Γ : Ctx) (file : File) (typeEnv : TypeEnv) : Prop :=
  ∀ tag fields, Γ.lookupTagDef tag = some fields →
    -- Tag exists in the file's tagDefs
    (∃ locAndDef, file.tagDefs.find? (fun (s, _) => s == tag) = some (tag, locAndDef)) ∧
    -- Tag exists in TypeEnv (for sizeof/alignof)
    typeEnv.lookupTag tag ≠ none

/-- Label invariants in the typing context correspond to actual labeled
    continuations pre-collected from the file.

    Structural check only (parameter count). The semantic correspondence
    — that the continuation body type-checks under the invariant — is
    established by the HasType.save rule itself. -/
def LabelInvsConsistent (labelInvs : List (Sym × LabelInv))
    (allConts : AllLabeledConts) (currentProc : Option Sym) : Prop :=
  ∀ label inv, (label, inv) ∈ labelInvs →
    ∃ procSym, currentProc = some procSym ∧
    ∃ procConts, allConts[procSym]? = some procConts ∧
    ∃ lc, procConts[label]? = some lc ∧
      lc.params.length = inv.params.length

/-! ## Valuation Extension -/

/-- Helper: ρ' agrees with ρ on all existing bindings. -/
def ValuationExtends (ρ ρ' : Valuation) : Prop :=
  ∀ s hv, ρ.lookup s = some hv → ρ'.lookup s = some hv

/-! ## Error Classification -/

/-- Helper predicate: the result is not undefined behavior.
    `ok` results must satisfy further properties (stated by the caller);
    non-UB errors (type error, fuel exhaustion, etc.) are acceptable. -/
def NotUB (result : Except InterpError α) : Prop :=
  match result with
  | .ok _ => True
  | .error (.undefinedBehavior _ _) => False
  | .error _ => True

/-! ## Procedure Call Helper -/

/-- Run a procedure call: look up the function, set up ThreadState, run.
    Matches the interpreter's procedure call flow in Step.lean:76-96.
    Takes callerEnv to match the real interpreter's scope structure. -/
def runProcCall (file : File) (_typeEnv : TypeEnv) (s : Sym)
    (argVals : List Value) (callerEnv : List (HashMap Sym Value))
    (fuel : Nat) : InterpM Value := do
  match callProc file s argVals with
  | .ok (resolvedSym, procEnv, body) =>
    let allConts := collectAllLabeledContinuations file
    let st : ThreadState := {
      arena := body
      stack := .cons (some resolvedSym) [] .empty
      env := procEnv :: callerEnv
      currentProc := some resolvedSym
    }
    runUntilDone st file allConts fuel
  | .error err => throw err

/-! ## Function Specification Correctness -/

/-- Semantic assumption: all function specs in the context correctly
    describe function behavior. This is the key modularity mechanism
    — we assume called functions satisfy their specs, rather than
    requiring their full typing derivations.

    For any function s with spec, calling s with arguments satisfying
    the precondition is UB-free and establishes the postcondition. -/
def FunSpecsCorrect (file : File) (typeEnv : TypeEnv)
    (funSpecs : List (Sym × FunctionSpec)) : Prop :=
  ∀ s spec, (s, spec) ∈ funSpecs →
    -- Function exists in the file
    (∃ fd, file.funs.find? (fun (sym, _) => sym == s) = some (s, fd) ∨
           file.stdlib.find? (fun (sym, _) => sym == s) = some (s, fd)) ∧
    -- For any state satisfying the precondition, calling the function is safe
    -- and establishes the postcondition
    ∀ (interpState : InterpState) (ρ : Valuation)
      (argVals : List Value) (argTerms : List IndexTerm) (σ : Subst),
      argVals.length = spec.params.length →
      argTerms.length = argVals.length →
      σ = Subst.fromMapping
        (spec.params.zip argTerms |>.map fun ((sym, _), term) => (sym.id, term)) →
      -- Each arg value has the spec's param type
      (∀ i (hv : i < argVals.length) (hp : i < spec.params.length),
        valueHasType argVals[i] (spec.params[i]'hp).2) →
      -- Precondition holds
      stateModels typeEnv interpState ρ (SLProp.ofPrecondition (spec.requires.substTotal σ)) →
      -- Then for any fuel and caller env, calling the function is safe
      ∀ (callerEnv : List (HashMap Sym Value)) (fuel : Nat),
        let result := ((runProcCall file typeEnv s argVals callerEnv fuel).run
                        ⟨file, typeEnv⟩).run interpState
        -- UB-free
        NotUB result ∧
        -- Partial correctness: if it terminates, postcondition holds
        (∀ v st', result = .ok (v, st') →
          valueHasType v spec.returnType ∧
          ∃ ρ', ValuationExtends ρ ρ' ∧
                stateModels typeEnv st' ρ' (SLProp.ofPostcondition (spec.ensures.substTotal σ)))

/-! ## State Compatibility Bundle -/

/-- Bundles all compatibility conditions between the proof system and
    interpreter into a single structure. This is the invariant that
    must hold at each step of the soundness proof. -/
structure StateCompatible (file : File) (typeEnv : TypeEnv) (interpState : InterpState)
    (env : List (HashMap Sym Value)) (currentProc : Option Sym)
    (Γ : Ctx) (ρ : Valuation) (H : SLProp) : Prop where
  /-- Variable bindings in env match context types and valuation -/
  envCompat : EnvCompat env Γ.vars ρ
  /-- All path conditions hold under the valuation -/
  pathConds : PathCondsHold ρ Γ.pathConds
  /-- The heap satisfies the SLProp under the valuation -/
  heapModels : stateModels typeEnv interpState ρ H
  /-- Tag definitions in context match file and type env -/
  tagDefs : TagDefsCompat Γ file typeEnv
  /-- Label invariants in context match actual continuations -/
  labelInvs : LabelInvsConsistent Γ.labelInvs
                (collectAllLabeledContinuations file) currentProc

end CerbLean.ProofSystem.Soundness
