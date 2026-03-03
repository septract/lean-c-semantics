/-
  Main Soundness Theorem Statements

  States the soundness of the separation-logic type system (HasType)
  with respect to the interpreter (runUntilDone): well-typed expressions
  are UB-free and partially correct.

  All theorem bodies are sorry'd — the goal is precise statements only.

  Created: 2026-03-02
-/

import CerbLean.ProofSystem.Soundness.Defs

namespace CerbLean.ProofSystem.Soundness

open CerbLean.Core (Sym Ctype Identifier AExpr APexpr Value MemValue File Loc)
open CerbLean.CN.Types (IndexTerm LogicalConstraint FunctionSpec Subst BaseType)
open CerbLean.CN.Semantics (HeapValue HeapFragment Valuation)
open CerbLean.Semantics (InterpM InterpState InterpEnv InterpError ThreadState
                          Stack runUntilDone collectAllLabeledContinuations
                          LabeledConts AllLabeledConts)
open CerbLean.Memory (TypeEnv MemState)
open CerbLean.ProofSystem (Ctx LabelInv SLProp HasType PureHasType
                            valueHasType heapValueHasType stateModels
                            MemValueFromValue)
open Std (HashMap)

/-! ## Main Soundness Theorem -/

/-- Main soundness theorem: well-typed expressions are UB-free and partially correct.

    **Safety**: for ANY amount of fuel, running the interpreter on a well-typed
    expression never produces undefined behavior.

    **Partial correctness**: if execution terminates (returns `.ok`), the result
    value has the claimed type and the final state satisfies the postcondition
    under some extension of the original valuation.

    Design notes:
    1. `∀ fuel` covers both safety and partial correctness. With fuel=0, we get
       `.error (.illformedProgram ...)` which satisfies `True`. With sufficient fuel,
       we get `.ok` and must satisfy the postcondition. Programs that diverge never
       reach `.ok`, so the postcondition is vacuously true for every finite fuel.

    2. `ValuationExtends ρ ρ'`: the post-valuation extends the pre-valuation.
       New bindings arise from `action_create` (fresh pointer symbol) and
       existentials in H₂. Without this, ρ' could be picked trivially.

    3. `StateCompatible` bundles env, heap, tag, path-condition, and label
       compatibility into one predicate (see Defs.lean).

    4. `FunSpecsCorrect` is the modular assumption: called functions satisfy
       their specs. This avoids needing whole-program typing derivations.

    5. `conts` is pinned to the file's actual labeled continuations via `hconts`,
       preventing unsound derivations with fabricated continuations. -/
theorem HasType.soundness
    {file : File} {typeEnv : TypeEnv} {interpState : InterpState}
    {env : List (HashMap Sym Value)} {currentProc : Option Sym}
    {conts : AllLabeledConts}
    {Γ : Ctx} {ρ : Valuation}
    {H₁ H₂ : SLProp} {e : AExpr} {τ : BaseType}
    (hty : HasType Γ H₁ e τ H₂)
    -- State compatibility: env, heap, tags, path conditions all match
    (hcompat : StateCompatible file typeEnv interpState env currentProc Γ ρ H₁)
    -- Called functions satisfy their specs (modular assumption)
    (hfunSpecs : FunSpecsCorrect file typeEnv Γ.funSpecs)
    -- Labeled continuations are pre-collected from the file
    (hconts : conts = collectAllLabeledContinuations file)
    : ∀ fuel : Nat,
      let ts : ThreadState := {
        arena := e
        stack := .cons currentProc [] .empty
        env := env
        currentProc := currentProc
      }
      match ((runUntilDone ts file conts fuel).run ⟨file, typeEnv⟩).run interpState with
      | .ok (v, st') =>
          valueHasType v τ ∧
          ∃ ρ', ValuationExtends ρ ρ' ∧ stateModels typeEnv st' ρ' H₂
      | .error (.undefinedBehavior _ _) => False
      | .error _ => True := by
  sorry

/-! ## Frame Soundness -/

/-- Frame soundness: if an expression is safe under H₁ and produces H₂,
    then running it under H₁ ∗ R is also safe and preserves R unchanged.

    This is implied by the main soundness theorem applied to `HasType.frame hty`,
    but stated separately to clarify the frame property and its proof obligations.
    The frame rule is the hardest structural rule to prove sound because it
    requires showing each memory operation has bounded footprint. -/
theorem HasType.frame_soundness
    {file : File} {typeEnv : TypeEnv} {interpState : InterpState}
    {env : List (HashMap Sym Value)} {currentProc : Option Sym}
    {conts : AllLabeledConts}
    {Γ : Ctx} {ρ : Valuation}
    {H₁ H₂ R : SLProp} {e : AExpr} {τ : BaseType}
    (hty : HasType Γ H₁ e τ H₂)
    (hcompat : StateCompatible file typeEnv interpState env currentProc Γ ρ (.star H₁ R))
    (hfunSpecs : FunSpecsCorrect file typeEnv Γ.funSpecs)
    (hconts : conts = collectAllLabeledContinuations file)
    : ∀ fuel : Nat,
      let ts : ThreadState := {
        arena := e
        stack := .cons currentProc [] .empty
        env := env
        currentProc := currentProc
      }
      match ((runUntilDone ts file conts fuel).run ⟨file, typeEnv⟩).run interpState with
      | .ok (v, st') =>
          valueHasType v τ ∧
          ∃ ρ', ValuationExtends ρ ρ' ∧ stateModels typeEnv st' ρ' (.star H₂ R)
      | .error (.undefinedBehavior _ _) => False
      | .error _ => True := by
  sorry

/-! ## MemValueFromValue Correctness -/

/-- The `MemValueFromValue` inductive relation (HasType.lean:880) characterizes
    the partial `memValueFromValue` function (Eval.lean:310).

    Since `memValueFromValue` is `partial`, it cannot appear directly in
    theorem statements. This theorem connects the specification relation
    to the actual implementation (proven by case analysis on the relation). -/
theorem memValueFromValue_correct
    {ct : Ctype} {v : Value} {mv : MemValue}
    (h : MemValueFromValue ct v mv)
    : CerbLean.Semantics.memValueFromValue ct v = some mv := by
  sorry

/-- The partial `memValueFromValue` function is total on well-typed values.
    If a value has type τ and the Ctype corresponds to τ, then conversion
    to a MemValue always succeeds.

    This is needed for the `action_store` rule: the typing premises guarantee
    the value is well-typed, so the interpreter's `memValueFromValue` call
    cannot fail. -/
theorem memValueFromValue_total_on_typed
    {ct : Ctype} {v : Value} {τ : BaseType}
    (hty : valueHasType v τ)
    (hct : CerbLean.ProofSystem.ctypeToBaseType ct = some τ)
    : ∃ mv, CerbLean.Semantics.memValueFromValue ct v = some mv := by
  sorry

end CerbLean.ProofSystem.Soundness
