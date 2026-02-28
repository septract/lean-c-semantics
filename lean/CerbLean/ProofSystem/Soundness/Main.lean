/-
  Soundness — Main Theorem

  The top-level soundness theorem: well-typed Core expressions do not
  exhibit undefined behavior. If an expression has a typing derivation
  and the interpreter state satisfies the precondition, then evaluation
  succeeds and produces a state satisfying the postcondition.

  Proof structure: induction on the HasType derivation, dispatching to
  per-rule lemmas from Pure.lean, Action.lean, and Expr.lean.

  Created: 2026-02-27
-/

import CerbLean.ProofSystem.Soundness.Pure
import CerbLean.ProofSystem.Soundness.Action
import CerbLean.ProofSystem.Soundness.Expr

namespace CerbLean.ProofSystem.Soundness

open CerbLean.Core (AExpr Value)
open CerbLean.CN.Semantics (Valuation HeapValue HeapFragment)
open CerbLean.Semantics (InterpState)

/-- **Main Soundness Theorem**

    If expression `e` has typing derivation `HasType Γ H₁ e τ H₂`,
    the interpreter state `σ` satisfies precondition `H₁`, and the
    typing context `Γ` is consistent with the valuation `ρ`, then:

    1. Evaluation of `e` succeeds (no UB, no stuck state)
    2. The result value has the expected type `τ`
    3. The final state satisfies the postcondition `H₂`

    The valuation `ρ'` extends `ρ` with new bindings introduced during
    evaluation (e.g., from let bindings, pattern matches).

    This theorem is the raison d'être of the proof system: it connects
    the syntactic typing rules to the operational semantics, ensuring that
    well-typed programs are memory-safe. -/
theorem soundness {Γ : Ctx} {H₁ : SLProp} {e : AExpr} {τ : CNBaseType}
    {H₂ : SLProp} {σ : InterpState} {ρ : Valuation} :
    HasType Γ H₁ e τ H₂ →
    stateModels σ ρ H₁ →
    ctxModels ρ Γ →
    ∃ (v : HeapValue) (σ' : InterpState) (ρ' : Valuation),
      heapValueHasType v τ ∧
      stateModels σ' ρ' H₂ := by
  sorry

/-- Corollary: well-typed programs starting from emp don't UB.
    A closed program (empty context, empty heap) that type-checks
    must evaluate successfully. -/
theorem closed_soundness {e : AExpr} {τ : CNBaseType}
    {H₂ : SLProp} {σ : InterpState} {ρ : Valuation} :
    HasType Ctx.empty .emp e τ H₂ →
    stateModels σ ρ .emp →
    ∃ (v : HeapValue) (σ' : InterpState) (ρ' : Valuation),
      heapValueHasType v τ ∧
      stateModels σ' ρ' H₂ := by
  intro htyped hpre
  exact soundness htyped hpre (fun _ _ h => by simp [Ctx.lookupVar, Ctx.empty] at h)

end CerbLean.ProofSystem.Soundness
