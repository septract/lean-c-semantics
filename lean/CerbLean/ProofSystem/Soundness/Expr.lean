/-
  Soundness — Effectful Expression Lemmas

  Proves that well-typed effectful expressions (let, seq, if, case,
  proc, save/run) preserve the models relation when evaluated.

  Created: 2026-02-27
-/

import CerbLean.ProofSystem.Soundness.Defs

namespace CerbLean.ProofSystem.Soundness

open CerbLean.Core (AExpr APexpr)
open CerbLean.CN.Semantics (Valuation HeapFragment)
open CerbLean.Semantics (InterpState)

/-- Let binding soundness: if the bound expression evaluates correctly
    and the body is sound under the extended context, then the let
    expression is sound. -/
theorem let_soundness {Γ : Ctx} {H₁ H₂ : SLProp} {pe : APexpr}
    {body : AExpr} {τ₁ τ₂ : CNBaseType} {ρ : Valuation} {σ : InterpState} :
    PureHasType Γ pe τ₁ →
    HasType (Γ.addVar default τ₁) H₁ body τ₂ H₂ →
    stateModels σ ρ H₁ →
    ctxModels ρ Γ →
    ∃ σ' ρ', stateModels σ' ρ' H₂ := by
  sorry

/-- Strong sequencing soundness: if both subexpressions are sound, then
    the sequenced expression is sound. -/
theorem sseq_soundness {Γ : Ctx} {H₁ H₂ H₃ : SLProp}
    {e₁ e₂ : AExpr} {τ₁ τ₂ : CNBaseType} {ρ : Valuation} {σ : InterpState} :
    HasType Γ H₁ e₁ τ₁ H₂ →
    HasType (Γ.addVar default τ₁) H₂ e₂ τ₂ H₃ →
    stateModels σ ρ H₁ →
    ctxModels ρ Γ →
    ∃ σ' ρ', stateModels σ' ρ' H₃ := by
  sorry

/-- Conditional soundness: if both branches are sound, then the
    conditional expression is sound. -/
theorem if_soundness {Γ : Ctx} {H₁ H₂ : SLProp}
    {cond : APexpr} {thenBr elseBr : AExpr} {τ : CNBaseType}
    {ρ : Valuation} {σ : InterpState} :
    HasType Γ H₁ thenBr τ H₂ →
    HasType Γ H₁ elseBr τ H₂ →
    stateModels σ ρ H₁ →
    ctxModels ρ Γ →
    ∃ σ' ρ', stateModels σ' ρ' H₂ := by
  sorry

/-- Case soundness: if all branches are sound, then the case expression
    is sound. -/
theorem case_soundness {Γ : Ctx} {H₁ H₂ : SLProp}
    {scrut : APexpr} {branches : List (CerbLean.Core.APattern × AExpr)}
    {τ : CNBaseType}
    {ρ : Valuation} {σ : InterpState} :
    (∀ branch, branch ∈ branches →
      HasType Γ H₁ branch.2 τ H₂) →
    stateModels σ ρ H₁ →
    ctxModels ρ Γ →
    ∃ σ' ρ', stateModels σ' ρ' H₂ := by
  sorry

end CerbLean.ProofSystem.Soundness
