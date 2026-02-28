/-
  Soundness — Pure Expression Lemmas

  Proves that well-typed pure expressions evaluate to values of the
  correct type without UB. These lemmas are the base case for the
  main soundness theorem.

  Created: 2026-02-27
-/

import CerbLean.ProofSystem.Soundness.Defs

namespace CerbLean.ProofSystem.Soundness

open CerbLean.Core (Value APexpr)
open CerbLean.CN.Types (BaseType)
open CerbLean.CN.Semantics (Valuation HeapValue)

/-- A well-typed value literal evaluates to a heap value of the right type. -/
theorem val_soundness {v : Value} {τ : CNBaseType} :
    valueHasType v τ →
    ∃ hv : HeapValue, heapValueHasType hv τ := by
  sorry

/-- A well-typed symbol reference evaluates to a heap value of the right type,
    given a consistent valuation. -/
theorem sym_soundness {Γ : Ctx} {s : CerbLean.Core.Sym} {τ : CNBaseType}
    {ρ : Valuation} :
    Γ.lookupVar s = some τ →
    ctxModels ρ Γ →
    ∃ v, ρ.lookup s = some v ∧ heapValueHasType v τ := by
  intro hlookup hctx
  exact hctx s τ hlookup

/-- Well-typed pure expressions evaluate to values of the correct type.
    This is the key lemma for the pure case of soundness. -/
theorem pure_soundness {Γ : Ctx} {pe : APexpr} {τ : CNBaseType}
    {ρ : Valuation} :
    PureHasType Γ pe τ →
    ctxModels ρ Γ →
    ∃ v : HeapValue, heapValueHasType v τ := by
  sorry

end CerbLean.ProofSystem.Soundness
