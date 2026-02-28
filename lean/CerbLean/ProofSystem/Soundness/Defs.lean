/-
  Soundness — Common Definitions

  Defines types and relations used across the soundness proof files.
  Placed here because `ctxModels` references both `Ctx` (from HasType)
  and `heapValueHasType` (from Models), which can't both be imported
  in Models.lean due to a cycle through SLProp.entails.

  Created: 2026-02-27
-/

import CerbLean.ProofSystem.HasType
import CerbLean.ProofSystem.Models

namespace CerbLean.ProofSystem

open CerbLean.CN.Semantics (Valuation HeapValue)

/-- The typing context is consistent with the valuation.
    Every variable in the context must be bound in the valuation to a
    value of the appropriate type. -/
def ctxModels (ρ : Valuation) (Γ : Ctx) : Prop :=
  ∀ s τ, Γ.lookupVar s = some τ →
    ∃ v, ρ.lookup s = some v ∧ heapValueHasType v τ

end CerbLean.ProofSystem
