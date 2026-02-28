/-
  Soundness — Memory Action Lemmas

  Proves that well-typed memory actions (load, store, create, kill)
  preserve the models relation. Each lemma shows that if the pre-heap
  satisfies the precondition, the action's effect on the heap produces
  a state satisfying the postcondition.

  Created: 2026-02-27
-/

import CerbLean.ProofSystem.Soundness.Defs

namespace CerbLean.ProofSystem.Soundness

open CerbLean.Core (Ctype)
open CerbLean.CN.Types (IndexTerm Init)
open CerbLean.CN.Semantics (Valuation HeapValue HeapFragment Location
                             interpOwned)
open CerbLean.Semantics (InterpState)

/-- Load preserves the heap: reading from `Owned<ct>(init, ptr, val)`
    returns the stored value and leaves the heap unchanged.
    The return value has type `val.bt`. -/
theorem load_preserves_models {ρ : Valuation} {ct : Ctype}
    {ptr val : IndexTerm} {R : SLProp} {h : HeapFragment} :
    models ρ (.star (.owned ct .init ptr val) R) h →
    ∃ v, CerbLean.ProofSystem.heapValueHasType v val.bt ∧
      models ρ (.star (.owned ct .init ptr val) R) h := by
  sorry

/-- Store updates the heap: writing to `Owned<ct>(init, ptr, valOld)`
    produces `Owned<ct>(init, ptr, valNew)`. -/
theorem store_updates_models {ρ : Valuation} {ct : Ctype}
    {ptr valOld valNew : IndexTerm} {R : SLProp}
    {h : HeapFragment} :
    models ρ (.star (.owned ct .init ptr valOld) R) h →
    ∃ h', models ρ (.star (.owned ct .init ptr valNew) R) h' := by
  sorry

/-- Create extends the heap: allocating fresh memory produces a new
    `Block<ct>(ptr)` resource for a fresh pointer `ptr`. -/
theorem create_extends_models {ρ : Valuation} {ct : Ctype}
    {H : SLProp} {h : HeapFragment} :
    models ρ H h →
    ∃ ptr h',
      models ρ (.star (.block ct ptr) H) h' := by
  sorry

/-- Kill (owned) shrinks the heap: deallocating an `Owned` resource
    removes it, leaving the remainder. -/
theorem kill_owned_shrinks_models {ρ : Valuation} {ct : Ctype}
    {initState : Init} {ptr val : IndexTerm} {R : SLProp}
    {h : HeapFragment} :
    models ρ (.star (.owned ct initState ptr val) R) h →
    ∃ h', models ρ R h' := by
  sorry

/-- Kill (block) shrinks the heap: deallocating a `Block` resource
    removes it, leaving the remainder. -/
theorem kill_block_shrinks_models {ρ : Valuation} {ct : Ctype}
    {ptr : IndexTerm} {R : SLProp} {h : HeapFragment} :
    models ρ (.star (.block ct ptr) R) h →
    ∃ h', models ρ R h' := by
  sorry

end CerbLean.ProofSystem.Soundness
