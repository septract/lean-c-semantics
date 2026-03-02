/-
  PureHasType Soundness Statement

  States the soundness of PureHasType with respect to evalPexpr:
  well-typed pure expressions evaluate to typed values without
  modifying memory.

  Created: 2026-03-02
-/

import CerbLean.ProofSystem.Soundness.Defs
import CerbLean.Semantics.Eval

namespace CerbLean.ProofSystem.Soundness

open CerbLean.Core (Sym Ctype Identifier APexpr Pexpr Value File)
open CerbLean.CN.Types (IndexTerm BaseType)
open CerbLean.CN.Semantics (HeapValue Valuation)
open CerbLean.Semantics (InterpState InterpEnv evalPexpr)
open CerbLean.Memory (TypeEnv)
open CerbLean.ProofSystem (Ctx SLProp PureHasType valueHasType
                            heapValueHasType evalIndexTerm
                            PexprMatchesTerm pexprEnvLookup)
open Std (HashMap)

/-! ## PureHasType Soundness -/

/-- PureHasType soundness: well-typed pure expressions evaluate to
    typed values without modifying memory.

    Design notes:
    1. **Existential fuel**: Unlike the main theorem which uses `∀ fuel`,
       we use `∃ fuel` here because pure expressions don't loop (PureHasType
       has no save/run constructors). Every well-typed pure expression
       terminates within some fuel bound.

    2. **Memory unchanged**: `st'.memory = interpState.memory` captures that
       pure evaluation doesn't modify the heap. The interpreter may update
       `stdout`/`stderr`/`nextExclusionId` but NOT memory.

    3. **evalPexpr runs in InterpM**: Even pure expressions run in `InterpM`
       because they may call `sizeof`/`alignof` (which read `TypeEnv`).
       They don't modify `MemState`. -/
theorem PureHasType.soundness
    {file : File} {typeEnv : TypeEnv} {interpState : InterpState}
    {env : List (HashMap Sym Value)}
    {Γ : Ctx} {ρ : Valuation}
    {pe : APexpr} {τ : BaseType}
    (hty : PureHasType Γ pe τ)
    (henv : EnvCompat env Γ.vars ρ)
    (htags : TagDefsCompat Γ file typeEnv)
    : ∃ fuel v st',
      (((evalPexpr fuel env pe).run ⟨file, typeEnv⟩).run interpState) = .ok (v, st') ∧
      valueHasType v τ ∧
      st'.memory = interpState.memory := by
  sorry

/-! ## PexprMatchesTerm Evaluation Compatibility -/

/-- If a Pexpr matches an IndexTerm, their evaluations are compatible:
    evaluating the Pexpr in the interpreter and evaluating the IndexTerm
    in the logical model produce corresponding values.

    This restates the sorry'd lemma at HasType.lean:978-986 with the
    precise type for the soundness proof context (using `flattenEnv`
    to convert the scoped env to a flat assoc list). -/
theorem pexprMatchesTerm_eval_compat
    {pe : Pexpr} {it : IndexTerm} {ρ : Valuation}
    {env : List (HashMap Sym Value)}
    {Γ : Ctx}
    (hmatch : PexprMatchesTerm pe it)
    (henv : EnvCompat env Γ.vars ρ)
    : ∀ v, pexprEnvLookup (flattenEnv env) pe = some v →
      ∀ τ, valueHasType v τ →
        ∃ hv, evalIndexTerm ρ it = some hv ∧ heapValueHasType hv τ := by
  sorry

end CerbLean.ProofSystem.Soundness
