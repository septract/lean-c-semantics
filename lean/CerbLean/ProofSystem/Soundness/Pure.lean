/-
  PureHasType Soundness Proof

  Proves soundness of PureHasType with respect to evalPexpr:
  well-typed pure expressions evaluate to typed values without
  modifying memory.

  Proof structure: induction on the PureHasType derivation.
  Each case connects the typing rule to the corresponding evalPexpr branch.

  Created: 2026-03-02
-/

import CerbLean.ProofSystem.Soundness.PureHelpers

namespace CerbLean.ProofSystem.Soundness

open CerbLean.Core (Sym Ctype Identifier APexpr Pexpr Value File Annots
                     Binop Iop IntegerType APattern Pattern)
open CerbLean.CN.Types (IndexTerm BaseType)
open CerbLean.CN.Semantics (HeapValue Valuation)
open CerbLean.Semantics (InterpState InterpEnv InterpError InterpM
                          evalPexpr evalBinop convertInt wrapIntOp
                          lookupEnv bindAllInEnv matchPattern mkAPexpr
                          evalPexpr_val' evalPexpr_if' evalPexpr_let'
                          evalPexpr_op')
open CerbLean.Memory (TypeEnv)
open CerbLean.ProofSystem (Ctx SLProp PureHasType valueHasType
                            heapValueHasType evalIndexTerm
                            PexprMatchesTerm pexprEnvLookup
                            opResultType intTypeToBaseType CNBaseType)
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
  induction hty with
  /-
    Tier 1: Trivial cases
  -/
  | @val Γ annots coreTy v τ hvt =>
    -- evalPexpr (fuel+1) env ⟨annots, coreTy, .val v⟩ = pure v
    -- Need: rw annotation irrelevance, then use evalPexpr_val'
    -- fuel=1, v_out=v, st'=interpState, pure doesn't modify state
    refine ⟨1, v, interpState, ?_, hvt, rfl⟩
    rw [evalPexpr_annot_irrelevant (a₁ := annots) (a₂ := []) (t₁ := coreTy) (t₂ := none)]
    simp only [evalPexpr_val']
    rfl

  | @sym Γ annots s coreTy τ hlook =>
    -- evalPexpr looks up s in env, which succeeds by EnvCompat (L8)
    -- Need: annotation irrelevance + EnvCompat_lookup + lookupEnv equation
    sorry

  | @op Γ annots coreTy binop e₁ e₂ τ₁ τ₂ τ _hty₁ _hty₂ hop ih₁ ih₂ =>
    -- IH gives fuel₁, v₁ for e₁ and fuel₂, v₂ for e₂
    -- Need: fuel monotonicity (L2) to combine, annotation irrelevance (L1),
    --       state preservation (L3), evalBinop type preservation (L5)
    sorry

  | @if_ Γ annots coreTy cond then_ else_ τ _htyCond _htyThen _htyElse
      ihCond ihThen ihElse =>
    -- IH gives fuel_c, v_c for cond (with type .bool)
    -- Need: bool form (L12) to case split on v_c = .true_ or .false_
    -- Then IH for the taken branch, fuel monotonicity (L2)
    sorry

  | @not_ Γ annots coreTy e _htyE ihE =>
    -- IH gives fuel_e, v for e (with type .bool)
    -- Need: bool form (L12), then invert .true_ → .false_ or vice versa
    sorry

  /-
    Tier 2: Moderate cases
  -/
  | @let_ Γ annots coreTy patAnnots x bty e₁ e₂ τ₁ τ₂ _htyE₁ _htyE₂ ih₁ ih₂ =>
    -- IH₁ gives fuel₁, v₁ for e₁
    -- matchPattern with base (some x) always gives [(x, v₁)] (L10)
    -- Need: EnvCompat_bind (L9) for extended env
    -- IH₂ gives fuel₂, v₂ for e₂ in extended context
    -- Combine with fuel monotonicity (L2)
    sorry

  | @arrayShift Γ annots coreTy ptr ct idx _htyPtr ihPtr =>
    -- IH gives ptr value with type .loc
    -- Need: loc form (L13) to get pointer value
    -- evalPexpr's arrayShift branch calls arrayShiftPtrval
    sorry

  | @memberShift Γ annots coreTy ptr tag member _htyPtr ihPtr =>
    -- IH gives ptr value with type .loc
    -- evalPexpr's memberShift branch extracts pointer and shifts
    sorry

  | @convInt Γ annots coreTy ity e τ₁ _htyE ihE =>
    -- IH gives v for e
    -- convertInt always produces .object (.integer ...) (L6)
    sorry

  | @wrapI Γ annots coreTy ity iop e₁ e₂ τ₁ τ₂ _htyE₁ _htyE₂ ih₁ ih₂ =>
    -- IH gives v₁, v₂ for operands
    -- wrapIntOp always produces .object (.integer ...) (L7)
    sorry

  | @isScalar Γ annots coreTy e _htyE ihE =>
    -- IH gives v with type .ctype (after Gap 2 fix)
    -- ctype form (L11): v = .ctype ct
    -- evalPexpr's isScalar returns .true_ or .false_, both have type .bool
    sorry

  | @isInteger Γ annots coreTy e _htyE ihE =>
    sorry

  | @isSigned Γ annots coreTy e _htyE ihE =>
    sorry

  | @isUnsigned Γ annots coreTy e _htyE ihE =>
    sorry

  | @areCompatible Γ annots coreTy e₁ e₂ _htyE₁ _htyE₂ ih₁ ih₂ =>
    sorry

  /-
    Tier 3: Hard cases
  -/
  | @struct_ Γ annots coreTy tag members fieldTypes hlen hfields ih =>
    -- Each field eval by IH, combine fuels with fuel monotonicity
    -- memValueFromValue is partial: need sorry'd bridge lemma
    sorry

  | @memberof Γ annots coreTy tag member e fields fieldCt τ
      _htyE htagLook hfieldLook hctBase ihE =>
    -- IH gives struct value, member extraction via valueFromMemValue
    sorry

  | @case_ Γ annots coreTy scrut branches τs τ _htyScrut htyBranches
      ihScrut ihBranches =>
    -- Scrutinee eval, then branch matching and eval
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
