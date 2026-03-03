/-
  PureHasType Soundness Proof

  Split into three theorems:

  1. **Preservation** (unconditional): IF evalPexpr succeeds, the result is
     well-typed and memory is unchanged. Provable for ALL PureHasType
     expressions (including memberof), vacuously true when eval fails.

  2. **Progress** (restricted): In a "pure" environment (PureEnvCompat — no
     `.loaded` values), evaluation succeeds. Sorry'd for cases where memberof
     produces `.loaded` values that break the extended env's PureEnvCompat.

  3. **Soundness** (combined): preservation + progress. The original theorem
     statement, now using PureEnvCompat instead of EnvCompat.

  Proof structure: induction on the PureHasType derivation.
  Each case connects the typing rule to the corresponding evalPexpr branch.

  Created: 2026-03-02
  Updated: 2026-03-03 — split into preservation/progress/soundness
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
open CerbLean.ProofSystem (Ctx SLProp PureHasType valueHasType pureValueHasType
                            pureValueHasType_implies_valueHasType
                            heapValueHasType evalIndexTerm
                            PexprMatchesTerm pexprEnvLookup
                            opResultType intTypeToBaseType CNBaseType)
open Std (HashMap)

/-! ## Theorem A: Type Preservation (unconditional)

    IF evalPexpr succeeds, the result is well-typed and memory is unchanged.
    This is unconditional — no environment restrictions needed. The theorem
    is vacuously true when evaluation fails.

    Uses `EnvCompat` (not `PureEnvCompat`) because we don't need env values
    to be operable — we only need to show that IF the result comes back,
    it has the right type. -/

/-- PureHasType preservation: if evalPexpr succeeds on a well-typed expression,
    the result value has the claimed type and memory is unchanged. -/
theorem PureHasType.preservation
    {file : File} {typeEnv : TypeEnv} {interpState : InterpState}
    {env : List (HashMap Sym Value)}
    {Γ : Ctx} {ρ : Valuation}
    {pe : APexpr} {τ : BaseType}
    (hty : PureHasType Γ pe τ)
    (henv : EnvCompat env Γ.vars ρ)
    (htags : TagDefsCompat Γ file typeEnv)
    {fuel : Nat} {v : Value} {st' : InterpState}
    (hok : (((evalPexpr fuel env pe).run ⟨file, typeEnv⟩).run interpState) = .ok (v, st'))
    : valueHasType v τ ∧ st'.memory = interpState.memory := by
  induction hty with
  | @val Γ annots coreTy v' τ' hvt =>
    -- evalPexpr_val' gives v' = v, st' = interpState
    sorry
  | @sym Γ annots s coreTy τ' hlook =>
    -- lookupEnv succeeds, EnvCompat gives valueHasType
    sorry
  | @op Γ annots coreTy binop e₁ e₂ τ₁ τ₂ τ' _hty₁ _hty₂ hop ih₁ ih₂ =>
    -- IH for subexpressions, evalBinop type preservation (L5)
    sorry
  | @if_ Γ annots coreTy cond then_ else_ τ' _htyCond _htyThen _htyElse
      ihCond ihThen ihElse =>
    -- Case split on condition value, IH for taken branch
    sorry
  | @not_ Γ annots coreTy e _htyE ihE =>
    -- Bool form, invert
    sorry
  | @let_ Γ annots coreTy patAnnots x bty e₁ e₂ τ₁ τ₂ _htyE₁ _htyE₂ ih₁ ih₂ =>
    -- IH₁ for e₁, extend env, IH₂ for e₂
    sorry
  | @arrayShift Γ annots coreTy ptr ct idx _htyPtr ihPtr =>
    sorry
  | @memberShift Γ annots coreTy ptr tag member _htyPtr ihPtr =>
    sorry
  | @convInt Γ annots coreTy ity e τ₁ _htyE ihE =>
    -- convertInt type preservation (L6)
    sorry
  | @wrapI Γ annots coreTy ity iop e₁ e₂ τ₁ τ₂ _htyE₁ _htyE₂ ih₁ ih₂ =>
    -- wrapIntOp type preservation (L7)
    sorry
  | @isScalar Γ annots coreTy e _htyE ihE =>
    -- Returns .true_ or .false_, both have type .bool
    sorry
  | @isInteger Γ annots coreTy e _htyE ihE => sorry
  | @isSigned Γ annots coreTy e _htyE ihE => sorry
  | @isUnsigned Γ annots coreTy e _htyE ihE => sorry
  | @areCompatible Γ annots coreTy e₁ e₂ _htyE₁ _htyE₂ ih₁ ih₂ => sorry
  | @struct_ Γ annots coreTy tag members fieldTypes hlen hfields ih => sorry
  | @memberof Γ annots coreTy tag member e fields fieldCt τ'
      _htyE htagLook hfieldLook hctBase ihE =>
    sorry
  | @case_ Γ annots coreTy scrut branches τs τ' _htyScrut htyBranches
      ihScrut ihBranches =>
    sorry

/-! ## Theorem B: Progress (restricted to pure-env programs)

    In a "pure" environment (PureEnvCompat — all values in `.object` form),
    evaluation succeeds. This is the termination/progress guarantee.

    **Caveat**: `memberof` produces `.loaded (.specified _)` values, so the
    extended env after a `let x = memberof(...) in body` is NOT PureEnvCompat.
    The `let_`-with-memberof case is sorry'd. -/

/-- PureHasType progress: in a pure environment, evaluation succeeds. -/
theorem PureHasType.progress
    {file : File} {typeEnv : TypeEnv} {interpState : InterpState}
    {env : List (HashMap Sym Value)}
    {Γ : Ctx} {ρ : Valuation}
    {pe : APexpr} {τ : BaseType}
    (hty : PureHasType Γ pe τ)
    (henv : PureEnvCompat env Γ.vars ρ)
    (htags : TagDefsCompat Γ file typeEnv)
    : ∃ fuel v st',
      (((evalPexpr fuel env pe).run ⟨file, typeEnv⟩).run interpState) = .ok (v, st') := by
  induction hty with
  /-
    Tier 1: Trivial cases
  -/
  | @val Γ annots coreTy v τ hvt =>
    -- evalPexpr (fuel+1) env ⟨annots, coreTy, .val v⟩ = pure v
    refine ⟨1, v, interpState, ?_⟩
    rw [evalPexpr_annot_irrelevant (a₁ := annots) (a₂ := []) (t₁ := coreTy) (t₂ := none)]
    simp only [evalPexpr_val']
    rfl

  | @sym Γ annots s coreTy τ hlook =>
    -- PureEnvCompat gives envLookup succeeds
    sorry

  | @op Γ annots coreTy binop e₁ e₂ τ₁ τ₂ τ _hty₁ _hty₂ hop ih₁ ih₂ =>
    -- IH gives fuel₁, v₁ for e₁ and fuel₂, v₂ for e₂
    -- Need: fuel monotonicity (L2) to combine, annotation irrelevance (L1),
    --       state preservation (L3), pureValueHasType form lemmas
    sorry

  | @if_ Γ annots coreTy cond then_ else_ τ _htyCond _htyThen _htyElse
      ihCond ihThen ihElse =>
    -- IH gives fuel_c, v_c for cond (with type .bool)
    -- Bool form: v_c = .true_ or .false_, then IH for taken branch
    sorry

  | @not_ Γ annots coreTy e _htyE ihE =>
    -- IH gives fuel_e, v for e (with type .bool)
    -- Bool form, then invert
    sorry

  /-
    Tier 2: Moderate cases
  -/
  | @let_ Γ annots coreTy patAnnots x bty e₁ e₂ τ₁ τ₂ _htyE₁ _htyE₂ ih₁ ih₂ =>
    -- IH₁ gives fuel₁, v₁ for e₁ (with pureValueHasType v₁ τ₁ from preservation)
    -- matchPattern with base (some x) always gives [(x, v₁)]
    -- CAVEAT: IH₂ needs PureEnvCompat for extended env. If e₁ is memberof,
    -- the result v₁ is .loaded, breaking PureEnvCompat. Sorry'd for now.
    sorry

  | @arrayShift Γ annots coreTy ptr ct idx _htyPtr ihPtr =>
    -- IH gives ptr value with type .loc
    -- pureValueHasType_loc_form: v = .object (.pointer _)
    sorry

  | @memberShift Γ annots coreTy ptr tag member _htyPtr ihPtr =>
    sorry

  | @convInt Γ annots coreTy ity e τ₁ _htyE ihE =>
    -- IH gives v for e, convertInt succeeds on well-typed input
    sorry

  | @wrapI Γ annots coreTy ity iop e₁ e₂ τ₁ τ₂ _htyE₁ _htyE₂ ih₁ ih₂ =>
    sorry

  | @isScalar Γ annots coreTy e _htyE ihE =>
    -- IH gives v with type .ctype
    -- pureValueHasType_ctype_form: v = .ctype ct
    -- isScalar always returns .true_ or .false_
    sorry

  | @isInteger Γ annots coreTy e _htyE ihE => sorry
  | @isSigned Γ annots coreTy e _htyE ihE => sorry
  | @isUnsigned Γ annots coreTy e _htyE ihE => sorry
  | @areCompatible Γ annots coreTy e₁ e₂ _htyE₁ _htyE₂ ih₁ ih₂ => sorry

  /-
    Tier 3: Hard cases
  -/
  | @struct_ Γ annots coreTy tag members fieldTypes hlen hfields ih =>
    -- Each field eval by IH, combine fuels
    sorry

  | @memberof Γ annots coreTy tag member e fields fieldCt τ
      _htyE htagLook hfieldLook hctBase ihE =>
    -- IH gives struct value, member extraction via valueFromMemValue
    -- NOTE: memberof produces .loaded values, but progress still holds
    -- (the eval itself succeeds). The issue is only when the .loaded result
    -- is used in a subsequent operation.
    sorry

  | @case_ Γ annots coreTy scrut branches τs τ _htyScrut htyBranches
      ihScrut ihBranches =>
    sorry

/-! ## Combined Soundness

    Combines preservation and progress: in a pure environment, evaluation
    succeeds AND the result is well-typed AND memory is unchanged.

    This is the original `PureHasType.soundness` theorem, now using
    `PureEnvCompat` (stronger env requirement) instead of `EnvCompat`. -/

/-- PureHasType soundness: well-typed pure expressions in a pure environment
    evaluate to typed values without modifying memory.

    Design notes:
    1. **Existential fuel**: Unlike the main theorem which uses `∀ fuel`,
       we use `∃ fuel` here because pure expressions don't loop (PureHasType
       has no save/run constructors). Every well-typed pure expression
       terminates within some fuel bound.

    2. **Memory unchanged**: `st'.memory = interpState.memory` captures that
       pure evaluation doesn't modify the heap. The interpreter may update
       `stdout`/`stderr`/`nextExclusionId` but NOT memory.

    3. **PureEnvCompat**: Requires all env values to be in `.object` form.
       This excludes programs where `memberof` results are used in operand
       positions (those programs fail at runtime despite being well-typed
       by PureHasType). See Phase 3 plan for the proper long-term fix
       (moving memberof out of PureHasType).

    4. **evalPexpr runs in InterpM**: Even pure expressions run in `InterpM`
       because they may call `sizeof`/`alignof` (which read `TypeEnv`).
       They don't modify `MemState`. -/
theorem PureHasType.soundness
    {file : File} {typeEnv : TypeEnv} {interpState : InterpState}
    {env : List (HashMap Sym Value)}
    {Γ : Ctx} {ρ : Valuation}
    {pe : APexpr} {τ : BaseType}
    (hty : PureHasType Γ pe τ)
    (henv : PureEnvCompat env Γ.vars ρ)
    (htags : TagDefsCompat Γ file typeEnv)
    : ∃ fuel v st',
      (((evalPexpr fuel env pe).run ⟨file, typeEnv⟩).run interpState) = .ok (v, st') ∧
      valueHasType v τ ∧
      st'.memory = interpState.memory := by
  -- Combine progress and preservation
  obtain ⟨fuel, v, st', hok⟩ := PureHasType.progress hty henv htags
  have henv' := PureEnvCompat_implies_EnvCompat henv
  obtain ⟨hvt, hmem⟩ := PureHasType.preservation hty henv' htags hok
  exact ⟨fuel, v, st', hok, hvt, hmem⟩

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
