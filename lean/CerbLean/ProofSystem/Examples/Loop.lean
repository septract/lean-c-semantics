/-
  Example: Typing derivation for a simple loop using save/run

  Demonstrates the save/run typing rules with the simplest possible
  loop: an infinite loop that immediately jumps back to the label.

  Core IR (simplified):
    save loop (v : signed_int = load(signed_int, p)) {
      run loop [v]
    }

  This is trivially well-typed because:
  - `save` checks that the body type-checks under the invariant
  - `run` type-checks against any return type and post-heap (it's a jump)

  A realistic countdown loop (decrement + conditional + run) additionally
  requires PexprMatchesTerm witnesses and substitution. See `countdownTyped`
  below.

  Created: 2026-02-27
  Updated: 2026-02-28 — added PexprMatchesTerm witnesses, argument substitution
-/

import CerbLean.ProofSystem.HasType

namespace CerbLean.ProofSystem.Examples

open CerbLean.Core (Sym Ctype Ctype_ BasicType IntegerType IntBaseKind
                     Value LoadedValue ObjectValue IntegerValue
                     APexpr Pexpr AExpr Expr APattern Pattern
                     Paction AAction Action Polarity MemoryOrder KillKind
                     Annots Binop SymPrefix Loc Name)
open CerbLean.CN.Types

/-! ## Type and Symbol Definitions -/

/-- The C type `signed int`. -/
def cntSignedIntCtype : Ctype := ⟨[], .basic (.integer (.signed .int_))⟩

/-- Symbol for the pointer parameter `p`. -/
def cntPSym : Sym := { id := 0, description := .id "p" }

/-- Symbol for the loop label. -/
def loopSym : Sym := { id := 1, description := .id "loop" }

/-- Symbol for the current counter value `v`. -/
def cntVSym : Sym := { id := 2, description := .id "v" }

/-! ## Index Terms -/

/-- Index term for pointer `p`. -/
def cntPtrTerm : IndexTerm :=
  AnnotTerm.mk (.sym cntPSym) .loc default

/-- Index term for the loop variable `v`. -/
def cntVTerm : IndexTerm :=
  AnnotTerm.mk (.sym cntVSym) (.bits .signed 32) default

/-! ## Loop Invariant

  The loop invariant is: `Owned<signed int>(init, p, v)`
  where `v` is the current counter value (parameter of the loop).
-/

/-- The loop invariant: `Owned<int>(init, p, v)`. -/
def loopInvariant : SLProp :=
  .owned cntSignedIntCtype .init cntPtrTerm cntVTerm

/-- The label invariant structure for the loop. -/
def loopLabelInv : LabelInv where
  params := [(cntVSym, .bits .signed 32)]
  invariant := loopInvariant

/-! ## Typing Context

  The context has:
  - `p` bound as a pointer (loc type)
  - The loop label invariant registered
-/

/-- The typing context for the loop. -/
def cntCtx : Ctx :=
  { Ctx.empty with
    vars := [(cntPSym, .loc)]
    labelInvs := [(loopSym, loopLabelInv)] }

/-! ## Sanity Checks -/

/-- The save rule is applicable: the loop label is in context. -/
example : cntCtx.lookupLabelInv loopSym = some loopLabelInv := by rfl

/-- The invariant parameters can be added to the context. -/
example : (cntCtx.addParams loopLabelInv.params).lookupVar cntVSym =
    some (.bits .signed 32) := by rfl

/-! ## Minimal Loop Expression

  The simplest loop: `save loop (v) { run loop [v] }`.
  This is an infinite loop that immediately jumps back with the same args.
  It's the minimal expression that exercises both save and run rules.
-/

/-- The Core BaseType for signed int. -/
def cntSignedIntBty : CerbLean.Core.BaseType := .loaded .integer

/-- APexpr for the initial value of the loop parameter. -/
def cntInitPe : APexpr := ⟨[], none, .sym cntVSym⟩

/-- The Core expression: `save loop (v = <init>) { run loop [v] }`. -/
def loopExpr : AExpr :=
  ⟨[], .save loopSym cntSignedIntBty [(cntVSym, cntSignedIntBty, cntInitPe)]
    ⟨[], .run loopSym [cntInitPe]⟩⟩

/-- The inner context inside the save body (with loop param `v` bound). -/
def innerCtx : Ctx := cntCtx.addParams loopLabelInv.params

/-! ### Substitutions for save/run arguments

  The save/run rules use `substTotal` (total substitution) instead of the
  `partial` `subst`. This enables definitional reduction: the substitution
  equalities hold by `rfl` on concrete terms.
-/

/-- The substitution mapping cntVSym → cntVTerm (identity-like). -/
def loopIdentSubst : Subst :=
  Subst.fromMapping [(cntVSym.id, cntVTerm)]

/-- Identity substitution on loopInvariant reduces by `rfl`. -/
example : loopInvariant.substTotal loopIdentSubst = loopInvariant := by rfl

/-- Typing derivation for the minimal loop.

    Proves that `save loop (v) { run loop [v] }` type-checks under
    the loop invariant. This exercises both the `save` and `run` rules
    with PexprMatchesTerm witnesses and argument substitution:

    1. **save**: looks up `loopSym` → `loopLabelInv`, matches args via
       PexprMatchesTerm, substitutes into invariant, checks body
    2. **run**: looks up `loopSym` → `loopLabelInv`, matches args,
       substitutes into invariant, checks precondition

    The substitution `loopIdentSubst` maps v → v (identity), so the
    substituted invariant equals `loopInvariant` by `rfl`. -/
theorem loopTyped :
    HasType cntCtx
      loopInvariant
      loopExpr
      .unit
      (.emp) := by
  -- save rule: substTotal reduces loopInvariant.substTotal loopIdentSubst = loopInvariant
  refine HasType.save (inv := loopLabelInv) (argTerms := [cntVTerm])
    (σ := loopIdentSubst) rfl rfl rfl rfl ?_ ?_
  · -- PexprMatchesTerm for each param
    intro i hp ht
    match i, hp, ht with
    | 0, _, _ => exact PexprMatchesTerm.sym cntVSym (.bits .signed 32) default
  · -- body (run loop) type-checks under invariant
    change HasType _ loopInvariant _ _ _
    -- run rule: substTotal reduces identically
    exact HasType.run (inv := loopLabelInv) (argTerms := [cntVTerm])
      (σ := loopIdentSubst) rfl rfl rfl rfl
      (fun i ha ht => by match i, ha, ht with
        | 0, _, _ => exact PexprMatchesTerm.sym cntVSym (.bits .signed 32) default)

/-! ## Countdown Loop Example

  A more realistic loop: decrement a counter until it reaches zero.

  Core IR (simplified):
    save loop (v : signed_int = <init>) {
      let c = v > 0;
      if c {
        sseq _ = store(signed_int, p, v - 1);
        run loop [v - 1]
      } else {
        pure ()
      }
    }

  This exercises the full set of loop typing rules:
  - `save` defines the loop with invariant `Owned(p, v) ∗ emp`
  - `let_` binds the comparison result (workaround: `condTermOfPexpr` only handles symbols)
  - `if_` branches on the condition with path conditions
  - `action_store` updates the heap value from v to v-1
  - `run` jumps back to the loop label with substituted invariant
  - `pure` exits the loop in the else branch

  **Key improvement over previous version**: The old `h_inv_restore` hypothesis
  was `SLProp.entails postStoreHeap countdownInvariant`, which asserted that
  `Owned(p, v-1)` entails `Owned(p, v)` — a false and unsound claim. The new
  `run` rule substitutes `v → (v-1)` into the invariant, producing
  `Owned(p, v-1) ∗ emp` = `postStoreHeap` as the precondition. This
  substitution reduces definitionally, so `countdownTyped` needs no hypotheses.
-/

/-- Additional symbol for the condition variable `c`. -/
def cdCSym : Sym := { id := 3, description := .id "c" }

/-- Index term for `v - 1`. -/
def vMinusOneTerm : IndexTerm :=
  AnnotTerm.mk
    (.binop .sub
      (AnnotTerm.mk (.sym cntVSym) (.bits .signed 32) default)
      (AnnotTerm.mk (.const (.bits .signed 32 1)) (.bits .signed 32) default))
    (.bits .signed 32) default

/-- The countdown invariant in star-emp form (fits action rules directly). -/
def countdownInvariant : SLProp :=
  .star (.owned cntSignedIntCtype .init cntPtrTerm cntVTerm) .emp

/-- Post-store heap: `Owned(p, v-1) ∗ emp`. -/
def postStoreHeap : SLProp :=
  .star (.owned cntSignedIntCtype .init cntPtrTerm vMinusOneTerm) .emp

/-- Label invariant for the countdown loop. -/
def countdownLabelInv : LabelInv where
  params := [(cntVSym, .bits .signed 32)]
  invariant := countdownInvariant

/-- Typing context for the countdown. -/
def countdownCtx : Ctx :=
  { Ctx.empty with
    vars := [(cntPSym, .loc)]
    labelInvs := [(loopSym, countdownLabelInv)] }

/-- APexpr for the type annotation `signed int`. -/
def cdTyPe : APexpr := ⟨[], none, .val (.ctype cntSignedIntCtype)⟩

/-- APexpr for the pointer parameter `p`. -/
def cdPtrPe : APexpr := ⟨[], none, .sym cntPSym⟩

/-- APexpr for `v > 0`. -/
def cdCondPe : APexpr :=
  ⟨[], none, .op .gt (.sym cntVSym)
    (.val (.loaded (.specified (.integer ⟨0, .none⟩))))⟩

/-- APexpr for `v - 1`. -/
def cdVMinusOnePe : APexpr :=
  ⟨[], none, .op .sub (.sym cntVSym)
    (.val (.loaded (.specified (.integer ⟨1, .none⟩))))⟩

/-- APexpr for the condition variable `c`. -/
def cdCondSymPe : APexpr := ⟨[], none, .sym cdCSym⟩

/-- The countdown loop expression:
    `save loop (v) { let c = v > 0; if c { store(p, v-1); run loop } else { pure () } }` -/
def countdownExpr : AExpr :=
  ⟨[], .save loopSym cntSignedIntBty [(cntVSym, cntSignedIntBty, cntInitPe)]
    ⟨[], .let_ ⟨[], .base (some cdCSym) (.loaded .integer)⟩ cdCondPe
      ⟨[], .if_ cdCondSymPe
        -- true branch: store v-1 then loop back
        ⟨[], .sseq ⟨[], .base none cntSignedIntBty⟩
          ⟨[], .action ⟨.pos, ⟨default, .store false cdTyPe cdPtrPe cdVMinusOnePe .na⟩⟩⟩
          ⟨[], .run loopSym [cdVMinusOnePe]⟩⟩
        -- false branch: exit loop
        ⟨[], .pure ⟨[], none, .val .unit⟩⟩⟩⟩⟩

/-! ### Substitutions for Countdown

  The save/run rules use `substTotal` for argument substitution into the invariant.
  - Save: maps v → v (identity) — invariant unchanged
  - Run: maps v → (v-1) — invariant becomes `Owned(p, v-1) ∗ emp` = `postStoreHeap`

  Both equalities reduce by `rfl` thanks to `substTotal` being total. -/

/-- Substitution for save: maps v → v (identity). -/
def countdownSaveSubst : Subst :=
  Subst.fromMapping [(cntVSym.id, cntVTerm)]

/-- Substitution for run: maps v → (v-1). -/
def countdownRunSubst : Subst :=
  Subst.fromMapping [(cntVSym.id, vMinusOneTerm)]

/-- Identity substitution on countdownInvariant reduces by `rfl`. -/
example : countdownInvariant.substTotal countdownSaveSubst = countdownInvariant := by rfl

/-- Run substitution produces postStoreHeap — reduces by `rfl`. -/
example : countdownInvariant.substTotal countdownRunSubst = postStoreHeap := by rfl

/-- Typing derivation for the countdown loop.

    **No hypotheses, no sorry** — the argument substitution in `save` and `run`
    rules uses `substTotal` which reduces definitionally on concrete terms.

    Previously this theorem required sorry'd substitution lemmas (because
    `Term.subst` is `partial`) and an unsound `SLProp.entails` hypothesis.
    Now the `run` rule substitutes `v → (v-1)` in the invariant via `substTotal`,
    producing `Owned(p, v-1) ∗ emp` = `postStoreHeap` as the precondition.

    **Rules exercised**: save, let_, if_, action_store, run, pure,
    PexprMatchesTerm (sym, op, bitsVal) -/
theorem countdownTyped :
    HasType countdownCtx
      countdownInvariant
      countdownExpr
      .unit
      countdownInvariant := by
  -- save rule: substTotal reduces countdownInvariant.substTotal countdownSaveSubst
  -- = countdownInvariant by rfl
  refine HasType.save (inv := countdownLabelInv) (argTerms := [cntVTerm])
    (σ := countdownSaveSubst) rfl rfl rfl rfl ?_ ?_
  · -- PexprMatchesTerm: cntInitPe.expr matches cntVTerm
    intro i hp ht
    match i, hp, ht with
    | 0, _, _ => exact PexprMatchesTerm.sym cntVSym (.bits .signed 32) default
  · -- body: let c = v > 0; if c { store; run } else { pure () }
    apply HasType.let_ (τ₁ := .bool)
    · exact PureHasType.op
        (PureHasType.sym (by rfl))
        (PureHasType.val (τ := .bits .signed 32) trivial) rfl
    · apply HasType.if_
      · exact PureHasType.sym (by rfl)
      · rfl
      · -- true branch: store v-1, then run loop [v-1]
        apply HasType.sseq_wild
        · -- store: PexprMatchesTerm for pointer and value
          exact @HasType.action_store _ _ _ _ _ _ _ vMinusOneTerm _ _ _
            (.bits .signed 32) rfl
            (PexprMatchesTerm.sym cntPSym .loc default)
            (PexprMatchesTerm.op .sub .sub _ _ _ _
              (.bits .signed 32) default trivial
              (PexprMatchesTerm.sym cntVSym (.bits .signed 32) default)
              (PexprMatchesTerm.bitsVal 1 .none .signed 32 (.bits .signed 32) default))
            (PureHasType.sym (by rfl))
            (PureHasType.op
              (PureHasType.sym (by rfl))
              (PureHasType.val (τ := .bits .signed 32) trivial) rfl)
            rfl  -- valNew.bt = τ
        · -- run: substTotal reduces countdownInvariant.substTotal countdownRunSubst
          -- = postStoreHeap by rfl, matching what the store produced
          change HasType _ postStoreHeap _ _ _
          exact HasType.run (inv := countdownLabelInv)
            (argTerms := [vMinusOneTerm]) (σ := countdownRunSubst)
            rfl rfl rfl rfl
            (fun i ha ht => by match i, ha, ht with
              | 0, _, _ =>
                exact PexprMatchesTerm.op .sub .sub _ _ _ _
                  (.bits .signed 32) default trivial
                  (PexprMatchesTerm.sym cntVSym (.bits .signed 32) default)
                  (PexprMatchesTerm.bitsVal 1 .none .signed 32
                    (.bits .signed 32) default))
      · exact HasType.pure (PureHasType.val trivial)

end CerbLean.ProofSystem.Examples
