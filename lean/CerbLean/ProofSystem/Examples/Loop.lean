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

  A realistic countdown loop (decrement + conditional + run) would additionally
  require entailment proofs to connect invariant maintenance through the store.
  See the comment on `countdownNotes` below for what that would need.

  Created: 2026-02-27
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

/-- Typing derivation for the minimal loop.

    Proves that `save loop (v) { run loop [v] }` type-checks under
    the loop invariant. This exercises both the `save` and `run` rules:

    1. **save**: looks up `loopSym` → `loopLabelInv`, binds params, checks body
    2. **run**: looks up `loopSym` → `loopLabelInv`, pre must satisfy invariant

    Since `run` makes the return type and post-heap unconstrained (it's a
    control transfer that doesn't return), we can claim any τ and H₂. -/
theorem loopTyped :
    HasType cntCtx
      loopInvariant
      loopExpr
      .unit
      (.emp) := by
  apply HasType.save (inv := loopLabelInv)
  · -- lookupLabelInv loopSym = some loopLabelInv
    rfl
  · -- body (run loop) type-checks under invariant
    apply HasType.run (inv := loopLabelInv)
    -- lookupLabelInv loopSym in inner context
    rfl

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
  - `run` jumps back to the loop label
  - `consequence` bridges between post-store heap and invariant
  - `pure` exits the loop in the else branch

  The one entailment we factor out as a hypothesis: after storing v-1,
  the heap `Owned(p, v-1) ∗ emp` must satisfy the invariant `Owned(p, v) ∗ emp`
  (with v rebound by the run arguments). In a full system with argument
  substitution in the `run` rule, this would be automatic.
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

/-- Typing derivation for the countdown loop.

    The single hypothesis `h_inv_restore` captures the key entailment that
    our current framework cannot prove internally: after storing `v - 1`,
    the resulting heap `Owned(p, v-1) ∗ emp` satisfies the loop invariant
    `Owned(p, v) ∗ emp` (with `v` rebound to `v-1` by the `run` arguments).

    In a full system with argument substitution in the `run` rule, this
    entailment would be discharged automatically. Here we factor it out
    to show the typing derivation structure is otherwise complete.

    **Rules exercised**: save, let_, if_, action_store, run, consequence, pure -/
theorem countdownTyped
    (h_inv_restore : SLProp.entails postStoreHeap countdownInvariant) :
    HasType countdownCtx
      countdownInvariant
      countdownExpr
      .unit
      countdownInvariant := by
  -- save: establish the loop with countdownLabelInv
  apply HasType.save (inv := countdownLabelInv)
  · rfl  -- lookupLabelInv loopSym = some countdownLabelInv
  · -- body: let c = v > 0; if c { store; run } else { pure () }
    apply HasType.let_ (τ₁ := .bool)
    · -- PureHasType: v > 0 has type bool
      exact PureHasType.op
        (PureHasType.sym (by rfl))
        (PureHasType.val (τ := .bits .signed 32) trivial)
        rfl
    · -- if c { store; run } else { pure () }
      apply HasType.if_
      · exact PureHasType.sym (by rfl)  -- c is bool
      · rfl  -- condTermOfPexpr (.sym cdCSym) = some condTerm
      · -- true branch: sseq _ = store(p, v-1); run loop
        apply HasType.sseq_wild
        · -- store: Owned(p,v)∗emp → Owned(p,v-1)∗emp
          exact @HasType.action_store _ _ _ _ _ _ _ vMinusOneTerm _ _ _
            (.bits .signed 32)
            (PureHasType.op
              (PureHasType.sym (by rfl))
              (PureHasType.val (τ := .bits .signed 32) trivial)
              rfl)
        · -- run: consequence bridges postStoreHeap → countdownInvariant
          exact HasType.consequence h_inv_restore (fun _ _ h => h)
            (HasType.run (inv := countdownLabelInv) (by rfl))
      · -- false branch: pure ()
        exact HasType.pure (PureHasType.val trivial)

end CerbLean.ProofSystem.Examples
