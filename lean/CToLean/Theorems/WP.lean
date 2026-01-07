/-
  Weakest Precondition (WP) Calculus for Core IR

  This module defines a WP transformer for compositional reasoning about
  UB-freeness and functional correctness of Core programs.

  The WP calculus allows us to:
  1. Compute preconditions for postconditions to hold
  2. Reason compositionally about program fragments
  3. Generate verification conditions automatically

  See docs/VERIFICATION_PLAN.md for the overall verification strategy.
-/

import CToLean.Theorems.UBFree
import CToLean.Semantics.Eval
import CToLean.Semantics.Step
import Std.Data.HashMap

namespace CToLean.Theorems.WP

open CToLean.Core
open CToLean.Semantics
open CToLean.Memory
open Std (HashMap)

/-! ## Postcondition Types

Postconditions describe what should be true after execution.
-/

/-- Postcondition for pure expressions: relates result value to initial state -/
abbrev PurePost := Value → InterpState → Prop

/-- Postcondition for effectful expressions: relates result value to final state -/
abbrev ExprPost := Value → InterpState → Prop

/-! ## WP for Pure Expressions

Pure expressions (Pexpr) don't have side effects, so their WP only needs
to ensure the expression evaluates without UB and satisfies the postcondition.

For a pure expression `pe`, `wpPure pe Q env state` means:
- Evaluating `pe` in environment `env` and state `state` doesn't produce UB
- If evaluation succeeds with value `v`, then `Q v state` holds
-/

/-- Fuel-parameterized weakest precondition for compositional reasoning.

    `wpPureN fuel pe Q env interpEnv state` holds iff:
    - Evaluating `pe` with `fuel` steps doesn't produce undefined behavior
    - If evaluation succeeds with value `v` and final state `s'`, then `Q v s'` holds

    This fuel-indexed version enables compositional rules because
    `evalPexpr (fuel + 1)` for compound expressions uses `evalPexpr fuel`
    for subexpressions.

    Note: We use the result state `s'` in the postcondition rather than the
    parameter state. This enables clean compositional rules since state
    threads through sequential evaluation.
-/
def wpPureN (fuel : Nat) (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) : Prop :=
  match ((evalPexpr fuel env pe).run interpEnv).run state with
  | .ok (v, s') => Q v s'
  | .error (.undefinedBehavior _ _) => False
  | .error _ => True  -- Other errors (type errors, not implemented) are not UB

/-- Weakest precondition for pure expression evaluation (default fuel).

    `wpPure pe Q env state` holds iff:
    - Evaluating `pe` doesn't produce undefined behavior
    - If evaluation succeeds with value `v`, then `Q v state` holds

    Note: Pure expressions don't modify state, so postcondition gets original state.
-/
def wpPure (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) : Prop :=
  wpPureN defaultPexprFuel pe Q env interpEnv state

/-! ## WP Soundness for Pure Expressions

The key theorem: if the WP holds, evaluation doesn't produce UB and
satisfies the postcondition.
-/

/-- Helper: check if an Except result is a UB error -/
def isUBResult {α : Type} : Except InterpError α → Bool
  | .ok _ => false
  | .error (.undefinedBehavior _ _) => true
  | .error _ => false

/-- If wpPureN holds, then evaluation doesn't produce UB -/
theorem wpPureN_noUB (fuel : Nat) (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpPureN fuel pe Q env interpEnv state) :
    isUBResult (((evalPexpr fuel env pe).run interpEnv).run state) = false := by
  unfold wpPureN at h
  unfold isUBResult
  cases hres : ((evalPexpr fuel env pe).run interpEnv).run state with
  | ok p => rfl
  | error e =>
    simp only [hres] at h
    cases e with
    | undefinedBehavior ub loc => exact absurd h (by simp)
    | _ => rfl

/-- If wpPure holds, then evaluation doesn't produce UB -/
theorem wpPure_noUB (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpPure pe Q env interpEnv state) :
    isUBResult (((evalPexpr defaultPexprFuel env pe).run interpEnv).run state) = false :=
  wpPureN_noUB defaultPexprFuel pe Q env interpEnv state h

/-- If wpPureN holds and evaluation succeeds, postcondition holds -/
theorem wpPureN_post (fuel : Nat) (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpPureN fuel pe Q env interpEnv state)
    (result : Value × InterpState)
    (heval : ((evalPexpr fuel env pe).run interpEnv).run state = Except.ok result) :
    Q result.1 result.2 := by
  unfold wpPureN at h
  rw [heval] at h
  exact h

/-- If wpPure holds and evaluation succeeds, postcondition holds -/
theorem wpPure_post (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpPure pe Q env interpEnv state)
    (result : Value × InterpState)
    (heval : ((evalPexpr defaultPexprFuel env pe).run interpEnv).run state = Except.ok result) :
    Q result.1 result.2 :=
  wpPureN_post defaultPexprFuel pe Q env interpEnv state h result heval

/-! ## WP Rules for Pure Expression Constructors

These lemmas characterize the WP for each pure expression form.
They allow compositional reasoning.
-/

/-- WP for value literals (fuel-indexed): postcondition must hold for the literal -/
theorem wpPureN_val (fuel : Nat) (v : Value) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN (fuel + 1) ⟨[], none, .val v⟩ Q env interpEnv state ↔ Q v state := by
  unfold wpPureN evalPexpr
  simp only []
  constructor <;> intro h <;> exact h

/-- WP for value literals: postcondition must hold for the literal -/
theorem wpPure_val (v : Value) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpPure ⟨[], none, .val v⟩ Q env interpEnv state ↔ Q v state := by
  unfold wpPure
  -- defaultPexprFuel = 100000 = 99999 + 1
  have h : defaultPexprFuel = 99999 + 1 := rfl
  rw [h]
  exact wpPureN_val 99999 v Q env interpEnv state

/-! ## WP for Effectful Expressions

Effectful expressions (Expr) can modify memory state. Their WP must account
for state changes.

Note: The full WP for effectful expressions requires tracking how
`runExprToValue` transforms state. This is more complex and will be
developed incrementally.
-/

/-- Weakest precondition for effectful expression evaluation (simplified).

    This is a simplified version that doesn't track state changes properly.
    A full version would need to reason about the step function.
-/
def wpExpr (e : AExpr) (Q : ExprPost) (file : File) (interpEnv : InterpEnv)
    (state : InterpState) : Prop :=
  match ((runExprToValue e [] file).run interpEnv).run state with
  | .ok (v, state') => Q v state'
  | .error (.undefinedBehavior _ _) => False
  | .error _ => True

/-! ## Memory Operation WP

WP rules for memory actions that can cause UB.
-/

/-- WP for store operation: pointer must be valid and writable -/
def wpStore (ptr : PointerValue) (state : InterpState) : Prop :=
  ValidPointer ptr state.memory
  -- Additional conditions: alignment, type compatibility would go here

/-- WP for load operation: pointer must be valid and initialized -/
def wpLoad (ptr : PointerValue) (state : InterpState) : Prop :=
  ValidInitializedPointer ptr state.memory
  -- The loaded value would need to satisfy Q

/-! ## Example: Proving Simple Properties

Demonstrate how to use the WP calculus to prove UB-freeness.
-/

/-- Create an integer value for examples -/
def mkIntVal (n : Int) : Value :=
  .object (.integer ⟨n, .none⟩)

/-- Example: literal 5 is UB-free and returns the expected value -/
example : wpPure ⟨[], none, .val (mkIntVal 5)⟩
    (fun v _ => v = mkIntVal 5)
    [] default default := by
  simp only [wpPure_val]

/-- Example: literal true is UB-free -/
example : wpPure ⟨[], none, .val Value.true_⟩ (fun _ _ => True) [] default default := by
  simp only [wpPure_val]

/-- Example: unit is UB-free -/
example : wpPure ⟨[], none, .val Value.unit⟩ (fun v _ => v = Value.unit) [] default default := by
  simp only [wpPure_val]

/-! ### Concrete WP Examples

These examples demonstrate that the WP infrastructure works correctly
by computing specific cases. They serve as sanity checks and show how
the WP calculus will be used in practice.
-/

/-- Example: if true then 1 else 2 is UB-free (evaluates without UB)

    This example verifies that `wpPureN` correctly computes for concrete
    expressions. Uses small fuel (10) for fast reduction.
-/
example : wpPureN 10 ⟨[], none, .if_ (.val .true_) (.val (mkIntVal 1)) (.val (mkIntVal 2))⟩
    (fun _ _ => True) [] default default := by
  -- Unfold and let Lean reduce the computation
  simp only [wpPureN, evalPexpr, mkAPexpr, bind, pure,
    ReaderT.bind, ReaderT.pure, ReaderT.run,
    StateT.bind, StateT.pure, StateT.run,
    Except.bind, Except.pure]

/-- Example: if false then 1 else 2 is UB-free -/
example : wpPureN 10 ⟨[], none, .if_ (.val .false_) (.val (mkIntVal 1)) (.val (mkIntVal 2))⟩
    (fun _ _ => True) [] default default := by
  simp only [wpPureN, evalPexpr, mkAPexpr, bind, pure,
    ReaderT.bind, ReaderT.pure, ReaderT.run,
    StateT.bind, StateT.pure, StateT.run,
    Except.bind, Except.pure]

/-! ## Compositional Rules (Fuel-Indexed)

These rules enable modular reasoning about WP. They are fuel-indexed
because `evalPexpr (fuel + 1)` for compound expressions uses `evalPexpr fuel`
for subexpressions.

The key insight is that `evalPexpr` is structured as:
```
evalPexpr (fuel + 1) env pe = match pe.expr with
  | .val v => pure v
  | .if_ cond then_ else_ =>
      evalPexpr fuel env cond >>= fun cv =>
        if cv = true_ then evalPexpr fuel env then_
        else if cv = false_ then evalPexpr fuel env else_
        else error
  ...
```

This structure means the WP for a compound expression relates to the WP
of its subexpressions with one less fuel.

Note: The proofs below use `sorry` because the current proof approach
(unfolding `evalPexpr` and case splitting) doesn't work well with Lean's
definitional equality checking for large mutual recursive functions.

A better approach would be to define `evalPexpr` using well-founded recursion
in a way that enables definitional unfolding, or to prove these lemmas
using a relational characterization of evaluation.
-/

/-- Helper: mkAPexpr equals the struct literal -/
theorem mkAPexpr_eq (e : Pexpr) : mkAPexpr e = ⟨[], none, e⟩ := rfl

/-- Helper: Except.bind on error -/
@[simp] theorem Except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

/-- Helper: Except.bind on ok -/
@[simp] theorem Except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- Monad bind distribution for InterpM through .run.run

    This lemma shows how bind distributes through running the monad transformers.
    Key insight: (m >>= f).run env).run state decomposes based on m's result.
-/
theorem InterpM_bind_run {α β : Type} (m : InterpM α) (f : α → InterpM β)
    (env : InterpEnv) (state : InterpState) :
    ((m >>= f).run env).run state =
    match (m.run env).run state with
    | .ok (v, s') => ((f v).run env).run s'
    | .error e => .error e := by
  simp only [bind, ReaderT.bind, StateT.bind, ReaderT.run, StateT.run]
  -- After simp, LHS is: (m env state).bind (fun (v, s') => f v env s')
  -- RHS is: match m env state with | ok (v,s') => f v env s' | error e => error e
  -- Split on m env state and substitute
  split
  · -- ok case: have heq : m env state = ok (v, s')
    rename_i v s' heq
    simp only [heq, Except.bind]
  · -- error case: have heq : m env state = error e
    rename_i e heq
    simp only [heq, Except.bind]

/-- WP for conditionals (fuel-indexed): requires WP for condition, then appropriate branch. -/
theorem wpPureN_if (fuel : Nat) (cond then_ else_ : Pexpr) (Q : PurePost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN (fuel + 1) ⟨[], none, .if_ cond then_ else_⟩ Q env interpEnv state ↔
    wpPureN fuel ⟨[], none, cond⟩ (fun v s =>
      match v with
      | .true_ => wpPureN fuel ⟨[], none, then_⟩ Q env interpEnv s
      | .false_ => wpPureN fuel ⟨[], none, else_⟩ Q env interpEnv s
      | _ => True  -- Type error, not UB
    ) env interpEnv state := by
  -- Unfold wpPureN on both sides
  simp only [wpPureN]
  -- Rewrite LHS using the evalPexpr equation lemma
  rw [evalPexpr_if']
  simp only [mkAPexpr_eq]
  -- Use bind distribution lemma to decompose the LHS
  rw [InterpM_bind_run]
  -- Now both sides have: match (evalPexpr cond).run.run with | ok => ... | error => ...
  -- Prove equivalence by case splitting
  constructor
  · -- Forward direction
    intro h
    cases hcond : ((evalPexpr fuel env ⟨[], none, cond⟩).run interpEnv).run state with
    | error e =>
      simp only [hcond] at h ⊢
      cases e with
      | undefinedBehavior _ _ => exact h
      | _ => trivial
    | ok p =>
      obtain ⟨condVal, state'⟩ := p
      simp only [hcond] at h ⊢
      cases condVal with
      | true_ => exact h
      | false_ => exact h
      | _ => trivial
  · -- Backward direction
    intro h
    cases hcond : ((evalPexpr fuel env ⟨[], none, cond⟩).run interpEnv).run state with
    | error e =>
      simp only [hcond] at h ⊢
      cases e with
      | undefinedBehavior _ _ => exact h
      | _ => trivial
    | ok p =>
      obtain ⟨condVal, state'⟩ := p
      simp only [hcond] at h ⊢
      cases condVal with
      | true_ => exact h
      | false_ => exact h
      | _ => trivial

/-- WP for let binding (fuel-indexed): WP of e1, then WP of e2 with bindings. -/
theorem wpPureN_let (fuel : Nat) (pat : APattern) (e1 e2 : Pexpr) (Q : PurePost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN (fuel + 1) ⟨[], none, .let_ pat e1 e2⟩ Q env interpEnv state ↔
    wpPureN fuel ⟨[], none, e1⟩ (fun v1 s =>
      match matchPattern pat v1 with
      | some bindings => wpPureN fuel ⟨[], none, e2⟩ Q (bindAllInEnv bindings env) interpEnv s
      | none => True  -- Pattern match failure, not UB
    ) env interpEnv state := by
  simp only [wpPureN]
  rw [evalPexpr_let']
  simp only [mkAPexpr_eq]
  -- Use bind distribution lemma
  rw [InterpM_bind_run]
  -- Now both sides have the same structure
  constructor
  · -- Forward direction
    intro h
    cases he1 : ((evalPexpr fuel env ⟨[], none, e1⟩).run interpEnv).run state with
    | error e =>
      simp only [he1] at h ⊢
      cases e with
      | undefinedBehavior _ _ => exact h
      | _ => trivial
    | ok p =>
      obtain ⟨v1, state'⟩ := p
      simp only [he1] at h ⊢
      cases hpat : matchPattern pat v1 with
      | none =>
        simp only [hpat] at h ⊢
        -- h : True, goal reduces to True after throw unfolds
      | some bindings =>
        simp only [hpat] at h ⊢
        exact h
  · -- Backward direction
    intro h
    cases he1 : ((evalPexpr fuel env ⟨[], none, e1⟩).run interpEnv).run state with
    | error e =>
      simp only [he1] at h ⊢
      cases e with
      | undefinedBehavior _ _ => exact h
      | _ => trivial
    | ok p =>
      obtain ⟨v1, state'⟩ := p
      simp only [he1] at h ⊢
      cases hpat : matchPattern pat v1 with
      | none =>
        -- Goal: match (throw patternMatchFailed).run ... with ... = True
        -- throw e unfolds to Except.error e, which matches the non-UB error case
        simp only [throw, throwThe, MonadExcept.throw, ReaderT.run, StateT.run]
        trivial
      | some bindings =>
        simp only [hpat] at h ⊢
        exact h

/-- WP for binary operations (fuel-indexed): first operand must be UB-free. -/
theorem wpPureN_binop_implies_e1 (fuel : Nat) (op : Binop) (e1 e2 : Pexpr) (Q : PurePost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN (fuel + 1) ⟨[], none, .op op e1 e2⟩ Q env interpEnv state →
    wpPureN fuel ⟨[], none, e1⟩ (fun _ _ => True) env interpEnv state := by
  intro h
  simp only [wpPureN] at h ⊢
  rw [evalPexpr_op'] at h
  simp only [mkAPexpr_eq] at h
  -- Use bind distribution lemma to decompose LHS
  rw [InterpM_bind_run] at h
  cases he1 : ((evalPexpr fuel env ⟨[], none, e1⟩).run interpEnv).run state with
  | error e =>
    -- e1 failed - h has this error result
    simp only [he1] at h ⊢
    cases e with
    | undefinedBehavior _ _ => exact h
    | _ => trivial
  | ok p =>
    -- e1 succeeded - goal is True
    trivial

end CToLean.Theorems.WP
