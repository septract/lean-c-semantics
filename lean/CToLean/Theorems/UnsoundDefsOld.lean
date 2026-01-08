import CToLean.Theorems.UBFree
import CToLean.Semantics.Eval
import CToLean.Semantics.Step
import Std.Data.HashMap

/-!
# UNSOUND Definitions - DO NOT USE FOR VERIFICATION

**WARNING: This file contains definitions that are NOT connected to the interpreter.**

These definitions were moved here because they are UNSOUND for verification purposes:
- They are syntactic definitions on the AST
- They have NO proven connection to what the interpreter actually does
- Using them for "verification" proves nothing about program behavior

They are kept for reference only. Do not use them for actual verification work.

See CLAUDE.md section 0.5 and docs/VERIFICATION_PLAN.md for the soundness requirements.

## Why These Are Unsound

1. `wpExprN` is defined structurally by pattern matching on the AST, NOT by
   running the interpreter. There is no theorem showing that `wpExprN` implies
   the interpreter doesn't produce UB.

2. `wpExprWithContsN` has the same problem.

3. `isKnownSafeFunction` is an ungrounded assertion that certain functions are
   safe. It says nothing about what the interpreter actually does.

## What Would Make Them Sound

To be sound, we would need to prove theorems like:
```lean
theorem wpExprN_sound :
  wpExprN fuel e Q env interpEnv state →
  ¬isUBResult ((runExprToValue e ...).run.run state)
```

Such proofs would require showing that each case of the structural definition
corresponds to the actual interpreter behavior.
-/

namespace CToLean.Theorems.UnsoundDefsOld

open CToLean.Core
open CToLean.Semantics
open CToLean.Memory
open Std (HashMap)

/-! ## UNSOUND: Known Safe Functions

This is an ungrounded assertion. It claims certain functions are safe
without proving anything about the interpreter.
-/

/-- UNSOUND: Predicate claiming a function is UB-free for any arguments.
    This is NOT proven against the interpreter. DO NOT USE. -/
def isKnownSafeFunction (name : String) : Bool :=
  name ∈ [
    "conv_loaded_int",
    "conv_int",
    "wrapI",
    "is_signed",
    "is_unsigned",
    "is_representable_integer"
  ]

/-! ## UNSOUND: Structural WP for Effectful Expressions

These definitions are NOT connected to the interpreter.
They pattern match on AST structure without proving correspondence to execution.
-/

/-- Postcondition for effectful expressions -/
abbrev ExprPost := Value → InterpState → Prop

/-- Postcondition for pure expressions -/
abbrev PurePost := Value → InterpState → Prop

/-- UNSOUND: Structurally-defined WP for effectful expressions.

    This is NOT proven to correspond to interpreter behavior.
    DO NOT USE for actual verification. -/
def wpExprN (fuel : Nat) (e : AExpr) (Q : ExprPost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) : Prop :=
  match fuel with
  | 0 => True
  | fuel' + 1 =>
    match e.expr with
    | .pure pe =>
        match ((evalPexpr fuel' env pe).run interpEnv).run state with
        | .ok (v, s') => Q v s'
        | .error (.undefinedBehavior _ _) => False
        | .error _ => True
    | .sseq pat e1 e2 =>
        wpExprN fuel' e1 (fun v1 s1 =>
          match matchPattern pat v1 with
          | some bindings => wpExprN fuel' e2 Q (bindAllInEnv bindings env) interpEnv s1
          | none => True
        ) env interpEnv state
    | .wseq pat e1 e2 =>
        wpExprN fuel' e1 (fun v1 s1 =>
          match matchPattern pat v1 with
          | some bindings => wpExprN fuel' e2 Q (bindAllInEnv bindings env) interpEnv s1
          | none => True
        ) env interpEnv state
    | .bound e' => wpExprN fuel' e' Q env interpEnv state
    | .if_ cond e1 e2 =>
        match ((evalPexpr fuel' env cond).run interpEnv).run state with
        | .ok (v, s) =>
          match v with
          | .true_ => wpExprN fuel' e1 Q env interpEnv s
          | .false_ => wpExprN fuel' e2 Q env interpEnv s
          | _ => True
        | .error (.undefinedBehavior _ _) => False
        | .error _ => True
    | .let_ pat pe body =>
        match ((evalPexpr fuel' env pe).run interpEnv).run state with
        | .ok (v, s) =>
          match matchPattern pat v with
          | some bindings => wpExprN fuel' body Q (bindAllInEnv bindings env) interpEnv s
          | none => True
        | .error (.undefinedBehavior _ _) => False
        | .error _ => True
    | .memop _ _ => True
    | .action _ => True
    | .case_ _ _ => True
    | .ccall _ _ _ => True
    | .proc _ _ => True
    | .unseq _ => True
    | .nd _ => True
    | .save _ _ _ _ => True
    | .run _ _ => True
    | .par _ => True
    | .wait _ => True

/-- UNSOUND: Structurally-defined WP with continuation tracking.

    This is NOT proven to correspond to interpreter behavior.
    DO NOT USE for actual verification. -/
def wpExprWithContsN (fuel : Nat) (conts : LabeledConts) (e : AExpr) (Q : ExprPost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) : Prop :=
  match fuel with
  | 0 => True
  | fuel' + 1 =>
    match e.expr with
    | .pure pe =>
        match ((evalPexpr fuel' env pe).run interpEnv).run state with
        | .ok (v, s') => Q v s'
        | .error (.undefinedBehavior _ _) => False
        | .error _ => True
    | .sseq pat e1 e2 =>
        wpExprWithContsN fuel' conts e1 (fun v1 s1 =>
          match matchPattern pat v1 with
          | some bindings => wpExprWithContsN fuel' conts e2 Q (bindAllInEnv bindings env) interpEnv s1
          | none => True
        ) env interpEnv state
    | .wseq pat e1 e2 =>
        wpExprWithContsN fuel' conts e1 (fun v1 s1 =>
          match matchPattern pat v1 with
          | some bindings => wpExprWithContsN fuel' conts e2 Q (bindAllInEnv bindings env) interpEnv s1
          | none => True
        ) env interpEnv state
    | .bound e' => wpExprWithContsN fuel' conts e' Q env interpEnv state
    | .if_ cond e1 e2 =>
        match ((evalPexpr fuel' env cond).run interpEnv).run state with
        | .ok (v, s) =>
          match v with
          | .true_ => wpExprWithContsN fuel' conts e1 Q env interpEnv s
          | .false_ => wpExprWithContsN fuel' conts e2 Q env interpEnv s
          | _ => True
        | .error (.undefinedBehavior _ _) => False
        | .error _ => True
    | .let_ pat pe body =>
        match ((evalPexpr fuel' env pe).run interpEnv).run state with
        | .ok (v, s) =>
          match matchPattern pat v with
          | some bindings => wpExprWithContsN fuel' conts body Q (bindAllInEnv bindings env) interpEnv s
          | none => True
        | .error (.undefinedBehavior _ _) => False
        | .error _ => True
    | .save sym _retTy symBTyPes body =>
        let paramSyms := symBTyPes.map fun (s, _, _) => s
        let cont : LabeledCont := { params := paramSyms, body := body }
        let conts' := conts.insert sym cont
        wpExprWithContsN fuel' conts' body Q env interpEnv state
    | .run sym _pes =>
        match conts[sym]? with
        | none => True
        | some labeledCont =>
            wpExprWithContsN fuel' conts labeledCont.body Q env interpEnv state
    | .memop _ _ => True
    | .action _ => True
    | .case_ _ _ => True
    | .ccall _ _ _ => True
    | .proc _ _ => True
    | .unseq _ => True
    | .nd _ => True
    | .par _ => True
    | .wait _ => True

/-! ## UNSOUND Theorems

These are tautologies about the unsound definitions above.
They prove nothing about actual program behavior.
-/

/-- UNSOUND: Tautology about wpExprN -/
theorem wpExprN_pure (fuel : Nat) (pe : APexpr) (Q : ExprPost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpExprN (fuel + 1) ⟨[], .pure pe⟩ Q env interpEnv state ↔
    match ((evalPexpr fuel env pe).run interpEnv).run state with
    | .ok (v, s') => Q v s'
    | .error (.undefinedBehavior _ _) => False
    | .error _ => True := by
  simp only [wpExprN]

/-- UNSOUND: Tautology about wpExprN -/
theorem wpExprN_bound (fuel : Nat) (e : AExpr) (Q : ExprPost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpExprN (fuel + 1) ⟨[], .bound e⟩ Q env interpEnv state ↔
    wpExprN fuel e Q env interpEnv state := by
  simp only [wpExprN]

/-- UNSOUND: Tautology about wpExprWithContsN -/
theorem wpExprWithContsN_pure (fuel : Nat) (conts : LabeledConts) (pe : APexpr) (Q : ExprPost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpExprWithContsN (fuel + 1) conts ⟨[], .pure pe⟩ Q env interpEnv state ↔
    match ((evalPexpr fuel env pe).run interpEnv).run state with
    | .ok (v, s') => Q v s'
    | .error (.undefinedBehavior _ _) => False
    | .error _ => True := by
  simp only [wpExprWithContsN]

/-- UNSOUND: Tautology about wpExprWithContsN -/
theorem wpExprWithContsN_bound (fuel : Nat) (conts : LabeledConts) (e : AExpr) (Q : ExprPost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpExprWithContsN (fuel + 1) conts ⟨[], .bound e⟩ Q env interpEnv state ↔
    wpExprWithContsN fuel conts e Q env interpEnv state := by
  simp only [wpExprWithContsN]

end CToLean.Theorems.UnsoundDefsOld
