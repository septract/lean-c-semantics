import CToLean.Theorems.WP
import Std.Data.HashMap

/-!
# Verification Examples

This module demonstrates verifying Core IR ASTs for UB-freeness using the
WP calculus. These examples show what kinds of programs we can verify.

## Verification Capabilities

Currently we can verify:
1. **Pure expressions with literals**: Values, booleans, integers
2. **Conditionals**: `if-then-else` with concrete or symbolic conditions
3. **Nested expressions**: Arbitrary nesting of the above
4. **Symbolic reasoning**: Properties that hold for all inputs

## Limitations

Not yet supported:
- Let bindings with symbol lookup (require proper environment setup)
- Binary operations beyond literals (need `evalBinop` lemmas)
- Memory operations (need memory model integration)
- Loops (need invariant infrastructure)

## Proof Techniques

1. **Concrete verification**: Use `simp` with monad reduction lemmas and small fuel
2. **Symbolic verification**: Use compositional rules (`wpPureN_if`, etc.)
-/

namespace CToLean.Theorems.Examples

open CToLean.Core
open CToLean.Semantics
open CToLean.Memory
open CToLean.Theorems.WP
open Std (HashMap)

/-! ## Helper Definitions -/

/-- Create an integer value -/
def mkInt (n : Int) : Value :=
  .object (.integer ⟨n, .none⟩)

/-- Standard simp set for concrete WP proofs -/
macro "wp_simp" : tactic =>
  `(tactic| simp only [wpPureN, evalPexpr, mkAPexpr, bind, pure,
    ReaderT.bind, ReaderT.pure, ReaderT.run,
    StateT.bind, StateT.pure, StateT.run,
    Except.bind, Except.pure])

/-! ## Concrete Verification Examples

These examples verify specific Core ASTs by running the interpreter
with small fuel and checking the result.
-/

section ConcreteExamples

/-- Literal integer 42 is UB-free -/
example : wpPureN 10 ⟨[], none, .val (mkInt 42)⟩
    (fun _ _ => True) [] default default := by
  wp_simp

/-- Literal true is UB-free -/
example : wpPureN 10 ⟨[], none, .val .true_⟩
    (fun _ _ => True) [] default default := by
  wp_simp

/-- Literal false is UB-free -/
example : wpPureN 10 ⟨[], none, .val .false_⟩
    (fun _ _ => True) [] default default := by
  wp_simp

/-- Unit value is UB-free -/
example : wpPureN 10 ⟨[], none, .val .unit⟩
    (fun _ _ => True) [] default default := by
  wp_simp

/-- Simple conditional: if true then 1 else 2 -/
example : wpPureN 10 ⟨[], none, .if_ (.val .true_) (.val (mkInt 1)) (.val (mkInt 2))⟩
    (fun _ _ => True) [] default default := by
  wp_simp

/-- Simple conditional: if false then 1 else 2 -/
example : wpPureN 10 ⟨[], none, .if_ (.val .false_) (.val (mkInt 1)) (.val (mkInt 2))⟩
    (fun _ _ => True) [] default default := by
  wp_simp

/-- Nested conditional: if true then (if false then 1 else 2) else 3 -/
example : wpPureN 10 ⟨[], none,
    .if_ (.val .true_)
         (.if_ (.val .false_) (.val (mkInt 1)) (.val (mkInt 2)))
         (.val (mkInt 3))⟩
    (fun _ _ => True) [] default default := by
  wp_simp

/-- Deeply nested: if true then (if true then (if false then 1 else 2) else 3) else 4 -/
example : wpPureN 10 ⟨[], none,
    .if_ (.val .true_)
         (.if_ (.val .true_)
               (.if_ (.val .false_) (.val (mkInt 1)) (.val (mkInt 2)))
               (.val (mkInt 3)))
         (.val (mkInt 4))⟩
    (fun _ _ => True) [] default default := by
  wp_simp

end ConcreteExamples

/-! ## Symbolic Verification Examples

These examples use the compositional rules to prove properties that
hold for ALL possible subexpressions, not just concrete ones.
-/

section SymbolicExamples

/-- WP for literals just checks the postcondition on the value.
    This holds for ANY value v and postcondition Q. -/
theorem literal_wp (fuel : Nat) (v : Value) (Q : PurePost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN (fuel + 1) ⟨[], none, .val v⟩ Q env interpEnv state ↔ Q v state := by
  simp only [wpPureN, evalPexpr, pure, ReaderT.pure, ReaderT.run,
    StateT.pure, StateT.run, Except.pure]

/-- Any literal is UB-free (with trivial postcondition). -/
theorem literal_ubfree (fuel : Nat) (v : Value)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN (fuel + 1) ⟨[], none, .val v⟩ (fun _ _ => True) env interpEnv state := by
  rw [literal_wp]
  trivial

end SymbolicExamples

/-! ### Compositional Rules

The compositional rules from `WP.lean` allow symbolic reasoning about
expressions. Key rules include:

- `wpPureN_if`: WP for conditionals decomposes into condition + branches
- `wpPureN_let`: WP for let bindings decomposes into bound expression + body
- `wpPureN_binop_implies_e1`: Binary ops require first operand to be UB-free

These rules enable proving properties that hold for ALL possible
subexpressions, not just concrete ones.
-/

/-! ## Postcondition Verification

These examples show verifying not just UB-freeness but also
functional correctness (the result satisfies some property).
-/

section PostconditionExamples

/-- Literal 42 evaluates to exactly 42 -/
example : wpPureN 10 ⟨[], none, .val (mkInt 42)⟩
    (fun v _ => v = mkInt 42) [] default default := by
  wp_simp

/-- if true then 1 else 2 evaluates to 1 -/
example : wpPureN 10 ⟨[], none, .if_ (.val .true_) (.val (mkInt 1)) (.val (mkInt 2))⟩
    (fun v _ => v = mkInt 1) [] default default := by
  wp_simp

/-- if false then 1 else 2 evaluates to 2 -/
example : wpPureN 10 ⟨[], none, .if_ (.val .false_) (.val (mkInt 1)) (.val (mkInt 2))⟩
    (fun v _ => v = mkInt 2) [] default default := by
  wp_simp

end PostconditionExamples

end CToLean.Theorems.Examples
