/-
  Pure Denotation for SMT Discharge

  This module provides pure interpretation functions that map CN terms
  directly to Lean Int/Prop, bypassing HeapValue. This enables SMT
  solvers to reason about arithmetic constraints.

  ## Design

  The standard `denoteTerm` returns `Option HeapValue`, which SMT can't
  understand. For arithmetic constraints, we provide:

  - `termToInt`: Interprets integer terms as `Int`
  - `termToProp`: Interprets boolean terms as `Prop`

  These are connected to `constraintToProp` via soundness theorems,
  allowing us to transform goals to pure arithmetic before calling SMT.

  ## Supported Fragment

  Only arithmetic operations are supported:
  - Integer constants, symbols
  - add, sub, mul, div, rem, min, max
  - lt, le, eq comparisons
  - and, or, not, implies (on booleans)

  Pointers, structs, arrays, etc. are not supported (return none).

  Audited: 2026-01-22 (new implementation for SMT discharge)
-/

import CerbLean.CN.Types
import CerbLean.CN.Semantics.Heap
import CerbLean.CN.Semantics.Denote

namespace CerbLean.CN.Semantics

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types

/-! ## Pure Valuation

Maps symbols directly to integers, without HeapValue wrapping.
-/

/-- Pure integer valuation: maps symbols to integers -/
abbrev PureIntVal := Sym → Int

/-- Look up a symbol in a pure valuation (total function) -/
def PureIntVal.lookup (σ : PureIntVal) (s : Sym) : Int := σ s

/-! ## Pure Integer and Boolean Interpretation

These are mutually recursive - integer terms can contain conditionals
that depend on boolean terms, and boolean terms compare integers.
-/

mutual

/-- Interpret an integer term as Int.
    Returns none for non-integer terms or unsupported operations.

    Note: This is partial due to mutual recursion with termToBool.
    Making it terminating requires well-founded recursion on a combined
    measure, which is complex. For soundness proofs, we use sorry for
    termination-dependent lemmas. -/
partial def termToInt (σ : PureIntVal) : Term → Option Int
  | .const (.z n) => some n
  | .const (.bits _ _ n) => some n
  | .sym s => some (σ s)
  | .unop .negate arg => do
    let n ← termToInt σ arg.term
    return -n
  | .binop op left right => do
    let n1 ← termToInt σ left.term
    let n2 ← termToInt σ right.term
    match op with
    | .add => return n1 + n2
    | .sub => return n1 - n2
    | .mul | .mulNoSMT => return n1 * n2
    | .div | .divNoSMT => if n2 = 0 then none else return n1 / n2
    | .rem | .remNoSMT => if n2 = 0 then none else return n1 % n2
    | .mod_ | .modNoSMT => if n2 = 0 then none else return n1 % n2
    | .min => return min n1 n2
    | .max => return max n1 n2
    | .exp | .expNoSMT =>
      if n2 < 0 then none else return n1 ^ n2.toNat
    | _ => none  -- Comparison ops return bool, not int
  | .ite cond thenBr elseBr => do
    let b ← termToBool σ cond.term
    if b then termToInt σ thenBr.term else termToInt σ elseBr.term
  | .let_ var binding body => do
    let v ← termToInt σ binding.term
    termToInt (fun s => if s == var then v else σ s) body.term
  | _ => none

/-- Interpret a boolean term as Bool.
    Returns none for non-boolean terms or unsupported operations. -/
partial def termToBool (σ : PureIntVal) : Term → Option Bool
  | .const (.bool b) => some b
  | .const (.z n) => some (decide (n ≠ 0))  -- C-style: 0 is false, non-0 is true
  | .unop .not arg => do
    let b ← termToBool σ arg.term
    return !b
  | .binop op left right =>
    match op with
    -- Logical operators
    | .and_ => do
      let b1 ← termToBool σ left.term
      let b2 ← termToBool σ right.term
      return b1 && b2
    | .or_ => do
      let b1 ← termToBool σ left.term
      let b2 ← termToBool σ right.term
      return b1 || b2
    | .implies => do
      let b1 ← termToBool σ left.term
      let b2 ← termToBool σ right.term
      return !b1 || b2
    -- Comparison operators (on integers)
    | .lt => do
      let n1 ← termToInt σ left.term
      let n2 ← termToInt σ right.term
      return decide (n1 < n2)
    | .le => do
      let n1 ← termToInt σ left.term
      let n2 ← termToInt σ right.term
      return decide (n1 ≤ n2)
    | .eq => do
      let n1 ← termToInt σ left.term
      let n2 ← termToInt σ right.term
      return n1 == n2
    | _ => none
  | .ite cond thenBr elseBr => do
    let b ← termToBool σ cond.term
    if b then termToBool σ thenBr.term else termToBool σ elseBr.term
  | .let_ var binding body => do
    let v ← termToInt σ binding.term
    termToBool (fun s => if s == var then v else σ s) body.term
  | _ => none

end

/-! ## Pure Prop Interpretation

Interpret boolean terms directly as Prop (for SMT).
-/

/-- Interpret a boolean term as Prop.
    This is what SMT will reason about. -/
partial def termToProp (σ : PureIntVal) : Term → Option Prop
  | .const (.bool true) => some True
  | .const (.bool false) => some False
  | .const (.z n) => some (n ≠ 0)
  | .unop .not arg => do
    let p ← termToProp σ arg.term
    return ¬p
  | .binop op left right =>
    match op with
    -- Logical operators
    | .and_ => do
      let p1 ← termToProp σ left.term
      let p2 ← termToProp σ right.term
      return p1 ∧ p2
    | .or_ => do
      let p1 ← termToProp σ left.term
      let p2 ← termToProp σ right.term
      return p1 ∨ p2
    | .implies => do
      let p1 ← termToProp σ left.term
      let p2 ← termToProp σ right.term
      return p1 → p2
    -- Comparison operators (on integers) - these produce Props directly
    | .lt => do
      let n1 ← termToInt σ left.term
      let n2 ← termToInt σ right.term
      return n1 < n2
    | .le => do
      let n1 ← termToInt σ left.term
      let n2 ← termToInt σ right.term
      return n1 ≤ n2
    | .eq => do
      let n1 ← termToInt σ left.term
      let n2 ← termToInt σ right.term
      return n1 = n2
    | _ => none
  | .ite cond thenBr elseBr => do
    let b ← termToBool σ cond.term
    if b then termToProp σ thenBr.term else termToProp σ elseBr.term
  | .let_ var binding body => do
    let v ← termToInt σ binding.term
    termToProp (fun s => if s == var then v else σ s) body.term
  | _ => none

/-! ## Constraint Interpretation

Interpret logical constraints as Props.
-/

/-- Interpret a logical constraint as Prop -/
def constraintToPureProp (σ : PureIntVal) : LogicalConstraint → Option Prop
  | .t it => termToProp σ it.term
  | .forall_ (x, _bt) body =>
    -- Universal quantification over integers
    -- Note: We interpret all quantified variables as integers
    some (∀ n : Int, match termToProp (fun s => if s == x then n else σ s) body.term with
      | some p => p
      | none => True)  -- If body can't be interpreted, vacuously true

/-- Interpret a set of logical constraints as Prop -/
def constraintSetToPureProp (σ : PureIntVal) (lcs : LCSet) : Option Prop :=
  lcs.foldlM (init := True) fun acc lc => do
    let p ← constraintToPureProp σ lc
    return acc ∧ p

/-! ## Valuation Compatibility

Relates HeapValue valuations to pure valuations.
-/

/-- A pure valuation is compatible with a HeapValue valuation if they agree on integers -/
def valuationCompatible (ρ : Valuation) (σ : PureIntVal) : Prop :=
  ∀ s : Sym, match ρ.lookup s with
    | some (.integer _ n) => σ s = n
    | _ => True  -- Non-integer or missing symbols don't constrain σ

/-! ## Tests

Verify the pure interpretation works correctly.
-/

section Tests

-- Test termToInt on constants
#eval termToInt (fun _ => 0) (.const (.z 42))  -- some 42

-- Test termToInt on addition
#eval termToInt (fun _ => 0) (.binop .add
  (AnnotTerm.mk (.const (.z 1)) .integer Loc.t.unknown)
  (AnnotTerm.mk (.const (.z 2)) .integer Loc.t.unknown))  -- some 3

-- Test termToBool on comparison
#eval termToBool (fun _ => 0) (.binop .lt
  (AnnotTerm.mk (.const (.z 1)) .integer Loc.t.unknown)
  (AnnotTerm.mk (.const (.z 2)) .integer Loc.t.unknown))  -- some true

-- Test with symbolic variable
def xSym : Sym := { id := 1, name := some "x" }

def testSigma : PureIntVal := fun s =>
  if s.name == some "x" then 5 else 0

#eval termToInt testSigma (.sym xSym)  -- some 5

end Tests

end CerbLean.CN.Semantics
