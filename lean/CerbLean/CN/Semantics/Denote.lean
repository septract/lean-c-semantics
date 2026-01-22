/-
  CN Index Term Denotation
  Corresponds to: semantic evaluation of CN index terms

  This module provides:
  - denote: Evaluate an index term to a concrete value
  - constraintToProp: Convert logical constraints to Props

  The denotation gives meaning to CN's specification language by mapping
  symbolic terms to concrete values in a valuation.

  Audited: 2026-01-21 (new implementation for proof obligations)
-/

import CerbLean.CN.Types
import CerbLean.CN.Semantics.Heap

namespace CerbLean.CN.Semantics

open CerbLean.Core (Sym Loc Ctype IntegerType)
open CerbLean.CN.Types

/-! ## Value Operations

Helper functions for computing with HeapValues.
-/

/-- Default integer type for boolean results -/
def defaultIntType : IntegerType := .signed .int_

/-- Extract an integer from a HeapValue -/
def heapValueAsInt : HeapValue → Option Int
  | .integer _ n => some n
  | _ => none

/-- Extract a boolean from a HeapValue (0 = false, non-0 = true) -/
def heapValueAsBool : HeapValue → Option Bool
  | .integer _ n => some (n ≠ 0)
  | _ => none

/-- Create a boolean HeapValue -/
def boolToHeapValue (b : Bool) : HeapValue :=
  .integer defaultIntType (if b then 1 else 0)

/-- Create an integer HeapValue -/
def intToHeapValue (ity : IntegerType) (n : Int) : HeapValue :=
  .integer ity n

/-- Check if a HeapValue represents true (non-zero integer) -/
def heapValueIsTrue : HeapValue → Prop
  | .integer _ n => n ≠ 0
  | _ => False

/-! ## Constant Denotation

Maps CN constants to HeapValues.
-/

/-- Denote a constant as a HeapValue -/
def denoteConst : Const → Option HeapValue
  | .z n => some (.integer defaultIntType n)
  | .bits sign width n =>
    let ity := if sign == .signed then IntegerType.signed (.intN width) else IntegerType.unsigned (.intN width)
    some (.integer ity n)
  | .bool b => some (boolToHeapValue b)
  | .unit => some (.integer defaultIntType 0)  -- Unit as 0
  | .null => some (.pointer none)
  | .pointer ptr => some (.pointer (some ⟨ptr.allocId.toNat, ptr.addr.toNat⟩))
  | .allocId id => some (.integer defaultIntType id)
  | .q _ _ => none  -- Rationals not supported for concrete evaluation
  | .memByte _ => none  -- Memory bytes need more context
  | .ctypeConst _ => none  -- C types are not runtime values
  | .default _ => none  -- Default values are symbolic

/-! ## Binary Operation Denotation

Evaluates binary operations on HeapValues.
-/

/-- Integer division that matches C semantics (truncated toward zero) -/
def intDivTrunc (a b : Int) : Int :=
  if b = 0 then 0  -- Division by zero returns 0 (handled elsewhere)
  else a / b

/-- Integer remainder that matches C semantics -/
def intRemTrunc (a b : Int) : Int :=
  if b = 0 then 0
  else a % b

/-- Evaluate a binary operation -/
def denoteBinOp (op : BinOp) (v1 v2 : HeapValue) : Option HeapValue :=
  match op with
  -- Logical operators (on integers representing booleans)
  | .and_ => do
    let b1 ← heapValueAsBool v1
    let b2 ← heapValueAsBool v2
    return boolToHeapValue (b1 && b2)
  | .or_ => do
    let b1 ← heapValueAsBool v1
    let b2 ← heapValueAsBool v2
    return boolToHeapValue (b1 || b2)
  | .implies => do
    let b1 ← heapValueAsBool v1
    let b2 ← heapValueAsBool v2
    return boolToHeapValue (!b1 || b2)

  -- Arithmetic operators
  | .add => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    return HeapValue.integer ty1 (n1 + n2)
  | .sub => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    return HeapValue.integer ty1 (n1 - n2)
  | .mul | .mulNoSMT => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    return HeapValue.integer ty1 (n1 * n2)
  | .div | .divNoSMT => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    if n2 = 0 then none  -- Division by zero is undefined
    else return HeapValue.integer ty1 (intDivTrunc n1 n2)
  | .rem | .remNoSMT => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    if n2 = 0 then none
    else return HeapValue.integer ty1 (intRemTrunc n1 n2)
  | .mod_ | .modNoSMT => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    if n2 = 0 then none
    else return HeapValue.integer ty1 (n1 % n2)
  | .exp | .expNoSMT => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    if n2 < 0 then none  -- Negative exponent not supported for integers
    else return HeapValue.integer ty1 (n1 ^ n2.toNat)
  | .min => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    return HeapValue.integer ty1 (min n1 n2)
  | .max => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    return HeapValue.integer ty1 (max n1 n2)

  -- Comparison operators
  | .lt => do
    let HeapValue.integer _ n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    return boolToHeapValue (n1 < n2)
  | .le => do
    let HeapValue.integer _ n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    return boolToHeapValue (n1 ≤ n2)
  | .eq => do
    -- Equality works for integers and pointers
    match v1, v2 with
    | HeapValue.integer _ n1, HeapValue.integer _ n2 => return boolToHeapValue (n1 == n2)
    | HeapValue.pointer p1, HeapValue.pointer p2 => return boolToHeapValue (p1 == p2)
    | _, _ => none

  -- Pointer comparison operators
  | .ltPointer => do
    let HeapValue.pointer (some loc1) := v1 | none
    let HeapValue.pointer (some loc2) := v2 | none
    if loc1.allocId ≠ loc2.allocId then none  -- Undefined: comparing pointers from different allocations
    else return boolToHeapValue (loc1.addr < loc2.addr)
  | .lePointer => do
    let HeapValue.pointer (some loc1) := v1 | none
    let HeapValue.pointer (some loc2) := v2 | none
    if loc1.allocId ≠ loc2.allocId then none
    else return boolToHeapValue (loc1.addr ≤ loc2.addr)

  -- Bitwise operators
  -- Note: Int doesn't have built-in bitwise operations; use Nat operations via toNat
  -- These are only correct for non-negative integers; negative integer bitwise ops are complex
  | .bwAnd => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    if n1 < 0 || n2 < 0 then none  -- Negative bitwise not supported
    else return HeapValue.integer ty1 (Int.ofNat (n1.toNat &&& n2.toNat))
  | .bwOr => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    if n1 < 0 || n2 < 0 then none
    else return HeapValue.integer ty1 (Int.ofNat (n1.toNat ||| n2.toNat))
  | .bwXor => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    if n1 < 0 || n2 < 0 then none
    else return HeapValue.integer ty1 (Int.ofNat (n1.toNat ^^^ n2.toNat))
  | .shiftLeft => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    if n1 < 0 || n2 < 0 then none
    else return HeapValue.integer ty1 (Int.ofNat (n1.toNat <<< n2.toNat))
  | .shiftRight => do
    let HeapValue.integer ty1 n1 := v1 | none
    let HeapValue.integer _ n2 := v2 | none
    if n1 < 0 || n2 < 0 then none
    else return HeapValue.integer ty1 (Int.ofNat (n1.toNat >>> n2.toNat))

  -- Set operators - not supported for concrete evaluation
  | .setUnion | .setIntersection | .setDifference | .setMember | .subset => none

/-- Evaluate a unary operation -/
def denoteUnOp (op : UnOp) (v : HeapValue) : Option HeapValue :=
  match op with
  | .not => do
    let b ← heapValueAsBool v
    return boolToHeapValue (!b)
  | .negate => do
    let HeapValue.integer ty n := v | none
    return HeapValue.integer ty (-n)
  | .bwCompl => do
    let HeapValue.integer ty n := v | none
    -- Bitwise complement: depends on width, but for unbounded integers we can't do this properly
    -- For now, return the logical complement assuming two's complement
    return HeapValue.integer ty (-(n + 1))
  -- These are marked NoSMT because they're uninterpreted
  | .bwClzNoSMT | .bwCtzNoSMT | .bwFfsNoSMT | .bwFlsNoSMT => none

/-! ## Term Denotation

Evaluate index terms to concrete values.
-/

/-- Evaluate an index term given a valuation.
    Returns None if the term cannot be evaluated (e.g., free variables, unsupported operations). -/
partial def denoteTerm (ρ : Valuation) : Term → Option HeapValue
  | .const c => denoteConst c
  | .sym s => ρ.lookup s
  | .unop op arg => do
    let v ← denoteTerm ρ arg.term
    denoteUnOp op v
  | .binop op left right => do
    let v1 ← denoteTerm ρ left.term
    let v2 ← denoteTerm ρ right.term
    denoteBinOp op v1 v2
  | .ite cond thenBr elseBr => do
    let condVal ← denoteTerm ρ cond.term
    let b ← heapValueAsBool condVal
    if b then denoteTerm ρ thenBr.term else denoteTerm ρ elseBr.term
  | .tuple elems => do
    -- Tuples are not directly representable as HeapValue
    -- For now, only support single-element tuples (projection)
    match elems with
    | [e] => denoteTerm ρ e.term
    | _ => none
  | .nthTuple _ _ =>
    -- Would need tuple value representation
    none
  | .struct_ tag members => do
    let fields ← members.mapM fun (id, val) => do
      let v ← denoteTerm ρ val.term
      return (id, v)
    return HeapValue.struct_ tag fields
  | .structMember obj member => do
    let HeapValue.struct_ _ fields := (← denoteTerm ρ obj.term) | none
    fields.find? (fun (id, _) => id == member) |>.map (·.2)
  | .nil _ => none  -- Lists not supported in concrete evaluation
  | .cons _ _ => none
  | .head _ => none
  | .tail _ => none
  | .let_ var binding body => do
    let v ← denoteTerm ρ binding.term
    denoteTerm ((var, v) :: ρ) body.term
  | .cast _ val => denoteTerm ρ val.term  -- Casts are no-ops for concrete values
  -- Most other constructs are not supported for concrete evaluation
  | _ => none

/-- Evaluate an annotated index term -/
def denoteAnnotTerm (ρ : Valuation) (t : AnnotTerm) : Option HeapValue :=
  denoteTerm ρ t.term

/-- Alias for IndexTerm -/
abbrev denoteIndexTerm := denoteAnnotTerm

/-! ## Logical Constraint Conversion

Convert logical constraints to propositions.
-/

/-- Convert a logical constraint to a Prop.
    The constraint is satisfied if the index term evaluates to true. -/
def constraintToProp (ρ : Valuation) : LogicalConstraint → Prop
  | .t it =>
    match denoteAnnotTerm ρ it with
    | some v => heapValueIsTrue v
    | none => False  -- Cannot evaluate → not satisfied
  | .forall_ (x, _) body =>
    -- Universally quantified: for all values of type bt, body is true
    -- This is a semantic universal quantification
    ∀ v : HeapValue,
      match denoteAnnotTerm ((x, v) :: ρ) body with
      | some hv => heapValueIsTrue hv
      | none => False

/-- Convert a set of logical constraints to a single Prop -/
def constraintSetToProp (ρ : Valuation) (lcs : LCSet) : Prop :=
  ∀ lc ∈ lcs, constraintToProp ρ lc

/-! ## Decidable Evaluation

For concrete evaluation, we can provide decidable procedures.
-/

/-- Check if a term evaluates to true (decidable) -/
def evalTermTrue (ρ : Valuation) (t : Term) : Bool :=
  match denoteTerm ρ t with
  | some (HeapValue.integer _ n) => n ≠ 0
  | _ => false

/-- Check if an index term evaluates to true (decidable) -/
def evalIndexTermTrue (ρ : Valuation) (t : IndexTerm) : Bool :=
  evalTermTrue ρ t.term

/-- Check if a logical constraint is satisfied (decidable, only for ground constraints) -/
def evalConstraint (ρ : Valuation) : LogicalConstraint → Bool
  | .t it => evalIndexTermTrue ρ it
  | .forall_ _ _ => false  -- Cannot decide universal quantification

/-- Check if all constraints in a set are satisfied (decidable, only for ground constraints) -/
def evalConstraintSet (ρ : Valuation) (lcs : LCSet) : Bool :=
  lcs.all (evalConstraint ρ)

end CerbLean.CN.Semantics
