/-
  CN Proof Obligations

  This module defines the proof obligation infrastructure for CN type checking.
  Instead of using a trusted oracle, type checking produces a list of obligations
  that must be discharged separately. This enables:
  - Foundational proofs (checked by Lean's kernel)
  - Multiple proof strategies (SMT, omega, manual proofs)
  - Proving CN type checking sound w.r.t. interpreter semantics

  ## Design: Value Constraints vs Heap Structure

  Obligations handle VALUE constraints only (pointer equality, arithmetic, etc.).
  Heap structure is handled separately:

  1. **Resource tracking** (structural): Type checker maintains `List Resource`
  2. **Resource interpretation** (semantic): `interpResources` gives heap meaning
     - Separation/disjointness is encoded in the interpretation via ∃ over disjoint sub-heaps
  3. **Value obligations** (this module): Constraints like `p == q`, `x < 100`

  For example, having `Owned(p)` and `Owned(q)` doesn't generate an explicit
  "p and q are disjoint" obligation. Instead:
  - If p ≠ q: The resources occupy different heap fragments (by interpretation)
  - If p == q: Type checking would fail (double ownership)

  Pointer equality constraints (e.g., matching `Owned(r)` against `Owned(p)`)
  DO generate obligations: the constraint `r == p`.

  ## Soundness Sketch

  For the soundness theorem, we need to prove:

  ```
  theorem cn_soundness
      (result : TypeCheckResult)
      (h_success : result.success)
      (h_obligations : result.allObligations)
      : ∀ ρ heap,
          interpResources precondition.resources ρ heap →
          constraintSetToProp ρ precondition.constraints →
          ¬ hasUB (execute body ρ heap) ∧
          postconditionHolds ...
  ```

  Key lemmas needed:
  1. **Path Condition Lemma**: If execution reaches the point where obligation `ob`
     was generated with valuation ρ, then `constraintSetToProp ρ ob.assumptions`.
  2. **Obligation Discharge**: If `ob.toProp` holds, then for any ρ satisfying
     the assumptions, the constraint holds.
  3. **Resource Interpretation Lemmas**: Properties like "Owned(p) implies p valid"
     are lemmas about `interpResource`, not obligations.
  4. **Composition**: All obligations discharged + resources tracked correctly
     implies all runtime checks pass.

  ## TODO: Well-Formedness Assumption

  The soundness theorem requires a well-formedness condition:

  **Well-formedness**: All constraints in generated obligations are evaluable
  under any valuation that binds all variables in scope at that program point.

  Currently, if a term cannot be evaluated (denoteTerm returns none), the
  constraint is treated as False. This makes obligations vacuously true if
  assumptions are unevaluable. The well-formedness condition ensures this
  doesn't happen for properly type-checked programs.

  This should either:
  - Be stated as a precondition of the soundness theorem, OR
  - Be proved as a lemma about the type checker

  Audited: 2026-01-21 (new implementation for proof obligations)
-/

import CerbLean.CN.Types
import CerbLean.CN.Semantics.Heap
import CerbLean.CN.Semantics.Denote

namespace CerbLean.CN.Verification

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types
open CerbLean.CN.Semantics (Valuation constraintToProp constraintSetToProp)

/-! ## Obligation Categories

Categories help choose appropriate discharge strategies.
-/

/-- Categories of proof obligations.
    Each category suggests different discharge strategies. -/
inductive ObligationCategory where
  /-- Arithmetic obligations (use omega or smt) -/
  | arithmetic
  /-- Equality obligations (use rfl, simp, or smt) -/
  | equality
  /-- Resource matching obligations (use frame_derived and resource lemmas) -/
  | resourceMatch
  /-- Pointer-related obligations -/
  | pointer
  /-- Custom obligations needing manual proofs or specialized tactics -/
  | custom
  deriving Repr, BEq, Inhabited

instance : ToString ObligationCategory where
  toString
    | .arithmetic => "arithmetic"
    | .equality => "equality"
    | .resourceMatch => "resourceMatch"
    | .pointer => "pointer"
    | .custom => "custom"

/-! ## Proof Obligation Type

A proof obligation captures what needs to be proved, along with metadata
for error reporting and strategy selection.
-/

/-- A proof obligation produced by type checking.

    Obligations are accumulated during type checking and discharged afterward.
    This separation enables:
    - Post-hoc proof strategies (SMT, omega, manual)
    - Independence of obligation discharge (no backtracking)
    - Proving soundness of type checking

    Key insight: An obligation is an implication `assumptions → constraint`,
    universally quantified over all valuations. The assumptions capture the
    constraints that were in scope when the obligation was generated.

    The `toProp` function gives the semantic meaning:
    ∀ ρ : Valuation, (∀ a ∈ assumptions, a holds under ρ) → constraint holds under ρ

    This connects symbolic verification to concrete execution semantics. -/
structure Obligation where
  /-- Human-readable description of the obligation -/
  description : String
  /-- The symbolic constraint to prove -/
  constraint : LogicalConstraint
  /-- Assumptions in scope when this obligation was generated -/
  assumptions : LCSet
  /-- Source location for error reporting -/
  loc : Loc
  /-- Category for choosing discharge strategy -/
  category : ObligationCategory
  deriving Inhabited

namespace Obligation

/-- Create an arithmetic obligation -/
def arithmetic (desc : String) (lc : LogicalConstraint) (assumptions : LCSet) (loc : Loc) : Obligation :=
  { description := desc, constraint := lc, assumptions := assumptions, loc := loc, category := .arithmetic }

/-- Create an equality obligation -/
def equality (desc : String) (lc : LogicalConstraint) (assumptions : LCSet) (loc : Loc) : Obligation :=
  { description := desc, constraint := lc, assumptions := assumptions, loc := loc, category := .equality }

/-- Create a resource match obligation -/
def resourceMatch (desc : String) (lc : LogicalConstraint) (assumptions : LCSet) (loc : Loc) : Obligation :=
  { description := desc, constraint := lc, assumptions := assumptions, loc := loc, category := .resourceMatch }

/-- Create a pointer obligation -/
def pointer (desc : String) (lc : LogicalConstraint) (assumptions : LCSet) (loc : Loc) : Obligation :=
  { description := desc, constraint := lc, assumptions := assumptions, loc := loc, category := .pointer }

/-- Create a custom obligation -/
def custom (desc : String) (lc : LogicalConstraint) (assumptions : LCSet) (loc : Loc) : Obligation :=
  { description := desc, constraint := lc, assumptions := assumptions, loc := loc, category := .custom }

/-- Convert obligation to Prop.
    An obligation holds if: for all valuations, if all assumptions hold,
    then the constraint holds.

    This is the semantic meaning that connects symbolic verification
    to concrete execution. -/
def toProp (ob : Obligation) : Prop :=
  ∀ ρ : Valuation,
    constraintSetToProp ρ ob.assumptions →
    constraintToProp ρ ob.constraint

end Obligation

/-! ## Obligation Set

A set of obligations to be discharged.
-/

/-- A set of proof obligations -/
abbrev ObligationSet := List Obligation

namespace ObligationSet

def empty : ObligationSet := []

def add (ob : Obligation) (s : ObligationSet) : ObligationSet := ob :: s

def union (s1 s2 : ObligationSet) : ObligationSet := s1 ++ s2

/-- All obligations in the set hold.
    Each obligation is already universally quantified over valuations,
    so this doesn't take a valuation parameter. -/
def allSatisfied (s : ObligationSet) : Prop :=
  ∀ ob ∈ s, ob.toProp

/-- Filter obligations by category -/
def filterCategory (cat : ObligationCategory) (s : ObligationSet) : ObligationSet :=
  s.filter (·.category == cat)

end ObligationSet

/-! ## Type Check Result

The result of type checking includes success status and accumulated obligations.
-/

/-- Result of type checking a function or statement.

    Even if `success = true`, the obligations still need to be discharged
    for the program to be verified. Structural type checking succeeding
    only means the resources can be matched; the semantic constraints
    still need proofs. -/
structure TypeCheckResult where
  /-- Did structural type checking succeed? -/
  success : Bool
  /-- Proof obligations to discharge -/
  obligations : ObligationSet
  /-- Error message if success = false -/
  error : Option String
  deriving Inhabited

namespace TypeCheckResult

/-- All obligations hold.
    Each obligation is universally quantified over valuations. -/
def allObligations (r : TypeCheckResult) : Prop :=
  r.obligations.allSatisfied

/-- A successful result with no obligations -/
def ok : TypeCheckResult :=
  { success := true, obligations := [], error := none }

/-- A successful result with obligations -/
def okWithObligations (obs : ObligationSet) : TypeCheckResult :=
  { success := true, obligations := obs, error := none }

/-- A failed result -/
def fail (msg : String) : TypeCheckResult :=
  { success := false, obligations := [], error := some msg }

end TypeCheckResult

/-! ## Constraint to Obligation Conversion

Convert logical constraints to proof obligations.
Note: Constraints are kept symbolic; conversion to Prop happens at discharge time.
-/

/-- Convert a logical constraint to a proof obligation.
    Requires the current assumptions (constraints in scope). -/
def constraintToObligation
    (lc : LogicalConstraint)
    (assumptions : LCSet)
    (loc : Loc)
    (desc : String := "constraint") : Obligation :=
  { description := desc
  , constraint := lc
  , assumptions := assumptions
  , loc := loc
  , category := .arithmetic  -- Default; could be refined based on constraint structure
  }

/-- Convert a set of constraints to obligations.
    All obligations share the same assumptions (those in scope). -/
def constraintsToObligations
    (lcs : LCSet)
    (assumptions : LCSet)
    (loc : Loc) : ObligationSet :=
  lcs.map fun lc => constraintToObligation lc assumptions loc

/-! ## Obligation Discharge Helpers

These are placeholders for actual discharge tactics.
The real tactics will use SMT, omega, or manual proofs.

Note: Actual discharge produces proof terms of type `ob.prop`.
Since Props are first-class in Lean, we can store them in structures
and prove them later using tactics.
-/

/-- Check if an obligation can be trivially satisfied (for decidable props) -/
def Obligation.isTrivial (_ob : Obligation) : Bool :=
  -- This would need actual decidability; placeholder for now
  false

/-- Result of attempting to discharge an obligation -/
inductive DischargeResult where
  /-- Successfully proved -/
  | proved
  /-- Failed to prove -/
  | failed (reason : String)
  /-- Unknown (solver timed out, etc.) -/
  | unknown
  deriving Repr, BEq, Inhabited

/-- A discharge strategy attempts to prove obligations -/
structure DischargeStrategy where
  /-- Name of the strategy -/
  name : String
  /-- Try to discharge an obligation (returns result, not the proof itself) -/
  tryDischarge : Obligation → DischargeResult
  deriving Inhabited

namespace DischargeStrategy

/-- Strategy that always fails (placeholder) -/
def fail : DischargeStrategy where
  name := "fail"
  tryDischarge _ := .failed "no strategy available"

/-- Strategy that always succeeds (UNSOUND - for testing only) -/
def trustAll : DischargeStrategy where
  name := "trust_all"
  tryDischarge _ := .proved

end DischargeStrategy

end CerbLean.CN.Verification
