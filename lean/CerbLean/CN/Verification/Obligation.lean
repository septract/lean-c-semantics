/-
  CN Proof Obligations

  This module defines the proof obligation infrastructure for CN type checking.
  Type checking produces a list of obligations that are discharged by an
  external SMT solver.

  ## Design: Value Constraints vs Heap Structure

  Obligations handle VALUE constraints only (pointer equality, arithmetic, etc.).
  Heap structure is handled separately:

  1. **Resource tracking** (structural): Type checker maintains `List Resource`
  2. **Value obligations** (this module): Constraints like `p == q`, `x < 100`

  For example, having `Owned(p)` and `Owned(q)` doesn't generate an explicit
  "p and q are disjoint" obligation. Instead:
  - If p ≠ q: The resources occupy different heap fragments (by interpretation)
  - If p == q: Type checking would fail (double ownership)

  Pointer equality constraints (e.g., matching `Owned(r)` against `Owned(p)`)
  DO generate obligations: the constraint `r == p`.

  Audited: 2026-01-27 (simplified for pragmatic SMT pipeline)
-/

import CerbLean.CN.Types

namespace CerbLean.CN.Verification

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types

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
  /-- Resource matching obligations -/
  | resourceMatch
  /-- Pointer-related obligations -/
  | pointer
  /-- Branch dead proof: prove ¬branchCondition to eliminate a failing branch.
      Corresponds to: CN's provable(false) dead-branch detection in check.ml:1985-2002,
      deferred to post-hoc SMT discharge. -/
  | branchDead
  /-- Custom obligations needing specialized handling -/
  | custom
  deriving Repr, BEq, Inhabited

instance : ToString ObligationCategory where
  toString
    | .arithmetic => "arithmetic"
    | .equality => "equality"
    | .resourceMatch => "resourceMatch"
    | .pointer => "pointer"
    | .branchDead => "branchDead"
    | .custom => "custom"

/-! ## Proof Obligation Type

A proof obligation captures what needs to be proved, along with metadata
for error reporting and strategy selection.
-/

/-- A proof obligation produced by type checking.

    Obligations are accumulated during type checking and discharged afterward
    by an external SMT solver.

    An obligation represents the implication `assumptions → constraint`.
    The assumptions capture the constraints that were in scope when the
    obligation was generated. -/
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

/-- Check if an obligation can be trivially satisfied -/
def isTrivial (_ob : Obligation) : Bool :=
  -- Placeholder - could check for tautologies
  false

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

/-- Filter obligations by category -/
def filterCategory (cat : ObligationCategory) (s : ObligationSet) : ObligationSet :=
  s.filter (·.category == cat)

end ObligationSet

/-! ## Type Check Result

The result of type checking includes success status and accumulated obligations.
-/

/-- Result of type checking a function or statement.

    Even if `success = true`, the obligations and conditional failures still
    need to be discharged by an SMT solver for the program to be verified. -/
structure TypeCheckResult where
  /-- Did structural type checking succeed? -/
  success : Bool
  /-- Proof obligations to discharge -/
  obligations : ObligationSet
  /-- Conditional failures: type errors from branches that may be dead.
      Each pairs an obligation (prove branch is dead) with the original error.
      Must be discharged post-hoc by SMT:
      - If obligation valid (branch IS dead): error is vacuous, discard.
      - If obligation invalid (branch is live): error is genuine, report. -/
  conditionalFailures : List (Obligation × String) := []
  /-- Error message if success = false -/
  error : Option String
  deriving Inhabited

namespace TypeCheckResult

/-- A successful result with no obligations -/
def ok : TypeCheckResult :=
  { success := true, obligations := [], error := none }

/-- A successful result with obligations -/
def okWithObligations (obs : ObligationSet) : TypeCheckResult :=
  { success := true, obligations := obs, error := none }

/-- A successful result with obligations and conditional failures -/
def okWithAll (obs : ObligationSet) (cfs : List (Obligation × String)) : TypeCheckResult :=
  { success := true, obligations := obs, conditionalFailures := cfs, error := none }

/-- A failed result -/
def fail (msg : String) : TypeCheckResult :=
  { success := false, obligations := [], error := some msg }

end TypeCheckResult

/-! ## Constraint to Obligation Conversion

Convert logical constraints to proof obligations.
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

end CerbLean.CN.Verification
