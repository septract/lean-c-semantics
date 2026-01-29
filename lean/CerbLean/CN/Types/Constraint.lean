/-
  CN Logical Constraints
  Corresponds to: cn/coq/Cn/LogicalConstraints.v

  Logical constraints are assertions that must hold during verification.
  They are sent to the SMT solver (or proved manually) during type checking.

  Audited: 2026-01-20 against cn/coq/Cn/LogicalConstraints.v
-/

import CerbLean.CN.Types.Term
import CerbLean.CN.Types.Base

namespace CerbLean.CN.Types

open CerbLean.Core (Sym)

/-! ## Logical Constraint Type

Corresponds to: cn/coq/Cn/LogicalConstraints.v lines 10-12
```coq
Inductive logical_constraint : Type :=
| T : IndexTerms.t -> logical_constraint
| Forall : (Sym.t * BaseTypes.t) -> IndexTerms.t -> logical_constraint.
```
-/

/-- A logical constraint that must be verified.
    - `t`: A simple constraint (an index term that should evaluate to true)
    - `forall_`: A universally quantified constraint -/
inductive LogicalConstraint where
  /-- Simple constraint: the index term must be true -/
  | t : IndexTerm → LogicalConstraint
  /-- Universally quantified constraint: ∀ (x : bt). body -/
  | forall_ : (Sym × BaseType) → IndexTerm → LogicalConstraint
  deriving Inhabited

namespace LogicalConstraint

/-- Substitute in a logical constraint.
    Corresponds to: LC.subst in cn/lib/logicalConstraints.ml -/
def subst (σ : Subst) : LogicalConstraint → LogicalConstraint
  | .t term => .t (term.subst σ)
  | .forall_ binding body =>
    -- Note: should alpha-rename if binding symbol is in σ, but we simplify
    .forall_ binding (body.subst σ)

end LogicalConstraint

/-! ## Logical Constraint Set

Corresponds to: cn/coq/Cn/LogicalConstraints.v lines 36-40
-/

/-- A set of logical constraints -/
abbrev LCSet := List LogicalConstraint

namespace LCSet

def empty : LCSet := []

def add (lc : LogicalConstraint) (s : LCSet) : LCSet := lc :: s

def union (s1 s2 : LCSet) : LCSet := s1 ++ s2

def fromList (l : List LogicalConstraint) : LCSet := l

-- Note: We don't implement `mem` because LogicalConstraint doesn't have BEq.
-- For now, we just always add constraints (duplicates don't affect semantics).

end LCSet

end CerbLean.CN.Types
