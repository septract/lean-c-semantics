/-
  Separation Logic Propositions for Core Proof System

  SLProp is the type of separation-logic assertions about heap state.
  It describes what resources are owned and what constraints hold.

  This is the foundation type — HasType, Models, and Convert all import it.
-/

import CerbLean.CN.Types.Term
import CerbLean.CN.Types.Base
import CerbLean.CN.Types.Resource
import CerbLean.CN.Types.Constraint
import CerbLean.Core.Sym
import CerbLean.Core.Ctype

namespace CerbLean.ProofSystem

open CerbLean.Core (Sym Ctype)
open CerbLean.CN.Types (IndexTerm BaseType Init QPredicate LogicalConstraint)

/-- Separation logic propositions over Core heap state.

    These describe ownership and constraints:
    - `emp`: empty heap (no resources)
    - `owned`: ownership of a typed memory cell
    - `block`: allocated but uninitialized block
    - `pred`: user-defined predicate instance
    - `star`: separating conjunction (disjoint composition)
    - `each`: iterated separating conjunction over a quantified predicate
    - `pure`: pure constraint (no heap)
    - `ex`: existential quantification -/
inductive SLProp where
  /-- Empty heap — owns nothing -/
  | emp : SLProp
  /-- Owned memory cell: `Owned<ct>(ptr) == val` with initialization state.
      When `initState = .init`, the cell is initialized and readable.
      When `initState = .uninit`, the cell is allocated but uninitialized. -/
  | owned (ct : Ctype) (initState : Init) (ptr : IndexTerm) (val : IndexTerm) : SLProp
  /-- Allocated block (no value): `Block<ct>(ptr)`.
      Represents allocated memory that has not been written to. -/
  | block (ct : Ctype) (ptr : IndexTerm) : SLProp
  /-- User-defined predicate instance: `PredName(ptr, iargs) == oarg` -/
  | pred (name : Sym) (ptr : IndexTerm) (iargs : List IndexTerm) (oarg : IndexTerm) : SLProp
  /-- Separating conjunction: `P ∗ Q` — disjoint composition of heaps -/
  | star (left right : SLProp) : SLProp
  /-- Iterated separating conjunction over a quantified predicate.
      `each qp oarg` represents `∗_{i ∈ dom(qp)} qp.name(qp.ptr + i, qp.iargs) == oarg`
      where the domain is determined by `qp.permission`. -/
  | each (qp : QPredicate) (oarg : IndexTerm) : SLProp
  /-- Pure constraint (no heap effect): the constraint must hold -/
  | pure (c : LogicalConstraint) : SLProp
  /-- Existential quantification: `∃ (var : ty), body` -/
  | ex (var : Sym) (ty : BaseType) (body : SLProp) : SLProp

namespace SLProp

/-- Fold a list of SLProps into a separating conjunction.
    `starAll []` = `emp`, `starAll [P]` = `P`, `starAll [P, Q, R]` = `P ∗ (Q ∗ R)` -/
def starAll : List SLProp → SLProp
  | [] => .emp
  | [p] => p
  | p :: ps => .star p (starAll ps)

/-- Flatten a star-tree into a list of atomic propositions.
    Inverse of `starAll` modulo associativity. -/
def flatten : SLProp → List SLProp
  | .star l r => flatten l ++ flatten r
  | .emp => []
  | other => [other]

end SLProp

instance : Repr SLProp where
  reprPrec p _ :=
    let rec go : SLProp → Std.Format
      | .emp => "emp"
      | .owned ct _init _ptr _val => f!"Owned<{repr ct}>"
      | .block ct _ptr => f!"Block<{repr ct}>"
      | .pred name _ptr _iargs _oarg => f!"Pred({repr name})"
      | .star l r => f!"({go l} ∗ {go r})"
      | .each _qp _oarg => f!"Each(...)"
      | .pure _c => f!"Pure(...)"
      | .ex var ty body => f!"∃ ({repr var} : {repr ty}), {go body}"
    go p

end CerbLean.ProofSystem
