/-
  Separation Logic Propositions for Core Proof System

  SLProp is the type of separation-logic assertions about heap state.
  It describes what resources are owned and what constraints hold.

  This is the foundation type — HasType, Models, and Convert all import it.
-/

import CerbLean.CN.Types.Term  -- for IndexTerm, Subst, AnnotTerm.subst
import CerbLean.CN.Types.Base
import CerbLean.CN.Types.Resource
import CerbLean.CN.Types.Constraint  -- for LogicalConstraint.subst
import CerbLean.Core.Sym
import CerbLean.Core.Ctype

namespace CerbLean.ProofSystem

open CerbLean.Core (Sym Ctype)
open CerbLean.CN.Types (IndexTerm BaseType Init QPredicate LogicalConstraint
                         Subst AnnotTerm Term freshSymFor)

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

/-- Substitute in an SLProp using the existing CN substitution infrastructure.
    Replaces index term symbol references according to the substitution mapping.
    The `ex` case filters out the bound variable from σ to avoid capture,
    and alpha-renames if the bound variable appears in σ's relevant set. -/
def subst (σ : Subst) : SLProp → SLProp
  | .emp => .emp
  | .owned ct initState ptr val => .owned ct initState (ptr.subst σ) (val.subst σ)
  | .block ct ptr => .block ct (ptr.subst σ)
  | .pred name ptr iargs oarg =>
    .pred name (ptr.subst σ) (iargs.map (·.subst σ)) (oarg.subst σ)
  | .star l r => .star (l.subst σ) (r.subst σ)
  | .each qp oarg => .each (qp.subst σ) (oarg.subst σ)
  | .pure c => .pure (c.subst σ)
  | .ex var ty body =>
    -- Capture-avoiding: alpha-rename var if it conflicts with σ
    -- Mirrors suitablyAlphaRename from CN/Types/Term.lean
    if σ.relevant.contains var.id then
      let var' := freshSymFor var σ.relevant
      -- Build a combined substitution: rename var→var' and apply σ
      let combined := Subst.fromMapping
        ((var.id, AnnotTerm.mk (.sym var') ty default) ::
         σ.mapping.filter (·.1 != var.id))
      .ex var' ty (body.subst combined)
    else
      -- Bound variable doesn't conflict — just filter it from σ
      let σ' := Subst.fromMapping (σ.mapping.filter (·.1 != var.id))
      .ex var ty (body.subst σ')

/-! ## Total Substitution

`SLProp.substTotal` is a total (non-partial) version of `SLProp.subst` that
uses `Term.substTotal` and `AnnotTerm.substTotal` (defined in CN/Types/Term.lean)
instead of the `partial` `Term.subst`. This covers only the ~10 Term constructors
that actually appear in SLProp's IndexTerms, which are all non-binding forms
and thus structurally recursive.

The key benefit: `substTotal` reduces definitionally on concrete terms,
enabling proofs by `rfl` and unblocking `models_substTotal_extend` (the
semantic substitution lemma needed for proc/save/run soundness).

See docs/2026-03-01_SOUNDNESS_AUDIT.md issue #5.
-/

/-- Total substitution for LogicalConstraints. Uses `AnnotTerm.substTotal`.
    The `.forall_` case uses capture-avoiding substitution, mirroring
    `LogicalConstraint.subst` (Constraint.lean:44-48) and `SLProp.substTotal`'s
    `.ex` case (lines 143-154). -/
def LogicalConstraint.substTotal (σ : Subst) : LogicalConstraint → LogicalConstraint
  | .t term => .t (AnnotTerm.substTotal σ term)
  | .forall_ (s, bt) body =>
    if σ.relevant.contains s.id then
      let s' := freshSymFor s σ.relevant
      let combined := Subst.fromMapping
        ((s.id, AnnotTerm.mk (.sym s') bt default) ::
         σ.mapping.filter (·.1 != s.id))
      .forall_ (s', bt) (AnnotTerm.substTotal combined body)
    else
      let σ' := Subst.fromMapping (σ.mapping.filter (·.1 != s.id))
      .forall_ (s, bt) (AnnotTerm.substTotal σ' body)

/-- Total substitution in SLProp. Uses `AnnotTerm.substTotal` and
    `LogicalConstraint.substTotal` instead of the `partial` versions.

    The `ex` case uses capture-avoiding alpha-renaming, mirroring
    `SLProp.subst` (lines 86-99) but using `substTotal`. -/
def substTotal (σ : Subst) : SLProp → SLProp
  | .emp => .emp
  | .owned ct initState ptr val =>
    .owned ct initState (AnnotTerm.substTotal σ ptr) (AnnotTerm.substTotal σ val)
  | .block ct ptr => .block ct (AnnotTerm.substTotal σ ptr)
  | .pred name ptr iargs oarg =>
    .pred name (AnnotTerm.substTotal σ ptr)
      (iargs.map (AnnotTerm.substTotal σ)) (AnnotTerm.substTotal σ oarg)
  | .star l r => .star (l.substTotal σ) (r.substTotal σ)
  | .each qp oarg => .each (qp.substTotal σ) (AnnotTerm.substTotal σ oarg)
  | .pure c => .pure (LogicalConstraint.substTotal σ c)
  | .ex var ty body =>
    -- Capture-avoiding: alpha-rename var if it conflicts with σ's range.
    -- Mirrors SLProp.subst but uses substTotal.
    if σ.relevant.contains var.id then
      let var' := freshSymFor var σ.relevant
      let combined := Subst.fromMapping
        ((var.id, AnnotTerm.mk (.sym var') ty default) ::
         σ.mapping.filter (·.1 != var.id))
      .ex var' ty (body.substTotal combined)
    else
      let σ' := Subst.fromMapping (σ.mapping.filter (·.1 != var.id))
      .ex var ty (body.substTotal σ')

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
