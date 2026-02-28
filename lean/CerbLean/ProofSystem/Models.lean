/-
  Semantic Interpretation of SLProp

  Defines what it means for a heap fragment to satisfy a separation-logic
  proposition (SLProp). The key definition is `models ρ H h`, which holds
  when heap fragment `h` satisfies proposition `H` under valuation `ρ`.

  This connects the syntactic SLProp layer (used in HasType) to the
  concrete heap model (HeapFragment, HeapValue) from CN.Semantics.

  Created: 2026-02-27
-/

import CerbLean.ProofSystem.SLProp
import CerbLean.ProofSystem.Convert
import CerbLean.CN.Semantics.Heap
import CerbLean.CN.Semantics.Interpretation
import CerbLean.Semantics.Monad

namespace CerbLean.CN.Semantics

/-! ## Heap Fragment Equivalence

Lookup-based equivalence for heap fragments. Two fragments are equivalent
if they map every location to the same value. This avoids dependence on
list ordering, making star commutativity trivial when domains are disjoint.
-/

/-- Two heap fragments are equivalent if they agree on all lookups. -/
def HeapFragment.equiv (h1 h2 : HeapFragment) : Prop :=
  ∀ loc, h1.lookup loc = h2.lookup loc

end CerbLean.CN.Semantics

namespace CerbLean.ProofSystem

open CerbLean.Core (Sym Ctype IntegerType IntBaseKind)
open CerbLean.CN.Types (IndexTerm Term Const PointerConst AnnotTerm Sign
                         BaseType LogicalConstraint Init QPredicate BinOp UnOp)
open CerbLean.CN.Semantics (Location HeapValue HeapFragment Valuation
                             interpResources)

/-! ## Index Term Evaluation

Partial evaluator for index terms under a valuation. Handles the
cases needed for semantic interpretation of SLProp: symbol lookup,
pointer constants, integer constants, and booleans.
Returns `none` for unhandled term forms.
-/

/-- Evaluate an index term under a valuation.
    Handles:
    - `Term.sym s` — look up symbol in the valuation
    - `Term.const (.pointer ⟨allocId, addr⟩)` — concrete pointer constant
    - `Term.const .null` — null pointer
    - `Term.const (.z n)` — unbounded integer constant
    - `Term.const (.bits sign width n)` — fixed-width bitvector constant
    - `Term.const (.bool b)` — boolean constant (true=1, false=0)
    Returns `none` for all other term forms.

    Note: matches on the AnnotTerm structure directly (not via `.term` projection)
    so Lean can verify structural termination on recursive calls. -/
def evalIndexTerm (ρ : Valuation) : IndexTerm → Option HeapValue
  | ⟨.sym s, _, _⟩ => ρ.lookup s
  | ⟨.const (.pointer ⟨allocId, addr⟩), _, _⟩ =>
    some (.pointer (some ⟨allocId.toNat, addr.toNat⟩))
  | ⟨.const .null, _, _⟩ =>
    some (.pointer none)
  | ⟨.const (.z n), _, _⟩ =>
    -- Unbounded integer; use signed int as representative IntegerType
    some (.integer (.signed .int_) n)
  | ⟨.const (.bits sign width n), _, _⟩ =>
    -- Fixed-width bitvector; map Sign to IntegerType
    let ity := match sign with
      | .signed => IntegerType.signed (.intN width)
      | .unsigned => IntegerType.unsigned (.intN width)
    some (.integer ity n)
  | ⟨.const (.bool b), _, _⟩ =>
    -- C convention: true = 1, false = 0
    some (.integer (.signed .int_) (if b then 1 else 0))
  | ⟨.binop op left right, _, _⟩ =>
    match evalIndexTerm ρ left, evalIndexTerm ρ right with
    | some (.integer ity1 v1), some (.integer _ity2 v2) =>
      match op with
      | .add => some (.integer ity1 (v1 + v2))
      | .sub => some (.integer ity1 (v1 - v2))
      | .mul => some (.integer ity1 (v1 * v2))
      | .div => if v2 ≠ 0 then some (.integer ity1 (v1 / v2)) else none
      | .eq => some (.integer (.signed .int_) (if v1 == v2 then 1 else 0))
      | .lt => some (.integer (.signed .int_) (if v1 < v2 then 1 else 0))
      | .le => some (.integer (.signed .int_) (if v1 ≤ v2 then 1 else 0))
      | _ => none
    | _, _ => none
  | ⟨.unop .not arg, _, _⟩ =>
    match evalIndexTerm ρ arg with
    | some (.integer ity val) =>
      some (.integer ity (if val == 0 then 1 else 0))
    | _ => none
  | _ => none

/-! ## Constraint Evaluation

Interprets a logical constraint as a Prop under a valuation.
-/

/-- Evaluate a logical constraint under a valuation.
    - `.t it` — the index term must evaluate to a truthy value:
      - integer: nonzero
      - non-null pointer: truthy
      - null pointer: falsy
      - unevaluable: conservatively false (sound)
    - `.forall_ (s, bt) body` — universally quantified: for all values `v`,
      the body (with `s` bound to `v`) must hold. -/
def evalConstraint (ρ : Valuation) (c : LogicalConstraint) : Prop :=
  match c with
  | .t it =>
    match evalIndexTerm ρ it with
    | some (.integer _ val) => val ≠ 0
    | some (.pointer (some _)) => True   -- non-null pointer is truthy
    | some (.pointer none) => False       -- null pointer is falsy
    | _ => False  -- unevaluable: conservatively false (sound)
  | .forall_ (s, _bt) body =>
    ∀ v, evalConstraint ((s, v) :: ρ) (.t body)

/-! ## Semantic Model Relation

The main semantic function: `models ρ H h` holds when heap fragment `h`
satisfies separation-logic proposition `H` under valuation `ρ`.
-/

/-- `models ρ H h` — heap fragment `h` satisfies SLProp `H` under valuation `ρ`.

    This is a `def` returning `Prop` (not an inductive) so it can be
    unfolded directly in proofs.

    All cases are **lookup-based**: emptiness means all lookups return `none`,
    ownership means exactly one location maps to the value and all others are
    `none`. This makes the relation invariant under lookup-equivalence
    (`HeapFragment.equiv`), which is required for the star-unit and
    star-commutativity laws.

    The `star` case uses lookup-based heap equivalence (`HeapFragment.equiv`)
    instead of list equality. This makes commutativity trivial since lookup
    on `h1 ++ h2` and `h2 ++ h1` agrees when domains are disjoint. -/
def models (ρ : Valuation) (H : SLProp) (h : HeapFragment) : Prop :=
  match H with
  | .emp =>
    ∀ loc, h.lookup loc = none
  | .owned ct initState ptr val =>
    ∃ loc v,
      evalIndexTerm ρ ptr = some (.pointer (some loc)) ∧
      h.lookup loc = some v ∧
      (∀ loc', loc' ≠ loc → h.lookup loc' = none) ∧
      match initState with
      | .init => evalIndexTerm ρ val = some v ∧
                 CerbLean.CN.Semantics.valueMatchesType ct v
      | .uninit => True
  | .block ct ptr =>
    ∃ loc v,
      evalIndexTerm ρ ptr = some (.pointer (some loc)) ∧
      h.lookup loc = some v ∧
      (∀ loc', loc' ≠ loc → h.lookup loc' = none)
  | .star P Q =>
    ∃ h1 h2,
      h1.disjoint h2 ∧
      h.equiv (h1 ++ h2) ∧
      models ρ P h1 ∧
      models ρ Q h2
  | .pure c =>
    evalConstraint ρ c ∧ (∀ loc, h.lookup loc = none)
  | .ex var _ty body =>
    ∃ v, models ((var, v) :: ρ) body h
  | .pred _name _ptr _iargs _oarg =>
    False  -- user predicates not yet supported
  | .each _qp _oarg =>
    False  -- iterated conjunction not yet supported

/-! ## Properties -/

/-- `models ρ .emp h` iff every lookup returns `none`. -/
theorem models_emp {ρ : Valuation} {h : HeapFragment} :
    models ρ .emp h ↔ (∀ loc, h.lookup loc = none) := by
  unfold models
  exact Iff.rfl

/-- Pure constraints produce a heap where every lookup returns `none`. -/
theorem models_pure {ρ : Valuation} {c : LogicalConstraint} {h : HeapFragment} :
    models ρ (.pure c) h → (∀ loc, h.lookup loc = none) := by
  unfold models
  intro ⟨_, hempty⟩
  exact hempty

/-- If a location is not in a heap's domain, find? on its cells returns none. -/
private theorem find?_none_of_not_in_dom {cells : List (Location × HeapValue)} {loc : Location}
    (h : loc ∉ cells.map Prod.fst) :
    cells.find? (·.1 == loc) = none := by
  rw [List.find?_eq_none]
  intro x hx hbeq; apply h
  rw [List.mem_map]; exact ⟨x, hx, eq_of_beq hbeq⟩

/-! ### HeapFragment Equivalence Lemmas -/

/-- Equivalence is reflexive. -/
private theorem HeapFragment.equiv_refl (h : HeapFragment) : h.equiv h :=
  fun _ => rfl

/-- Equivalence is symmetric. -/
private theorem HeapFragment.equiv_symm {h1 h2 : HeapFragment}
    (he : h1.equiv h2) : h2.equiv h1 :=
  fun loc => (he loc).symm

/-- Equivalence is transitive. -/
private theorem HeapFragment.equiv_trans {h1 h2 h3 : HeapFragment}
    (e12 : h1.equiv h2) (e23 : h2.equiv h3) : h1.equiv h3 :=
  fun loc => (e12 loc).trans (e23 loc)

/-- Append is associative (structural equality at the cells level). -/
private theorem HeapFragment.append_assoc (h1 h2 h3 : HeapFragment) :
    (h1 ++ h2) ++ h3 = h1 ++ (h2 ++ h3) :=
  congrArg HeapFragment.mk (List.append_assoc _ _ _)

/-- Equivalence is a left-congruence for append: if h1.equiv h2 then
    (h1 ++ k).equiv (h2 ++ k). Uses case analysis on find? results. -/
private theorem HeapFragment.equiv_append_right {h1 h2 : HeapFragment} (k : HeapFragment)
    (he : h1.equiv h2) : (h1 ++ k).equiv (h2 ++ k) := by
  intro loc
  simp only [HeapFragment.lookup]
  change (((h1.cells ++ k.cells).find? (·.1 == loc)).map Prod.snd =
         ((h2.cells ++ k.cells).find? (·.1 == loc)).map Prod.snd)
  rw [List.find?_append, List.find?_append]
  have he_loc := he loc
  simp only [HeapFragment.lookup] at he_loc
  cases hf1 : h1.cells.find? (·.1 == loc) with
  | none =>
    cases hf2 : h2.cells.find? (·.1 == loc) with
    | none => simp [Option.or]
    | some p2 => simp [hf1, hf2] at he_loc
  | some p1 =>
    cases hf2 : h2.cells.find? (·.1 == loc) with
    | none => simp [hf1, hf2] at he_loc
    | some p2 => simp [Option.or, hf1, hf2] at he_loc ⊢; exact he_loc

/-- Equivalence is a right-congruence for append: if h1.equiv h2 then
    (k ++ h1).equiv (k ++ h2). -/
private theorem HeapFragment.equiv_append_left (k : HeapFragment) {h1 h2 : HeapFragment}
    (he : h1.equiv h2) : (k ++ h1).equiv (k ++ h2) := by
  intro loc
  simp only [HeapFragment.lookup]
  change (((k.cells ++ h1.cells).find? (·.1 == loc)).map Prod.snd =
         ((k.cells ++ h2.cells).find? (·.1 == loc)).map Prod.snd)
  rw [List.find?_append, List.find?_append]
  cases k.cells.find? (·.1 == loc) with
  | some p => simp [Option.or]
  | none =>
    simp [Option.or]
    have he_loc := he loc
    simp only [HeapFragment.lookup] at he_loc
    exact he_loc

/-- If h.lookup loc = some v, then loc is in h's domain. -/
private theorem HeapFragment.dom_of_lookup {h : HeapFragment} {loc : Location} {v : HeapValue}
    (hl : h.lookup loc = some v) : loc ∈ h.dom := by
  simp only [HeapFragment.lookup] at hl
  match hf : h.cells.find? (·.1 == loc) with
  | none => simp [hf] at hl
  | some pair =>
    have hmem := List.mem_of_find?_eq_some hf
    have hbeq := @List.find?_some _ (·.1 == loc) pair _ hf
    unfold HeapFragment.dom
    have : pair.1 = loc := eq_of_beq hbeq
    rw [← this]; exact List.mem_map_of_mem hmem

/-- Disjointness is symmetric. -/
private theorem HeapFragment.disjoint_symm {h1 h2 : HeapFragment}
    (hd : h1.disjoint h2) : h2.disjoint h1 :=
  fun loc hloc2 hloc1 => hd loc hloc1 hloc2

/-- Dom of append is append of doms. -/
private theorem HeapFragment.dom_append (h1 h2 : HeapFragment) :
    (h1 ++ h2).dom = h1.dom ++ h2.dom :=
  List.map_append ..

/-- For disjoint heaps, lookup on h1 ++ h2 and h2 ++ h1 agree. -/
private theorem union_lookup_comm (h1 h2 : HeapFragment) (hdisj : h1.disjoint h2) :
    (h1 ++ h2).equiv (h2 ++ h1) := by
  intro loc
  simp only [HeapFragment.lookup]
  change (((h1.cells ++ h2.cells).find? (·.1 == loc)).map Prod.snd =
         ((h2.cells ++ h1.cells).find? (·.1 == loc)).map Prod.snd)
  rw [List.find?_append, List.find?_append]
  cases hf1 : h1.cells.find? (·.1 == loc) with
  | none =>
    cases h2.cells.find? (·.1 == loc) <;> simp [Option.or]
  | some pair =>
    have hbeq := @List.find?_some _ (·.1 == loc) pair _ hf1
    have hkey : pair.1 = loc := eq_of_beq hbeq
    have hmem : pair ∈ h1.cells := List.mem_of_find?_eq_some hf1
    have hdom : pair.1 ∈ h1.dom := by
      unfold HeapFragment.dom; exact List.mem_map_of_mem hmem
    have hnotdom : loc ∉ h2.dom := by rw [← hkey]; exact hdisj pair.1 hdom
    have hf2 := find?_none_of_not_in_dom hnotdom
    simp [Option.or, hf2]

/-- Separating conjunction is commutative.
    With lookup-based equivalence, this follows from disjoint-union commutativity. -/
theorem models_star_comm {ρ : Valuation} {P Q : SLProp} {h : HeapFragment} :
    models ρ (.star P Q) h → models ρ (.star Q P) h := by
  unfold models
  intro ⟨h1, h2, hdisj, hequiv, hp, hq⟩
  refine ⟨h2, h1,
    fun loc hloc2 hloc1 => hdisj loc hloc1 hloc2,
    fun loc => ?_,
    hq, hp⟩
  have hcomm := union_lookup_comm h1 h2 hdisj
  rw [hequiv loc, hcomm loc]

/-- Given a membership in a domain, produce a cell witness and a non-none find?. -/
private theorem lookup_some_of_mem_dom {h : HeapFragment} {loc : Location}
    (hmem : loc ∈ h.dom) : ∃ v, h.lookup loc = some v := by
  simp only [HeapFragment.dom, List.mem_map] at hmem
  obtain ⟨⟨loc', v⟩, hcell, heq⟩ := hmem
  simp at heq  -- (loc', v).fst = loc → loc' = loc
  have his : (h.cells.find? (·.1 == loc)).isSome = true :=
    List.find?_isSome.mpr ⟨(loc', v), hcell, by subst heq; simp⟩
  match hf : h.cells.find? (·.1 == loc), his with
  | some p, _ => exact ⟨p.2, by simp [HeapFragment.lookup, hf]⟩
  | none, h => simp_all

/-- Route a domain membership through an equiv: if loc ∈ dom of one side
    of an equiv, it's in the domain of the other side. -/
private theorem dom_of_equiv_dom {h1 h2 : HeapFragment}
    (he : h1.equiv h2) {loc : Location} (hmem : loc ∈ h2.dom) :
    loc ∈ h1.dom := by
  obtain ⟨v, hv⟩ := lookup_some_of_mem_dom hmem
  have := he loc ▸ hv
  exact HeapFragment.dom_of_lookup this

/-- Separating conjunction is associative (forward direction).
    Given `(P ∗ Q) ∗ R`, reassociates to `P ∗ (Q ∗ R)`.
    Witnesses: outer = (h_p, h_q ++ h_r), inner = (h_q, h_r). -/
theorem models_star_assoc_forward {ρ : Valuation} {P Q R : SLProp} {h : HeapFragment} :
    models ρ (.star (.star P Q) R) h → models ρ (.star P (.star Q R)) h := by
  unfold models
  intro ⟨h_pq, h_r, d_pq_r, e_h, ⟨h_p, h_q, d_p_q, e_pq, mp, mq⟩, mr⟩
  refine ⟨h_p, h_q ++ h_r, ?d_p_qr, ?e_h', mp, h_q, h_r, ?d_q_r,
    HeapFragment.equiv_refl _, mq, mr⟩
  case d_p_qr =>
    -- h_p.disjoint (h_q ++ h_r)
    intro loc hloc_p hloc_qr
    rw [HeapFragment.dom_append] at hloc_qr
    rcases List.mem_append.mp hloc_qr with hloc_q | hloc_r
    · exact d_p_q loc hloc_p hloc_q
    · -- loc ∈ h_p.dom → loc ∈ (h_p++h_q).dom → (via equiv) loc ∈ h_pq.dom → loc ∉ h_r.dom
      have hmem_pq : loc ∈ (h_p ++ h_q).dom := by
        rw [HeapFragment.dom_append]; exact List.mem_append_left _ hloc_p
      exact d_pq_r loc (dom_of_equiv_dom e_pq hmem_pq) hloc_r
  case e_h' =>
    -- h.equiv (h_p ++ (h_q ++ h_r))
    exact HeapFragment.equiv_trans e_h
      (HeapFragment.equiv_trans
        (HeapFragment.equiv_append_right h_r e_pq)
        (by rw [HeapFragment.append_assoc]; exact HeapFragment.equiv_refl _))
  case d_q_r =>
    -- h_q.disjoint h_r
    intro loc hloc_q hloc_r
    have hmem_pq : loc ∈ (h_p ++ h_q).dom := by
      rw [HeapFragment.dom_append]; exact List.mem_append_right _ hloc_q
    exact d_pq_r loc (dom_of_equiv_dom e_pq hmem_pq) hloc_r

/-- Separating conjunction is associative (backward direction).
    Given `P ∗ (Q ∗ R)`, reassociates to `(P ∗ Q) ∗ R`.
    Proved by composing star_comm and star_assoc_forward. -/
theorem models_star_assoc_backward {ρ : Valuation} {P Q R : SLProp} {h : HeapFragment} :
    models ρ (.star P (.star Q R)) h → models ρ (.star (.star P Q) R) h := by
  -- P ∗ (Q ∗ R) → (Q ∗ R) ∗ P → Q ∗ (R ∗ P) → Q ∗ (P ∗ R) → (P ∗ R) ∗ Q → ...
  -- Simpler: P ∗ (Q ∗ R) →[comm] (Q ∗ R) ∗ P →[assoc_fwd] Q ∗ (R ∗ P) →[comm inner] Q ∗ (P ∗ R)
  --          →[comm] (P ∗ R) ∗ Q →[assoc_fwd] P ∗ (R ∗ Q) →[comm inner] P ∗ (Q ∗ R)
  -- That's circular. Let's just do the direct proof.
  unfold models
  intro ⟨h_p, h_qr, d_p_qr, e_h, mp, h_q, h_r, d_q_r, e_qr, mq, mr⟩
  refine ⟨h_p ++ h_q, h_r, ?_, ?_, ⟨h_p, h_q, ?_, HeapFragment.equiv_refl _, mp, mq⟩, mr⟩
  · -- (h_p ++ h_q).disjoint h_r
    intro loc hloc_pq hloc_r
    rw [HeapFragment.dom_append] at hloc_pq
    rcases List.mem_append.mp hloc_pq with hloc_p | hloc_q
    · have hmem_qr : loc ∈ (h_q ++ h_r).dom := by
        rw [HeapFragment.dom_append]; exact List.mem_append_right _ hloc_r
      exact d_p_qr loc hloc_p (dom_of_equiv_dom e_qr hmem_qr)
    · exact d_q_r loc hloc_q hloc_r
  · -- h.equiv ((h_p ++ h_q) ++ h_r)
    exact HeapFragment.equiv_trans e_h
      (HeapFragment.equiv_trans
        (HeapFragment.equiv_append_left h_p e_qr)
        (by rw [← HeapFragment.append_assoc]; exact HeapFragment.equiv_refl _))
  · -- h_p.disjoint h_q
    intro loc hloc_p hloc_q
    have hmem_qr : loc ∈ (h_q ++ h_r).dom := by
      rw [HeapFragment.dom_append]; exact List.mem_append_left _ hloc_q
    exact d_p_qr loc hloc_p (dom_of_equiv_dom e_qr hmem_qr)

/-! ## Resource Conversion Compatibility -/

/-- Compatibility lemma: `models` via `SLProp.ofResources` agrees with `interpResources`.
    States that the syntactic-to-semantic path through SLProp is equivalent to
    direct semantic interpretation of resources.

    **Deferred to Stage 5** (connecting proof system to CN type checker).
    Requires:
    1. Each `SLProp.ofResource r` matches `interpResource r` for a single resource
    2. The `starAll` fold in `SLProp.ofResources` matches the recursive cons-cell
       split in `interpResources`
    3. Bridge between lookup-based `models` for `.owned` and structural `interpOwned`
       (see `interpOwned_implies_lookup` in the test suite for the forward direction;
       the reverse needs a well-formedness invariant on HeapFragment)

    Not needed until we verify that CN's resource inference output plugs into
    our HasType derivations. -/
theorem models_ofResources_iff (ρ : Valuation) (rs : List CerbLean.CN.Types.Resource)
    (h : HeapFragment) :
    models ρ (SLProp.ofResources rs) h ↔ interpResources rs ρ h := by
  sorry

/-! ## Block-Owned Bridge -/

/-- Block implies owned-uninit: the backward direction of the block-owned bridge.
    If we have `Owned<ct>(uninit, ptr, val)` for some `val`, we can forget the
    value witness to get `Block<ct>(ptr)`. -/
theorem models_owned_uninit_of_block {ρ : Valuation} {ct : Ctype}
    {ptr val : IndexTerm} {h : HeapFragment} :
    models ρ (.owned ct .uninit ptr val) h → models ρ (.block ct ptr) h := by
  unfold models
  intro ⟨loc, v, hptr, hlookup, hother, _⟩
  exact ⟨loc, v, hptr, hlookup, hother⟩

/-- Block is equivalent to owned-uninit with some existential value.
    Forward: the `val` IndexTerm is a dummy since for `.uninit` the `models`
    definition does not require `evalIndexTerm ρ val = some v` (the value
    evaluation constraint only applies to `.init`).
    Backward: just drop the existential witness. -/
theorem models_block_iff_owned_uninit {ρ : Valuation} {ct : Ctype}
    {ptr : IndexTerm} {h : HeapFragment} :
    models ρ (.block ct ptr) h ↔ ∃ val, models ρ (.owned ct .uninit ptr val) h := by
  constructor
  · -- Forward: block → ∃ val, owned uninit
    unfold models
    intro ⟨loc, v, hptr, hlookup, hother⟩
    -- Any IndexTerm works as the dummy val since .uninit doesn't evaluate it
    exact ⟨⟨.const .unit, .unit, default⟩, loc, v, hptr, hlookup, hother, trivial⟩
  · -- Backward: ∃ val, owned uninit → block
    intro ⟨val, howned⟩
    exact models_owned_uninit_of_block howned

/-! ## Entailment -/

/-- `H₁` entails `H₂` when every heap satisfying `H₁` also satisfies `H₂`,
    for all valuations. -/
def SLProp.entails (H₁ H₂ : SLProp) : Prop :=
  ∀ ρ h, models ρ H₁ h → models ρ H₂ h

/-- Entailment is reflexive. -/
theorem SLProp.entails_refl (H : SLProp) : SLProp.entails H H :=
  fun _ _ h => h

/-- `models` is invariant under lookup-equivalence.
    Since all cases of `models` are defined via `h.lookup`, replacing `h` with
    a lookup-equivalent heap preserves the relation. -/
theorem models_equiv {H : SLProp} {ρ : Valuation} {h1 h2 : HeapFragment}
    (he : h1.equiv h2) : models ρ H h2 → models ρ H h1 := by
  induction H generalizing ρ h1 h2 with
  | emp =>
    intro hemp loc; exact (he loc).trans (hemp loc)
  | owned ct initState ptr val =>
    intro ⟨loc, v, hptr, hlookup, hother, htail⟩
    exact ⟨loc, v, hptr, (he loc).trans hlookup,
      fun loc' hne => (he loc').trans (hother loc' hne), htail⟩
  | block ct ptr =>
    intro ⟨loc, v, hptr, hlookup, hother⟩
    exact ⟨loc, v, hptr, (he loc).trans hlookup,
      fun loc' hne => (he loc').trans (hother loc' hne)⟩
  | star P Q _ihP _ihQ =>
    intro ⟨h_p, h_q, hdisj, hequiv, mp, mq⟩
    exact ⟨h_p, h_q, hdisj, HeapFragment.equiv_trans he hequiv, mp, mq⟩
  | pure c =>
    intro ⟨hc, hemp⟩
    exact ⟨hc, fun loc => (he loc).trans (hemp loc)⟩
  | ex var _ty body ih =>
    intro ⟨v, hm⟩
    exact ⟨v, ih he hm⟩
  | pred => exact id
  | each => exact id

/-- Appending an empty heap on the right is lookup-equivalent. -/
private theorem HeapFragment.equiv_append_empty {h1 h2 : HeapFragment}
    (hemp : ∀ loc, h2.lookup loc = none) : h1.equiv (h1 ++ h2) := by
  intro loc
  simp only [HeapFragment.lookup]
  change (h1.cells.find? (·.1 == loc)).map Prod.snd =
         ((h1.cells ++ h2.cells).find? (·.1 == loc)).map Prod.snd
  rw [List.find?_append]
  cases h1.cells.find? (·.1 == loc) with
  | some p => simp [Option.or]
  | none =>
    simp [Option.or]
    have := hemp loc
    simp only [HeapFragment.lookup] at this
    match hf : h2.cells.find? (·.1 == loc) with
    | none => simp [hf]
    | some p => simp [hf] at this

/-- `H ∗ emp` entails `H`: the right unit law for star. -/
theorem models_star_emp {ρ : Valuation} {H : SLProp} {h : HeapFragment} :
    models ρ (.star H .emp) h → models ρ H h := by
  intro ⟨h1, h2, _hdisj, hequiv, mh, hemp⟩
  -- h2 is empty (all lookups none from emp)
  -- h.equiv (h1 ++ h2) and h1.equiv (h1 ++ h2) since h2 lookups are all none
  -- So h.equiv h1, and models_equiv transfers mh from h1 to h
  exact models_equiv (HeapFragment.equiv_trans hequiv
    (HeapFragment.equiv_symm (HeapFragment.equiv_append_empty hemp))) mh

/-- `emp ∗ H` entails `H`: the left unit law for star. -/
theorem models_emp_star {ρ : Valuation} {H : SLProp} {h : HeapFragment} :
    models ρ (.star .emp H) h → models ρ H h := by
  exact fun hstar => models_star_emp (models_star_comm hstar)

/-! ## HeapValue ↔ CN BaseType Compatibility -/

/-- Relates a `HeapValue` to a CN `BaseType`.
    Used in soundness proofs to state that a value has the expected type.
    This is the semantic counterpart of `valueHasType` (in HasType.lean),
    which relates Core `Value` to `CNBaseType`. -/
def heapValueHasType : HeapValue → CerbLean.CN.Types.BaseType → Prop
  | .integer _ _, .integer => True
  | .integer (.signed (.intN w)) _, .bits .signed w' => w = w'
  | .integer (.unsigned (.intN w)) _, .bits .unsigned w' => w = w'
  | .pointer _, .loc => True
  | .struct_ _ _, .record _ => True  -- field-level checking deferred
  | _, .unit => True  -- unit is trivially satisfied
  | _, .bool => True  -- booleans represented as integers in C
  | _, _ => False

/-! ## Interpreter State Bridge

The bridge between the proof system's heap model (`HeapFragment`) and the
interpreter's concrete memory state (`InterpState`). The full conversion is
complex because `MemState` uses a byte-level `bytemap` while `HeapFragment`
uses typed `(Location × HeapValue)` cells. The extraction requires type
information to group bytes into typed values.

For now we axiomatize the extraction and defer its implementation to when
the soundness proof needs it. -/

open CerbLean.Semantics (InterpState)

/-- Extract a logical heap fragment from an interpreter state.
    AXIOM: The actual conversion from byte-level `MemState` to typed
    `HeapFragment` requires type-directed byte grouping. This axiom is
    in the TCB — it asserts that such an extraction exists and is faithful
    to the memory model's semantics. -/
axiom heapFragmentOf : InterpState → HeapFragment

/-- The interpreter state satisfies a separation-logic proposition.
    Connects the proof system (`models` over `HeapFragment`) to the
    interpreter (`InterpState`). -/
def stateModels (σ : InterpState) (ρ : Valuation) (H : SLProp) : Prop :=
  models ρ H (heapFragmentOf σ)

end CerbLean.ProofSystem
