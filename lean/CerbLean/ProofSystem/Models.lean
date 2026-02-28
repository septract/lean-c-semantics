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
                             interpOwned interpResources)

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

    The `star` case uses lookup-based heap equivalence (`HeapFragment.equiv`)
    instead of list equality. This makes commutativity trivial since lookup
    on `h1 ++ h2` and `h2 ++ h1` agrees when domains are disjoint. -/
def models (ρ : Valuation) (H : SLProp) (h : HeapFragment) : Prop :=
  match H with
  | .emp =>
    h.cells = []
  | .owned ct initState ptr val =>
    ∃ loc v,
      evalIndexTerm ρ ptr = some (.pointer (some loc)) ∧
      evalIndexTerm ρ val = some v ∧
      interpOwned ct loc initState v h
  | .block ct ptr =>
    ∃ loc v,
      evalIndexTerm ρ ptr = some (.pointer (some loc)) ∧
      interpOwned ct loc .uninit v h
  | .star P Q =>
    ∃ h1 h2,
      h1.disjoint h2 ∧
      h.equiv (h1 ++ h2) ∧
      models ρ P h1 ∧
      models ρ Q h2
  | .pure c =>
    evalConstraint ρ c ∧ h.cells = []
  | .ex var _ty body =>
    ∃ v, models ((var, v) :: ρ) body h
  | .pred _name _ptr _iargs _oarg =>
    False  -- user predicates not yet supported
  | .each _qp _oarg =>
    False  -- iterated conjunction not yet supported

/-! ## Properties -/

/-- `models ρ .emp h` iff the heap is empty. -/
theorem models_emp {ρ : Valuation} {h : HeapFragment} :
    models ρ .emp h ↔ h.cells = [] := by
  unfold models
  exact Iff.rfl

/-- Pure constraints produce an empty heap. -/
theorem models_pure {ρ : Valuation} {c : LogicalConstraint} {h : HeapFragment} :
    models ρ (.pure c) h → h.cells = [] := by
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

/-- Separating conjunction is associative (forward direction).
    Deferred: requires proving that equiv is a congruence for append, and
    that disjointness distributes across append. Standard SL property. -/
theorem models_star_assoc_forward {ρ : Valuation} {P Q R : SLProp} {h : HeapFragment} :
    models ρ (.star (.star P Q) R) h → models ρ (.star P (.star Q R)) h := by
  sorry

/-! ## Resource Conversion Compatibility -/

/-- Compatibility lemma: `models` via `SLProp.ofResources` agrees with `interpResources`.
    States that the syntactic-to-semantic path through SLProp is equivalent to
    direct semantic interpretation of resources.
    Deferred: requires proving each SLProp.ofResource matches interpResource,
    and that starAll composition matches the recursive interpResources split. -/
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
  intro ⟨loc, v, hptr, _hval, howned⟩
  exact ⟨loc, v, hptr, howned⟩

/-- Block is equivalent to owned-uninit with some existential value.
    Forward direction deferred: requires constructing an IndexTerm that
    evaluates to a given HeapValue (i.e., a "representability" lemma). -/
theorem models_block_iff_owned_uninit {ρ : Valuation} {ct : Ctype}
    {ptr : IndexTerm} {h : HeapFragment} :
    models ρ (.block ct ptr) h ↔ ∃ val, models ρ (.owned ct .uninit ptr val) h := by
  constructor
  · -- Forward: block → ∃ val, owned uninit — requires constructing an IndexTerm
    sorry
  · -- Backward: ∃ val, owned uninit → block
    intro ⟨val, howned⟩
    exact models_owned_uninit_of_block howned

/-! ## Entailment -/

/-- `H₁` entails `H₂` when every heap satisfying `H₁` also satisfies `H₂`,
    for all valuations. -/
def SLProp.entails (H₁ H₂ : SLProp) : Prop :=
  ∀ ρ h, models ρ H₁ h → models ρ H₂ h

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
