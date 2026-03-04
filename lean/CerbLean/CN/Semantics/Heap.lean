/-
  CN Heap Data Structures
  Corresponds to: cn/coq/Cn/CNMem.v

  Defines the concrete memory representation for semantic interpretation:
  - Location: allocation ID + address
  - HeapValue: concrete values in memory
  - HeapFragment: partial map from locations to values (separation logic heap)
  - Valuation: maps logical symbols to concrete values

  Audited: 2026-01-18 against cn/coq/Cn/CNMem.v
-/

import CerbLean.CN.Types
import CerbLean.Memory.Types

namespace CerbLean.CN.Semantics

open CerbLean.Core (Sym Identifier Ctype IntegerType FloatingType FloatingValue)

/-! ## Location

Corresponds to: CNMem.location = (provenance * address) in cn/coq/Cn/CNMem.v
-/

/-- A location in concrete memory (allocation ID + address)
    Corresponds to: CNMem.location = (provenance * address) in cn/coq/Cn/CNMem.v -/
structure Location where
  allocId : Nat
  addr : Nat
  deriving Repr, BEq, Inhabited, DecidableEq, Hashable

/-- Location's derived BEq agrees with propositional equality.
    Required to connect `find?` (BEq-based) with `∈ dom` (Eq-based)
    in heap disjointness proofs. -/
instance : LawfulBEq Location where
  eq_of_beq {a b} h := by
    cases a with | mk a1 a2 => cases b with | mk b1 b2 =>
    simp [BEq.beq, instBEqLocation.beq] at h; obtain ⟨h1, h2⟩ := h; congr
  rfl {a} := by cases a with | mk a1 a2 => simp [BEq.beq, instBEqLocation.beq]

/-! ## Heap Value

Corresponds to: mem_value in cn/coq/Cn/CNMem.v
-/

/-- A concrete value in memory
    Corresponds to: mem_value in cn/coq/Cn/CNMem.v -/
inductive HeapValue where
  | integer (ity : IntegerType) (val : Int)
  | pointer (addr : Option Location)  -- None = NULL
  | floating (fty : FloatingType) (fv : FloatingValue)
  | struct_ (tag : Sym) (fields : List (Identifier × HeapValue))
  | array (elemTy : Ctype) (elems : List HeapValue)
  | uninitialized (ty : Ctype)
  deriving Repr, Inhabited

/-! ## MemValue → HeapValue Conversion

Converts interpreter memory values (`MemValue`) to separation-logic heap values
(`HeapValue`). This is the type-level bridge between the concrete memory model
and the logical heap model.

Note: MemValue carries more information (Ctype per struct field, provenance on
integers, floating point). HeapValue is the simpler logical representation.
-/

open CerbLean.Core (MemValue PointerValue PointerValueBase Provenance)

/-- Convert a pointer value to an optional Location.
    Only concrete pointers with provenance produce a location;
    NULL and function pointers map to `none`. -/
def locationOfPointerValue (pv : PointerValue) : Option Location :=
  match pv.prov, pv.base with
  | .some allocId, .concrete _ addr => some ⟨allocId, addr⟩
  | _, .null _ => none
  | _, _ => none  -- function pointers, symbolic provenance: not heap locations

/-- Convert a MemValue (interpreter) to a HeapValue (separation logic).
    Structural recursion on MemValue.
    - `floating` maps directly to `HeapValue.floating`
    - `union_` mapped to struct with single member field
    - `array` elements recursively converted (Ctype stubbed as `.void`) -/
def heapValueOfMemValue : MemValue → HeapValue
  | .integer ity iv => .integer ity iv.val
  | .pointer _ty pv => .pointer (locationOfPointerValue pv)
  | .struct_ tag members =>
    .struct_ tag (convertFields members)
  | .union_ tag id mv =>
    .struct_ tag [(id, heapValueOfMemValue mv)]
  | .array elems =>
    -- DIVERGES-FROM-CN: MemValue.array doesn't carry element Ctype, so
    -- we use a dummy `.void` for `elemTy`. The HeapValue elements are
    -- recursively converted; `elemTy` is only used for display/debugging.
    .array ⟨[], .void⟩ (convertArray elems)
  | .floating fty fv =>
    .floating fty fv
  | .unspecified ty => .uninitialized ty
where
  /-- Convert struct fields, recursing into each MemValue member. -/
  convertFields : List (Identifier × Ctype × MemValue) → List (Identifier × HeapValue)
    | [] => []
    | (id, _ty, mv) :: rest => (id, heapValueOfMemValue mv) :: convertFields rest
  /-- Convert array elements, recursing into each MemValue element. -/
  convertArray : List MemValue → List HeapValue
    | [] => []
    | mv :: rest => heapValueOfMemValue mv :: convertArray rest

/-! ## Heap Fragment

This is the standard separation logic heap - a partial map from locations to values.
-/

/-- A heap fragment - partial map from locations to values
    This is the standard separation logic heap.
    Corresponds to: implicit heap in separation logic -/
structure HeapFragment where
  cells : List (Location × HeapValue)
  deriving Repr, Inhabited

namespace HeapFragment

def empty : HeapFragment := ⟨[]⟩

def singleton (loc : Location) (val : HeapValue) : HeapFragment :=
  ⟨[(loc, val)]⟩

def dom (h : HeapFragment) : List Location :=
  h.cells.map (·.1)

def lookup (h : HeapFragment) (loc : Location) : Option HeapValue :=
  h.cells.find? (·.1 == loc) |>.map (·.2)

/-- Disjointness: no shared locations -/
def disjoint (h1 h2 : HeapFragment) : Prop :=
  ∀ loc, loc ∈ h1.dom → loc ∉ h2.dom

/-- Separating conjunction: combine disjoint heaps -/
def union (h1 h2 : HeapFragment) : HeapFragment :=
  ⟨h1.cells ++ h2.cells⟩

instance : Append HeapFragment := ⟨union⟩

/-- A sub-heap relation -/
def subheap (h1 h2 : HeapFragment) : Prop :=
  ∀ loc v, h1.lookup loc = some v → h2.lookup loc = some v

end HeapFragment

/-! ## Valuation

Maps logical symbols to concrete values for semantic interpretation.
-/

/-- Valuation: maps logical symbols to concrete values -/
abbrev Valuation := List (Sym × HeapValue)

namespace Valuation

def lookup (v : Valuation) (s : Sym) : Option HeapValue :=
  v.find? (fun (s', _) => s'.id == s.id) |>.map (·.2)

def empty : Valuation := []

end Valuation

end CerbLean.CN.Semantics
