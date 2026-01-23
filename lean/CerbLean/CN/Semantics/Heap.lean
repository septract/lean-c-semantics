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

open CerbLean.Core (Sym Identifier Ctype IntegerType)

/-! ## Location

Corresponds to: CNMem.location = (provenance * address) in cn/coq/Cn/CNMem.v
-/

/-- A location in concrete memory (allocation ID + address)
    Corresponds to: CNMem.location = (provenance * address) in cn/coq/Cn/CNMem.v -/
structure Location where
  allocId : Nat
  addr : Nat
  deriving Repr, BEq, Inhabited, DecidableEq, Hashable

/-! ## Heap Value

Corresponds to: mem_value in cn/coq/Cn/CNMem.v
-/

/-- A concrete value in memory
    Corresponds to: mem_value in cn/coq/Cn/CNMem.v -/
inductive HeapValue where
  | integer (ity : IntegerType) (val : Int)
  | pointer (addr : Option Location)  -- None = NULL
  | struct_ (tag : Sym) (fields : List (Identifier × HeapValue))
  | array (elemTy : Ctype) (elems : List HeapValue)
  | uninitialized (ty : Ctype)
  deriving Repr, Inhabited

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
