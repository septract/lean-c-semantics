/-
  Core IR value representations
  Based on cerberus/frontend/ott/core-ott/core.ott lines 236-282
-/

import CToLean.Core.Types

namespace CToLean.Core

/-! ## Memory Values

These are abstract representations - actual memory values will be provided
by the memory model implementation.
-/

/-- Provenance for pointers and integers (memory model tracking)
    In Cerberus concrete memory model:
    - none: no provenance (e.g., integer constants)
    - some id: allocation ID this value came from
    - symbolic iota: for PNVI-ae-udi model
    - device: for memory-mapped I/O -/
inductive Provenance where
  | none
  | some (allocId : Nat)
  | symbolic (iota : Nat)
  | device
  deriving Repr, BEq, Inhabited

/-- Integer value with provenance (arbitrary precision)
    Provenance tracks which allocation the integer came from (for pointer-to-int casts) -/
structure IntegerValue where
  val : Int
  prov : Provenance := .none
  deriving Repr, BEq, Inhabited

/-- Floating point value with proper handling of special cases -/
inductive FloatingValue where
  | finite (val : Float)
  | nan
  | posInf
  | negInf
  | unspecified
  deriving Repr, BEq, Inhabited

/-- Pointer value base - the actual pointer content -/
inductive PointerValueBase where
  | null (ty : Ctype)
  | function (sym : Sym)
  | concrete (unionMember : Option Identifier) (addr : Nat)
  deriving Repr, BEq, Inhabited

/-- Pointer value with provenance -/
structure PointerValue where
  prov : Provenance
  base : PointerValueBase
  deriving Repr, BEq, Inhabited

/-- Memory value - the actual representation of values in memory -/
inductive MemValue where
  | unspecified (ty : Ctype)
  | integer (ity : IntegerType) (v : IntegerValue)
  | floating (fty : FloatingType) (v : FloatingValue)
  | pointer (ty : Ctype) (v : PointerValue)
  | array (elems : List MemValue)
  | struct_ (tag : Sym) (members : List (Identifier × Ctype × MemValue))
  | union_ (tag : Sym) (member : Identifier) (value : MemValue)
  deriving Repr, Inhabited

/-! ## Object Values

Values that can be stored in memory (inhabitants of object types)
-/

/-- Struct member with identifier, type, and value -/
structure StructMember where
  name : Identifier
  ty : Ctype
  value : MemValue
  deriving Repr, Inhabited

-- Object and Loaded values are mutually recursive
mutual
  /-- Object values - C values that can be read/stored from memory -/
  inductive ObjectValue where
    | integer (v : IntegerValue)
    | floating (v : FloatingValue)
    | pointer (v : PointerValue)
    | array (elems : List LoadedValue)
    | struct_ (tag : Sym) (members : List StructMember)
    | union_ (tag : Sym) (member : Identifier) (value : MemValue)
    deriving Inhabited

  /-- Loaded values - potentially unspecified object values -/
  inductive LoadedValue where
    | specified (v : ObjectValue)
    | unspecified (ty : Ctype)
    deriving Inhabited
end

/-! ## Core Values

The full value type for Core expressions
-/

/-- Data constructors for pattern matching and value construction -/
inductive Ctor where
  -- List constructors
  | nil (elemTy : BaseType)
  | cons
  -- Tuple constructor
  | tuple
  -- Array constructor
  | array
  -- Integer operations (compile-time)
  | ivmax      -- max value for integer type
  | ivmin      -- min value for integer type
  | ivsizeof   -- sizeof
  | ivalignof  -- alignof
  -- Bitwise operations
  | ivCOMPL    -- bitwise complement
  | ivAND      -- bitwise AND
  | ivOR       -- bitwise OR
  | ivXOR      -- bitwise XOR
  -- Loaded value constructors
  | specified
  | unspecified
  -- Conversions
  | fvfromint   -- integer to float
  | ivfromfloat -- float to integer
  deriving Repr, BEq, Inhabited

/-- Core values -/
inductive Value where
  | object (v : ObjectValue)
  | loaded (v : LoadedValue)
  | unit
  | true_
  | false_
  | ctype (ty : Ctype)           -- C type as a value
  | list (elemTy : BaseType) (elems : List Value)
  | tuple (elems : List Value)
  deriving Inhabited

end CToLean.Core
