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

/-- Integer value (arbitrary precision) -/
structure IntegerValue where
  val : Int
  deriving Repr, BEq, Inhabited

/-- Floating point value -/
structure FloatingValue where
  val : Float
  deriving Repr, BEq, Inhabited

/-- Pointer value (abstract - memory model provides concrete representation) -/
inductive PointerValue where
  | null (ty : Ctype)
  | ptr (addr : Nat) (allocId : Option Nat := none)  -- simplified for now
  deriving Repr, BEq, Inhabited

/-- Memory value (byte-level representation) -/
structure MemValue where
  bytes : List UInt8
  deriving Repr, BEq, Inhabited

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
