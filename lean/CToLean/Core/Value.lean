/-
  Core IR value representations
  Corresponds to: cerberus/frontend/ott/core-ott/core.ott lines 236-282
  Audited: 2025-12-31
  Deviations: Memory values use simplified representation
-/

import CToLean.Core.Types

namespace CToLean.Core

/-! ## Memory Values

Corresponds to: cerberus/frontend/model/mem_common.lem
These are abstract representations - actual memory values will be provided
by the memory model implementation.
-/

/-- Provenance for pointers and integers (memory model tracking)
    Corresponds to: provenance type in impl_mem.ml (concrete memory model)
    Audited: 2025-12-31
    Deviations: Simplified from impl_mem.ml which has more variants -/
inductive Provenance where
  | none
  | some (allocId : Nat)
  | symbolic (iota : Nat)
  | device
  deriving Repr, BEq, Inhabited

/-- Integer value with provenance (arbitrary precision)
    Corresponds to: integer_value type in mem_common.lem
    Provenance tracks which allocation the integer came from (for pointer-to-int casts)
    Audited: 2025-12-31
    Deviations: Uses Int instead of Lem's integer type -/
structure IntegerValue where
  val : Int
  prov : Provenance := .none
  deriving Repr, BEq, Inhabited

/-- Floating point value with proper handling of special cases
    Corresponds to: floating_value type in mem_common.lem
    Audited: 2025-12-31
    Deviations: Uses Float instead of Lem's floating type -/
inductive FloatingValue where
  | finite (val : Float)
  | nan
  | posInf
  | negInf
  | unspecified
  deriving Repr, BEq, Inhabited

/-- Pointer value base - the actual pointer content
    Corresponds to: pointer_value_base in impl_mem.ml (concrete model)
    Audited: 2025-12-31
    Deviations: Simplified from impl_mem.ml -/
inductive PointerValueBase where
  | null (ty : Ctype)
  | function (sym : Sym)
  | concrete (unionMember : Option Identifier) (addr : Nat)
  deriving Repr, BEq, Inhabited

/-- Pointer value with provenance
    Corresponds to: pointer_value in impl_mem.ml (concrete model)
    Audited: 2025-12-31
    Deviations: None -/
structure PointerValue where
  prov : Provenance
  base : PointerValueBase
  deriving Repr, BEq, Inhabited

/-- Memory value - the actual representation of values in memory
    Corresponds to: mem_value in mem_common.lem
    Audited: 2025-12-31
    Deviations: Uses simplified types for integer/floating -/
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

Corresponds to: core.ott lines 241-247
```ott
object_value :: 'OV' ::=
  | Mem_integer_value
  | Mem_floating_value
  | Mem_pointer_value
  | array ( </ loaded_valuei // , // i /> )
  | ( struct tag ) { </ . Symbol_identifieri : tyi = Mem_mem_valuei // , // i /> }
  | ( union tag ) { . Symbol_identifier = Mem_mem_value }
```
-/

/-- Struct member with identifier, type, and value -/
structure StructMember where
  name : Identifier
  ty : Ctype
  value : MemValue
  deriving Repr, Inhabited

-- Object and Loaded values are mutually recursive
mutual
  /-- Object values - C values that can be read/stored from memory
      Corresponds to: object_value in core.ott:241-247
      Audited: 2025-12-31
      Deviations: Uses simplified memory value types -/
  inductive ObjectValue where
    | integer (v : IntegerValue)
    | floating (v : FloatingValue)
    | pointer (v : PointerValue)
    | array (elems : List LoadedValue)
    | struct_ (tag : Sym) (members : List StructMember)
    | union_ (tag : Sym) (member : Identifier) (value : MemValue)
    deriving Inhabited

  /-- Loaded values - potentially unspecified object values
      Corresponds to: loaded_value in core.ott:249-251
      Audited: 2025-12-31
      Deviations: None -/
  inductive LoadedValue where
    | specified (v : ObjectValue)
    | unspecified (ty : Ctype)
    deriving Inhabited
end

/-! ## Data Constructors

Corresponds to: core.ott lines 266-282
```ott
ctor :: 'C' ::=
  | Nil core_base_type | Cons | Tuple | Array
  | Ivmax | Ivmin | Ivsizeof | Ivalignof
  | IvCOMPL | IvAND | IvOR | IvXOR
  | Specified | Unspecified
  | Fvfromint | Ivfromfloat
```
-/

/-- Data constructors for pattern matching and value construction
    Corresponds to: ctor in core.ott:266-282
    Audited: 2025-12-31
    Deviations: None -/
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

/-! ## Core Values

Corresponds to: core.ott lines 253-261
```ott
value :: 'V' ::=
  | object_value
  | loaded_value
  | Unit
  | True
  | False
  | ' ty '
  | core_base_type [ value1 , .. , valuei ]
  | ( value1 , .. , valuei )
```
-/

/-- Core values
    Corresponds to: value in core.ott:253-261
    Audited: 2025-12-31
    Deviations: None -/
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
