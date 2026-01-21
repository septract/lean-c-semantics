/-
  CN Base Types
  Corresponds to: cn/lib/baseTypes.ml lines 1-26

  These are the types used in CN specifications (refinement types).
  They are distinct from Cerberus Core types - CN types are used in
  the specification language, while Core types are used in the C semantics.

  Audited: 2025-01-17 against cn/lib/baseTypes.ml
  Deviations: None
-/

import CerbLean.Core.Sym

namespace CerbLean.CN.Types

open CerbLean.Core (Sym Identifier)

/-! ## Sign

Corresponds to: cn/lib/baseTypes.ml lines 1-4
```ocaml
type sign =
  | Signed
  | Unsigned
```
-/

/-- Signedness for bitvector types
    Corresponds to: sign in baseTypes.ml lines 1-4
    Audited: 2025-01-17
    Deviations: None -/
inductive Sign where
  | signed
  | unsigned
  deriving Repr, BEq, Inhabited, DecidableEq

/-! ## Base Type

Corresponds to: cn/lib/baseTypes.ml lines 6-24
```ocaml
type 'a t_gen =
  | Unit
  | Bool
  | Integer
  | MemByte
  | Bits of sign * int
  | Real
  | Alloc_id
  | Loc of 'a
  | CType
  | Struct of Sym.t
  | Datatype of Sym.t
  | Record of 'a member_types_gen
  | Map of 'a t_gen * 'a t_gen
  | List of 'a t_gen
  | Tuple of 'a t_gen list
  | Set of 'a t_gen
  | Option of 'a t_gen

and 'a member_types_gen = (Id.t * 'a t_gen) list
```

Note: CN's BaseTypes.t_gen is parameterized by a type 'a for location
information in pointer types. We use a simple unit type for now (matching
BaseTypes.Unit module in CN), with Loc representing pointers without
tracking their pointee type in the base type.
-/

/-- CN base types for specifications
    Corresponds to: t_gen in baseTypes.ml lines 6-24
    Audited: 2025-01-17
    Deviations: Simplified Loc to not carry pointee type (matches BaseTypes.Unit) -/
inductive BaseType where
  /-- void/unit type -/
  | unit
  /-- boolean type -/
  | bool
  /-- unbounded mathematical integers -/
  | integer
  /-- memory byte (for low-level memory reasoning) -/
  | memByte
  /-- fixed-width bitvectors (sign, width in bits) -/
  | bits (sign : Sign) (width : Nat)
  /-- real numbers -/
  | real
  /-- allocation identifiers -/
  | allocId
  /-- pointer/location type -/
  | loc
  /-- C type values (for sizeof, typeof, etc.) -/
  | ctype
  /-- struct type (by tag symbol) -/
  | struct_ (tag : Sym)
  /-- user-defined algebraic datatype -/
  | datatype (tag : Sym)
  /-- anonymous record type (list of field name, type pairs) -/
  | record (members : List (Identifier × BaseType))
  /-- finite map type -/
  | map (keyType : BaseType) (valueType : BaseType)
  /-- list type -/
  | list (elemType : BaseType)
  /-- tuple type -/
  | tuple (elemTypes : List BaseType)
  /-- set type -/
  | set (elemType : BaseType)
  /-- option type -/
  | option (innerType : BaseType)
  deriving Repr, Inhabited

/-! ## Type Abbreviations

Common bitvector types matching CN conventions.
-/

/-- Signed 8-bit integer (i8) -/
abbrev i8 : BaseType := .bits .signed 8
/-- Signed 16-bit integer (i16) -/
abbrev i16 : BaseType := .bits .signed 16
/-- Signed 32-bit integer (i32) -/
abbrev i32 : BaseType := .bits .signed 32
/-- Signed 64-bit integer (i64) -/
abbrev i64 : BaseType := .bits .signed 64

/-- Unsigned 8-bit integer (u8) -/
abbrev u8 : BaseType := .bits .unsigned 8
/-- Unsigned 16-bit integer (u16) -/
abbrev u16 : BaseType := .bits .unsigned 16
/-- Unsigned 32-bit integer (u32) -/
abbrev u32 : BaseType := .bits .unsigned 32
/-- Unsigned 64-bit integer (u64) -/
abbrev u64 : BaseType := .bits .unsigned 64

/-! ## Member Types

Corresponds to: 'a member_types_gen in baseTypes.ml line 26
```ocaml
and 'a member_types_gen = (Id.t * 'a t_gen) list
```
-/

/-- Record member types (field name to type mapping)
    Corresponds to: member_types_gen in baseTypes.ml line 26
    Audited: 2025-01-17
    Deviations: None -/
abbrev MemberTypes := List (Identifier × BaseType)

/-! ## Datatype Information

Corresponds to: cn/lib/baseTypes.ml lines 31-40
```ocaml
module Datatype = struct
  type 'a info =
    { constrs : Sym.t list;
      all_params : 'a member_types_gen
    }

  type 'a constr_info =
    { params : 'a member_types_gen;
      datatype_tag : Sym.t
    }
end
```
-/

/-- Information about a datatype definition
    Corresponds to: Datatype.info in baseTypes.ml lines 32-35
    Audited: 2025-01-17
    Deviations: None -/
structure DatatypeInfo where
  /-- List of constructor symbols -/
  constrs : List Sym
  /-- All parameters across all constructors -/
  allParams : MemberTypes
  deriving Repr, Inhabited

/-- Information about a datatype constructor
    Corresponds to: Datatype.constr_info in baseTypes.ml lines 37-40
    Audited: 2025-01-17
    Deviations: None -/
structure ConstrInfo where
  /-- Constructor parameters -/
  params : MemberTypes
  /-- Tag of the datatype this constructor belongs to -/
  datatypeTag : Sym
  deriving Repr, Inhabited

/-! ## Bitvector Range Utilities

Corresponds to: cn/lib/baseTypes.ml lines 193-229
-/

/-- Cardinality of a bitvector type: 2^n -/
def bitsCardinality (n : Nat) : Int := 2 ^ n

/-- Range of values for a bitvector type
    Corresponds to: bits_range in baseTypes.ml lines 195-199
    Returns (min, max) inclusive bounds. -/
def bitsRange (sign : Sign) (sz : Nat) : Int × Int :=
  match sign with
  | .unsigned => (0, bitsCardinality sz - 1)
  | .signed =>
    let halfCard := bitsCardinality (sz - 1)
    (-halfCard, halfCard - 1)

/-- Check if a value fits in a bitvector range
    Corresponds to: fits_range in baseTypes.ml lines 202-204 -/
def fitsRange (sign : Sign) (sz : Nat) (z : Int) : Bool :=
  let (minInt, maxInt) := bitsRange sign sz
  minInt ≤ z && z ≤ maxInt

end CerbLean.CN.Types
