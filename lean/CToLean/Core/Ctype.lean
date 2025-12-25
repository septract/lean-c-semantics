/-
  C types (simplified representation)
  Based on cerberus/frontend/model/ctype.lem
-/

import CToLean.Core.Sym

namespace CToLean.Core

/-- Integer base type kinds (used for both signed and unsigned) -/
inductive IntBaseKind where
  | ichar       -- (signed/unsigned) char
  | short
  | int_
  | long
  | longLong
  | intN (n : Nat)       -- _BitInt(N) / unsigned _BitInt(N)
  | intLeastN (n : Nat)  -- int_leastN_t / uint_leastN_t
  | intFastN (n : Nat)   -- int_fastN_t / uint_fastN_t
  | intmax             -- intmax_t / uintmax_t
  | intptr             -- intptr_t / uintptr_t
  deriving Repr, BEq, Inhabited

/-- Integer types from the C standard -/
inductive IntegerType where
  | char                           -- plain char (implementation-defined signedness)
  | bool                           -- _Bool
  | signed (kind : IntBaseKind)    -- signed integer types
  | unsigned (kind : IntBaseKind)  -- unsigned integer types
  | enum (tag : Sym)               -- enum type
  | size_t                         -- size_t (unsigned, special)
  | wchar_t                        -- wchar_t (implementation-defined)
  | wint_t                         -- wint_t
  | ptrdiff_t                      -- ptrdiff_t (signed, special)
  | ptraddr_t                      -- ptraddr_t (CHERI)
  deriving Repr, BEq, Inhabited

/-- Backward compatibility aliases -/
abbrev SignedIntKind := IntBaseKind
abbrev UnsignedIntKind := IntBaseKind

/-- Floating types -/
inductive FloatingType where
  | float
  | double
  | longDouble
  deriving Repr, BEq, Inhabited

/-- Basic types (integer or floating) -/
inductive BasicType where
  | integer (ty : IntegerType)
  | floating (ty : FloatingType)
  deriving Repr, BEq, Inhabited

/-- Type qualifiers -/
structure Qualifiers where
  const : Bool := false
  restrict : Bool := false
  volatile : Bool := false
  deriving Repr, BEq, Inhabited

def Qualifiers.none : Qualifiers := {}

/-- C type representation -/
inductive Ctype where
  | void
  | basic (ty : BasicType)
  | array (elemTy : Ctype) (size : Option Nat)
  | function (retQuals : Qualifiers) (retTy : Ctype) (params : List (Qualifiers × Ctype)) (variadic : Bool)
  | functionNoParams (retQuals : Qualifiers) (retTy : Ctype)  -- K&R style or incomplete
  | pointer (quals : Qualifiers) (pointeeTy : Ctype)
  | atomic (ty : Ctype)
  | struct_ (tag : Sym)
  | union_ (tag : Sym)
  | byte  -- Internal byte type
  deriving Repr, BEq, Inhabited

end CToLean.Core
