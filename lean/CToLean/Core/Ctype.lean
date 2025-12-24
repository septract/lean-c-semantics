/-
  C types (simplified representation)
  Based on cerberus/frontend/model/ctype.lem
-/

import CToLean.Core.Sym

namespace CToLean.Core

/-- Signed integer kinds -/
inductive SignedIntKind where
  | ichar    -- signed char
  | short
  | int_
  | long
  | longLong
  | intN (n : Nat)  -- _BitInt(N)
  deriving Repr, BEq, Inhabited

/-- Unsigned integer kinds -/
inductive UnsignedIntKind where
  | ichar    -- unsigned char
  | short
  | int_
  | long
  | longLong
  | intN (n : Nat)  -- unsigned _BitInt(N)
  deriving Repr, BEq, Inhabited

/-- Integer types from the C standard -/
inductive IntegerType where
  | char
  | bool
  | signed (kind : SignedIntKind)
  | unsigned (kind : UnsignedIntKind)
  | enum (tag : Sym)
  deriving Repr, BEq, Inhabited

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
  | function (retTy : Ctype) (params : List (Qualifiers × Ctype)) (variadic : Bool)
  | pointer (quals : Qualifiers) (pointeeTy : Ctype)
  | atomic (ty : Ctype)
  | struct_ (tag : Sym)
  | union_ (tag : Sym)
  deriving Repr, BEq, Inhabited

end CToLean.Core
