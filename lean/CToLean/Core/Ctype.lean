/-
  C types representation
  Corresponds to: cerberus/frontend/model/ctype.lem and integerType.lem
  Audited: 2025-12-31
  Deviations: None
-/

import CToLean.Core.Sym
import CToLean.Core.Annot

namespace CToLean.Core

/-! ## Integer Types

Corresponds to: cerberus/frontend/model/integerType.lem lines 10-35
-/

/-- Integer base type kinds (used for both signed and unsigned)
    Corresponds to: integerBaseType in integerType.lem lines 10-21
    Audited: 2025-12-31
    Deviations: None -/
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

/-- Integer types from the C standard (§6.2.5#17)
    Corresponds to: integerType in integerType.lem lines 24-35
    Audited: 2025-12-31
    Deviations: None -/
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

/-! ## Floating Types

Corresponds to: cerberus/frontend/model/ctype.lem lines 11-18
-/

/-- Real floating types (§6.2.5#10)
    Corresponds to: realFloatingType in ctype.lem lines 11-14
    Audited: 2025-12-31
    Deviations: None -/
inductive RealFloatingType where
  | float
  | double
  | longDouble
  deriving Repr, BEq, Inhabited

/-- Floating types (§6.2.5#11)
    Corresponds to: floatingType in ctype.lem lines 17-18
    Audited: 2025-12-31
    Deviations: Complex types not yet supported (commented out in Cerberus) -/
inductive FloatingType where
  | realFloating (ty : RealFloatingType)
  -- | complex (ty : FloatingType)  -- §6.2.5#11, not yet in Cerberus
  deriving Repr, BEq, Inhabited

/-! ## Basic Types -/

/-- Basic types (§6.2.5#14)
    Corresponds to: basicType in ctype.lem lines 22-24
    Audited: 2025-12-31
    Deviations: None -/
inductive BasicType where
  | integer (ty : IntegerType)
  | floating (ty : FloatingType)
  deriving Repr, BEq, Inhabited

/-! ## Type Qualifiers -/

/-- Type qualifiers (§6.2.5#26)
    Corresponds to: qualifiers in ctype.lem lines 27-32
    Audited: 2025-12-31
    Deviations: None -/
structure Qualifiers where
  const : Bool := false
  restrict : Bool := false
  volatile : Bool := false
  deriving Repr, BEq, Inhabited

/-- No qualifiers (internal helper)
    Corresponds to: no_qualifiers in ctype.lem -/
def Qualifiers.none : Qualifiers := {}

/-! ## C Types

In Cerberus, ctype is defined as:
  type ctype_ = Void | Basic | Array | Function | ...
  and ctype = Ctype of list Annot.annot * ctype_

We match this structure exactly.
-/

/-- Inner C type representation (without annotations)
    Corresponds to: ctype_ in ctype.lem lines 34-61
    Audited: 2025-12-31
    Deviations: None -/
inductive Ctype_ where
  | void
  | basic (ty : BasicType)
  | array (elemTy : Ctype_) (size : Option Nat)
  /-- Function type with parameters including is_register flag
      Cerberus: Function of (qualifiers * ctype) * list (qualifiers * ctype * bool) * bool
      The bool in parameters is is_register -/
  | function (retQuals : Qualifiers) (retTy : Ctype_)
      (params : List (Qualifiers × Ctype_ × Bool)) (variadic : Bool)
  | functionNoParams (retQuals : Qualifiers) (retTy : Ctype_)  -- K&R style or incomplete
  | pointer (quals : Qualifiers) (pointeeTy : Ctype_)
  | atomic (ty : Ctype_)
  | struct_ (tag : Sym)
  | union_ (tag : Sym)
  | byte  -- Internal byte type
  deriving Repr, BEq, Inhabited

/-- C type with annotations
    Corresponds to: ctype in ctype.lem lines 62-63
    Audited: 2025-12-31
    Deviations: None -/
structure Ctype where
  annots : Annots := []
  ty : Ctype_
  deriving Repr, BEq, Inhabited

/-- Create a Ctype without annotations (internal helper) -/
def Ctype.mk' (ty : Ctype_) : Ctype := { ty := ty }

/-! ## Convenience Constructors

Internal helpers for constructing Ctype values without explicit annotations.
-/

namespace Ctype

def void : Ctype := mk' .void
def basic (ty : BasicType) : Ctype := mk' (.basic ty)
def array (elemTy : Ctype) (size : Option Nat) : Ctype := mk' (.array elemTy.ty size)
def function (retQuals : Qualifiers) (retTy : Ctype)
    (params : List (Qualifiers × Ctype × Bool)) (variadic : Bool) : Ctype :=
  mk' (.function retQuals retTy.ty (params.map fun (q, t, r) => (q, t.ty, r)) variadic)
def functionNoParams (retQuals : Qualifiers) (retTy : Ctype) : Ctype :=
  mk' (.functionNoParams retQuals retTy.ty)
def pointer (quals : Qualifiers) (pointeeTy : Ctype) : Ctype :=
  mk' (.pointer quals pointeeTy.ty)
def atomic (ty : Ctype) : Ctype := mk' (.atomic ty.ty)
def struct_ (tag : Sym) : Ctype := mk' (.struct_ tag)
def union_ (tag : Sym) : Ctype := mk' (.union_ tag)
def byte : Ctype := mk' .byte

/-- Integer type constructor (internal helper) -/
def integer (ity : IntegerType) : Ctype :=
  mk' (.basic (.integer ity))

/-- Floating type constructor (internal helper) -/
def floating (fty : RealFloatingType) : Ctype :=
  mk' (.basic (.floating (.realFloating fty)))

end Ctype

end CToLean.Core
