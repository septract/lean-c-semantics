/-
  Core IR file structure (programs)
  Based on cerberus/frontend/ott/core-ott/core.ott lines 488-596
-/

import CToLean.Core.Expr
import Std.Data.HashMap

namespace CToLean.Core

/-! ## Tag Definitions (structs/unions) -/

/-- Struct field definition -/
structure FieldDef where
  name : Identifier
  ty : Ctype
  deriving Repr, Inhabited

/-- Tag definition (struct or union layout) -/
inductive TagDef where
  | struct_ (fields : List FieldDef)
  | union_ (fields : List FieldDef)
  deriving Repr, Inhabited

/-- Tag definitions map -/
abbrev TagDefs := Std.HashMap Sym (Loc × TagDef)

/-! ## Function Definitions -/

/-- Function/procedure declaration -/
inductive FunDecl where
  -- Pure function
  | fun_ (retTy : BaseType) (params : List (Sym × BaseType)) (body : APexpr)
  -- Effectful procedure
  | proc (loc : Loc) (retTy : BaseType) (params : List (Sym × BaseType)) (body : AExpr)
  -- Forward declarations
  | procDecl (loc : Loc) (retTy : BaseType) (paramTys : List BaseType)
  | builtinDecl (loc : Loc) (retTy : BaseType) (paramTys : List BaseType)
  deriving Inhabited

/-- Function map -/
abbrev FunMap := Std.HashMap Sym FunDecl

/-! ## Implementation Definitions -/

-- Hashable instances needed for HashMap keys

instance : Hashable SignedIntKind where
  hash
    | .ichar => 0
    | .short => 1
    | .int_ => 2
    | .long => 3
    | .longLong => 4
    | .intN n => mixHash 5 (hash n)

instance : Hashable UnsignedIntKind where
  hash
    | .ichar => 0
    | .short => 1
    | .int_ => 2
    | .long => 3
    | .longLong => 4
    | .intN n => mixHash 5 (hash n)

instance : Hashable IntegerType where
  hash
    | .char => 0
    | .bool => 1
    | .signed k => mixHash 2 (hash k)
    | .unsigned k => mixHash 3 (hash k)
    | .enum s => mixHash 4 (hash s)

instance : Hashable FloatingType where
  hash
    | .float => 0
    | .double => 1
    | .longDouble => 2

instance : Hashable BasicType where
  hash
    | .integer ty => mixHash 0 (hash ty)
    | .floating ty => mixHash 1 (hash ty)

partial def Ctype.hash : Ctype → UInt64
  | .void => 0
  | .basic b => mixHash 1 (Hashable.hash b)
  | .array e _ => mixHash 2 (Ctype.hash e)
  | .function r _ _ => mixHash 3 (Ctype.hash r)
  | .pointer _ t => mixHash 4 (Ctype.hash t)
  | .atomic t => mixHash 5 (Ctype.hash t)
  | .struct_ s => mixHash 6 (Hashable.hash s)
  | .union_ s => mixHash 7 (Hashable.hash s)

instance : Hashable Ctype := ⟨Ctype.hash⟩

instance : Hashable ImplConst where
  hash
    | .intMax ty => mixHash 0 (hash ty)
    | .intMin ty => mixHash 1 (hash ty)
    | .sizeof_ ty => mixHash 2 (hash ty)
    | .alignof_ ty => mixHash 3 (hash ty)
    | .other s => mixHash 4 (hash s)

/-- Implementation-defined constant definition -/
inductive ImplDecl where
  | def_ (ty : BaseType) (value : APexpr)
  | ifun (ty : BaseType) (params : List (Sym × BaseType)) (body : APexpr)
  deriving Inhabited

/-- Implementation definitions map -/
abbrev ImplDefs := Std.HashMap ImplConst ImplDecl

/-! ## Global Definitions -/

/-- Global variable definition or declaration -/
inductive GlobDecl where
  | def_ (coreTy : BaseType) (cTy : Ctype) (init : AExpr)
  | decl (coreTy : BaseType) (cTy : Ctype)
  deriving Inhabited

/-- Linking kind for external symbols -/
inductive LinkingKind where
  | none_
  | tentative (sym : Sym)
  | normal (sym : Sym)
  deriving Repr, BEq, Inhabited

/-! ## Core File -/

/-- A complete Core program file -/
structure File where
  /-- Entry point (main function symbol) -/
  main : Option Sym := none
  /-- Struct/union tag definitions -/
  tagDefs : TagDefs := {}
  /-- Standard library functions -/
  stdlib : FunMap := {}
  /-- Implementation-defined constants -/
  impl : ImplDefs := {}
  /-- Global variables (in definition order) -/
  globs : List (Sym × GlobDecl) := []
  /-- User-defined functions -/
  funs : FunMap := {}
  /-- External symbol mapping -/
  extern : Std.HashMap Identifier (List Sym × LinkingKind) := {}

instance : Inhabited File := ⟨{}⟩

/-- Create an empty Core file -/
def File.empty : File := {}

end CToLean.Core
