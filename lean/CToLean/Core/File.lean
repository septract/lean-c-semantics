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
  | struct_ (fields : List FieldDef) (flexibleArray : Option FieldDef := none)
  | union_ (fields : List FieldDef)
  deriving Repr, Inhabited

/-- Tag definitions - using List to preserve definition order -/
abbrev TagDefs := List (Sym × (Loc × TagDef))

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

/-- Function map - using List to preserve definition order -/
abbrev FunMap := List (Sym × FunDecl)

/-! ## Implementation Definitions -/

-- Hashable instances needed for HashMap keys

instance : Hashable IntBaseKind where
  hash
    | .ichar => 0
    | .short => 1
    | .int_ => 2
    | .long => 3
    | .longLong => 4
    | .intN n => mixHash 5 (hash n)
    | .intLeastN n => mixHash 6 (hash n)
    | .intFastN n => mixHash 7 (hash n)
    | .intmax => 8
    | .intptr => 9

instance : Hashable IntegerType where
  hash
    | .char => 0
    | .bool => 1
    | .signed k => mixHash 2 (hash k)
    | .unsigned k => mixHash 3 (hash k)
    | .enum s => mixHash 4 (hash s)
    | .size_t => 5
    | .wchar_t => 6
    | .wint_t => 7
    | .ptrdiff_t => 8
    | .ptraddr_t => 9

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
  | .function _ r _ _ => mixHash 3 (Ctype.hash r)
  | .functionNoParams _ r => mixHash 4 (Ctype.hash r)
  | .pointer _ t => mixHash 5 (Ctype.hash t)
  | .atomic t => mixHash 6 (Ctype.hash t)
  | .struct_ s => mixHash 7 (Hashable.hash s)
  | .union_ s => mixHash 8 (Hashable.hash s)
  | .byte => 9

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
  stdlib : FunMap := []
  /-- Implementation-defined constants -/
  impl : ImplDefs := {}
  /-- Global variables (in definition order) -/
  globs : List (Sym × GlobDecl) := []
  /-- User-defined functions (in definition order) -/
  funs : FunMap := []
  /-- External symbol mapping -/
  extern : Std.HashMap Identifier (List Sym × LinkingKind) := {}

instance : Inhabited File := ⟨{}⟩

/-- Create an empty Core file -/
def File.empty : File := {}

end CToLean.Core
