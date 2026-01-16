/-
  Core IR file structure (programs)
  Corresponds to: cerberus/frontend/ott/core-ott/core.ott lines 488-596
  Audited: 2025-12-31
  Deviations: None
-/

import CerbLean.Core.Expr
import Std.Data.HashMap

namespace CerbLean.Core

/-! ## Tag Definitions (structs/unions)

Corresponds to: core.ott lines 540-541 (core_tag_definitions)
```lem
type core_tag_definitions =
  map Symbol.sym (Loc.t * Ctype.tag_definition)
```
-/

/-- Struct field definition
    Corresponds to: Ctype.field_def in ctype.lem
    Audited: 2025-12-31
    Deviations: None -/
structure FieldDef where
  name : Identifier
  ty : Ctype
  deriving Repr, Inhabited

/-- Tag definition (struct or union layout)
    Corresponds to: Ctype.tag_definition in ctype.lem:83-85
    Audited: 2025-12-31
    Deviations: None -/
inductive TagDef where
  | struct_ (fields : List FieldDef) (flexibleArray : Option FieldDef := none)
  | union_ (fields : List FieldDef)
  deriving Repr, Inhabited

/-- Tag definitions - using List to preserve definition order
    Corresponds to: core_tag_definitions in core.ott:540-541
    Audited: 2025-12-31
    Deviations: Uses List instead of map -/
abbrev TagDefs := List (Sym × (Loc × TagDef))

/-! ## Function Definitions

Corresponds to: core.ott lines 483-487 (generic_fun_map_decl)
```lem
type generic_fun_map_decl 'bty 'a =
  | Fun of core_base_type * list (Symbol.sym * core_base_type) * generic_pexpr 'bty Symbol.sym
  | Proc of Loc.t * maybe nat (* marker env *) * core_base_type * list (Symbol.sym * core_base_type) * generic_expr 'a 'bty Symbol.sym
  | ProcDecl of Loc.t * core_base_type * list core_base_type
  | BuiltinDecl of Loc.t * core_base_type * list core_base_type
```
-/

/-- Function/procedure declaration
    Corresponds to: generic_fun_map_decl in core.ott:483-487
    Audited: 2025-12-31
    Deviations: None -/
inductive FunDecl where
  -- Pure function: Fun of core_base_type * list (Symbol.sym * core_base_type) * generic_pexpr
  | fun_ (retTy : BaseType) (params : List (Sym × BaseType)) (body : APexpr)
  -- Effectful procedure: Proc of Loc.t * maybe nat * core_base_type * list (Symbol.sym * core_base_type) * generic_expr
  | proc (loc : Loc) (markerEnv : Option Nat) (retTy : BaseType) (params : List (Sym × BaseType)) (body : AExpr)
  -- Forward declarations: ProcDecl of Loc.t * core_base_type * list core_base_type
  | procDecl (loc : Loc) (retTy : BaseType) (paramTys : List BaseType)
  -- Builtin declarations: BuiltinDecl of Loc.t * core_base_type * list core_base_type
  | builtinDecl (loc : Loc) (retTy : BaseType) (paramTys : List BaseType)
  deriving Inhabited

/-- Function map - using List to preserve definition order
    Corresponds to: generic_fun_map in core.ott:489
    Audited: 2025-12-31
    Deviations: Uses List instead of map -/
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

instance : Hashable RealFloatingType where
  hash
    | .float => 0
    | .double => 1
    | .longDouble => 2

instance : Hashable FloatingType where
  hash
    | .realFloating ty => hash ty

instance : Hashable BasicType where
  hash
    | .integer ty => mixHash 0 (hash ty)
    | .floating ty => mixHash 1 (hash ty)

partial def Ctype_.hash : Ctype_ → UInt64
  | .void => 0
  | .basic b => mixHash 1 (Hashable.hash b)
  | .array e _ => mixHash 2 (Ctype_.hash e)
  | .function _ r _ _ => mixHash 3 (Ctype_.hash r)
  | .functionNoParams _ r => mixHash 4 (Ctype_.hash r)
  | .pointer _ t => mixHash 5 (Ctype_.hash t)
  | .atomic t => mixHash 6 (Ctype_.hash t)
  | .struct_ s => mixHash 7 (Hashable.hash s)
  | .union_ s => mixHash 8 (Hashable.hash s)
  | .byte => 9

instance : Hashable Ctype_ := ⟨Ctype_.hash⟩

instance : Hashable Ctype where
  hash ct := Ctype_.hash ct.ty

instance : Hashable ImplConst where
  hash
    | .intMax ty => mixHash 0 (hash ty)
    | .intMin ty => mixHash 1 (hash ty)
    | .sizeof_ ty => mixHash 2 (hash ty)
    | .alignof_ ty => mixHash 3 (hash ty)
    | .other s => mixHash 4 (hash s)

/-! ## Implementation Definitions

Corresponds to: core.ott lines 478-480 (generic_impl_decl)
```lem
type generic_impl_decl 'bty =
  | Def of core_base_type * generic_pexpr 'bty Symbol.sym
  | IFun of core_base_type * list (Symbol.sym * core_base_type) * generic_pexpr 'bty Symbol.sym
```
-/

/-- Implementation-defined constant definition
    Corresponds to: generic_impl_decl in core.ott:478-480
    Audited: 2025-12-31
    Deviations: None -/
inductive ImplDecl where
  | def_ (ty : BaseType) (value : APexpr)
  | ifun (ty : BaseType) (params : List (Sym × BaseType)) (body : APexpr)
  deriving Inhabited

/-- Implementation definitions map
    Corresponds to: generic_impl in core.ott:481
    Audited: 2025-12-31
    Deviations: None -/
abbrev ImplDefs := Std.HashMap ImplConst ImplDecl

/-! ## Global Definitions

Corresponds to: core.ott lines 533-535 (generic_globs)
```lem
type generic_globs 'a 'bty =
  | GlobalDef of (core_base_type * Ctype.ctype) * generic_expr 'a 'bty Symbol.sym
  | GlobalDecl of (core_base_type * Ctype.ctype)
```
-/

/-- Global variable definition or declaration
    Corresponds to: generic_globs in core.ott:533-535
    Audited: 2025-12-31
    Deviations: None -/
inductive GlobDecl where
  | def_ (coreTy : BaseType) (cTy : Ctype) (init : AExpr)
  | decl (coreTy : BaseType) (cTy : Ctype)
  deriving Inhabited

/-! ## Linking Kind

Corresponds to: core.ott lines 520-523 (linking_kind)
```lem
type linking_kind =
  | LK_none
  | LK_tentative of Symbol.sym
  | LK_normal of Symbol.sym
```
-/

/-- Linking kind for external symbols
    Corresponds to: linking_kind in core.ott:520-523
    Audited: 2025-12-31
    Deviations: None -/
inductive LinkingKind where
  | none_
  | tentative (sym : Sym)
  | normal (sym : Sym)
  deriving Repr, BEq, Inhabited

/-! ## Visible Objects Environment

Corresponds to: core.ott line 543
```lem
type visible_objects_env = map nat (list (Symbol.sym * Ctype.ctype))
```
-/

/-- Visible objects environment for marker scopes
    Corresponds to: visible_objects_env in core.ott:543
    Audited: 2025-12-31
    Deviations: Uses List instead of map -/
abbrev VisibleObjectsEnv := List (Nat × List (Sym × Ctype))

/-! ## Function Info (for cfunction expression)

Corresponds to: core.ott line 557 (funinfo field)
```lem
funinfo : map Symbol.sym (Loc.t * Annot.attributes * ctype * list (maybe Symbol.sym * ctype) * bool * bool);
```
-/

/-- Function parameter info (internal helper)
    Represents one element of funinfo params in core.ott:557: (maybe Symbol.sym * ctype) -/
structure FunParam where
  /-- Parameter symbol (may be None for unnamed parameters) -/
  sym : Option Sym
  /-- Parameter C type -/
  ty : Ctype
  deriving Repr, Inhabited

/-- Function type info - used by cfunction() expression
    Corresponds to: funinfo value type in core.ott:557
    Audited: 2025-12-31
    Deviations: attributes field not used (always empty in practice) -/
structure FunInfo where
  /-- Source location -/
  loc : Loc
  /-- C2X attributes (usually empty) -/
  attrs : Attributes := Attributes.empty
  /-- Return type -/
  returnType : Ctype
  /-- Parameter types (with optional names) -/
  params : List FunParam
  /-- Whether the function is variadic (takes ...) -/
  isVariadic : Bool
  /-- Whether the function has a prototype -/
  hasProto : Bool
  deriving Repr, Inhabited

/-- Function info map: symbol -> function type information
    Corresponds to: funinfo type in core.ott:557
    Audited: 2025-12-31
    Deviations: None -/
abbrev FunInfoMap := Std.HashMap Sym FunInfo

/-! ## Core File

Corresponds to: core.ott lines 547-560 (generic_file)
```lem
type generic_file 'bty 'a = <|
  main    : maybe Symbol.sym;
  tagDefs : core_tag_definitions;
  stdlib  : generic_fun_map 'bty 'a;
  impl    : generic_impl 'bty;
  globs   : list (Symbol.sym * generic_globs 'a 'bty);
  funs    : generic_fun_map 'bty 'a;
  extern  : extern_map;
  funinfo : map Symbol.sym (Loc.t * Annot.attributes * ctype * list (maybe Symbol.sym * ctype) * bool * bool);
  loop_attributes : Annot.loop_attributes;
  visible_objects_env: visible_objects_env;
|>
```
-/

/-- A complete Core program file
    Corresponds to: generic_file in core.ott:547-560
    Audited: 2025-12-31
    Deviations: None -/
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
  /-- Function type information (for cfunction expression) -/
  funinfo : FunInfoMap := {}
  /-- Loop attributes for CN verification -/
  loopAttributes : LoopAttributes := []
  /-- Visible objects environment for marker scopes -/
  visibleObjectsEnv : VisibleObjectsEnv := []

instance : Inhabited File := ⟨{}⟩

/-- Create an empty Core file (internal helper) -/
def File.empty : File := {}

/-- Look up function info by symbol name (internal helper)
    Note: This is a workaround because pointer values in JSON are exported as strings,
    losing the symbol ID. We look up by name only, which works in practice since
    function names are unique within a translation unit. -/
def File.lookupFunInfoByName (file : File) (name : Option String) : Option FunInfo :=
  file.funinfo.toList.find? (fun (sym, _) => sym.name == name) |>.map (·.2)

end CerbLean.Core
