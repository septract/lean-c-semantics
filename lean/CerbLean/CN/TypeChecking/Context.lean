/-
  CN Typing Context
  Corresponds to: cn/lib/context.ml

  The typing context tracks the state during type checking:
  - Computational variables (C-level variables)
  - Logical variables (ghost/specification variables)
  - Resources (separation logic ownership predicates)
  - Constraints (logical constraints that must hold)

  Audited: 2026-01-20 against cn/lib/context.ml
-/

import CerbLean.CN.Types

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types

/-! ## Binding Types

Corresponds to: cn/lib/context.ml lines 13-19
```ocaml
type basetype_or_value =
  | BaseType of BT.t
  | Value of IndexTerms.t
```
-/

/-- A binding can be either a type (variable declared but not defined)
    or a concrete value (variable with known value).
    Corresponds to: basetype_or_value in context.ml lines 13-14 -/
inductive BaseTypeOrValue where
  | baseType (bt : BaseType)
  | value (it : IndexTerm)
  deriving Inhabited

namespace BaseTypeOrValue

/-- Get the base type of a binding
    Corresponds to: bt_of in context.ml line 17 -/
def bt : BaseTypeOrValue → BaseType
  | baseType bt => bt
  | value it => it.bt

/-- Check if binding has a concrete value
    Corresponds to: has_value in context.ml line 19 -/
def hasValue : BaseTypeOrValue → Bool
  | baseType _ => false
  | value _ => true

end BaseTypeOrValue

/-! ## Location Info

Corresponds to: cn/lib/context.ml lines 7-10
```ocaml
type l_info = Locations.t * Pp.document Lazy.t
```
-/

/-- Location and description for a binding
    Corresponds to: l_info in context.ml line 7 -/
structure LInfo where
  loc : Loc
  description : String
  deriving Repr, Inhabited

/-! ## Typing Context

Corresponds to: cn/lib/context.ml lines 21-28
```ocaml
type t =
  { computational : (basetype_or_value * l_info) Sym.Map.t;
    logical : (basetype_or_value * l_info) Sym.Map.t;
    resources : Res.t list;
    constraints : LC.Set.t;
    global : Global.t;
    where : Where.t
  }
```
-/

/-- The typing context tracks all state during type checking.
    Corresponds to: t in context.ml lines 21-28
    Note: We omit `global` and `where` for now (they're for error reporting) -/
structure Context where
  /-- Computational variable bindings (C variables) -/
  computational : List (Sym × BaseTypeOrValue × LInfo)
  /-- Logical variable bindings (ghost/specification variables) -/
  logical : List (Sym × BaseTypeOrValue × LInfo)
  /-- Current resources (separation logic ownership) -/
  resources : List Resource
  /-- Logical constraints that must hold -/
  constraints : LCSet
  deriving Inhabited

namespace Context

/-- Empty context
    Corresponds to: empty in context.ml lines 30-42 -/
def empty : Context :=
  { computational := []
  , logical := []
  , resources := []
  , constraints := LCSet.empty }

/-! ### Variable Lookups

Corresponds to: context.ml lines 75-91
-/

/-- Check if a computational variable is bound
    Corresponds to: bound_a in context.ml line 75 -/
def boundA (s : Sym) (ctx : Context) : Bool :=
  ctx.computational.any fun (s', _, _) => s'.id == s.id

/-- Check if a logical variable is bound
    Corresponds to: bound_l in context.ml line 77 -/
def boundL (s : Sym) (ctx : Context) : Bool :=
  ctx.logical.any fun (s', _, _) => s'.id == s.id

/-- Check if any variable is bound
    Corresponds to: bound in context.ml line 79 -/
def bound (s : Sym) (ctx : Context) : Bool :=
  ctx.boundA s || ctx.boundL s

/-- Get a computational variable binding
    Corresponds to: get_a in context.ml lines 81-84 -/
def getA (s : Sym) (ctx : Context) : Option BaseTypeOrValue :=
  ctx.computational.find? (fun (s', _, _) => s'.id == s.id) |>.map (·.2.1)

/-- Get a logical variable binding
    Corresponds to: get_l in context.ml lines 87-90 -/
def getL (s : Sym) (ctx : Context) : Option BaseTypeOrValue :=
  ctx.logical.find? (fun (s', _, _) => s'.id == s.id) |>.map (·.2.1)

/-! ### Adding Bindings

Corresponds to: context.ml lines 93-109
-/

/-- Add a computational variable with just a type
    Corresponds to: add_a in context.ml line 98 -/
def addA (s : Sym) (bt : BaseType) (info : LInfo) (ctx : Context) : Context :=
  { ctx with computational := (s, .baseType bt, info) :: ctx.computational }

/-- Add a computational variable with a known value
    Corresponds to: add_a_value in context.ml line 100 -/
def addAValue (s : Sym) (v : IndexTerm) (info : LInfo) (ctx : Context) : Context :=
  { ctx with computational := (s, .value v, info) :: ctx.computational }

/-- Add a logical variable with just a type
    Corresponds to: add_l in context.ml line 107 -/
def addL (s : Sym) (bt : BaseType) (info : LInfo) (ctx : Context) : Context :=
  { ctx with logical := (s, .baseType bt, info) :: ctx.logical }

/-- Add a logical variable with a known value
    Corresponds to: add_l_value in context.ml line 109 -/
def addLValue (s : Sym) (v : IndexTerm) (info : LInfo) (ctx : Context) : Context :=
  { ctx with logical := (s, .value v, info) :: ctx.logical }

/-! ### Moving Variables Between Scopes

Corresponds to: context.ml lines 114-121
-/

/-- Move a computational variable to logical scope.
    Corresponds to: remove_a in context.ml:114-121 -/
def removeA (s : Sym) (ctx : Context) : Context :=
  match ctx.computational.find? (fun (s', _, _) => s'.id == s.id) with
  | some entry =>
    { ctx with
      computational := ctx.computational.filter (fun (s', _, _) => s'.id != s.id)
      logical := entry :: ctx.logical }
  | none => ctx

/-! ### Constraints

Corresponds to: context.ml lines 123-128
-/

/-- Add a constraint to the context
    Corresponds to: add_c in context.ml lines 123-128
    Note: We don't check for duplicates since LogicalConstraint lacks BEq.
    Duplicates don't affect semantics. -/
def addC (lc : LogicalConstraint) (ctx : Context) : Context :=
  { ctx with constraints := LCSet.add lc ctx.constraints }

/-! ### Resources

Corresponds to: context.ml lines 45, 148
-/

/-- Get the list of resources
    Corresponds to: get_rs in context.ml line 45 -/
def getResources (ctx : Context) : List Resource := ctx.resources

/-- Add a resource to the context
    Corresponds to: add_r in context.ml line 148 -/
def addR (r : Resource) (ctx : Context) : Context :=
  { ctx with resources := r :: ctx.resources }

/-- Remove a resource at the given index from the context (for consumption) -/
def removeRAt (idx : Nat) (ctx : Context) : Context :=
  { ctx with resources := ctx.resources.eraseIdx idx }

/-- Replace all resources in the context -/
def setResources (rs : List Resource) (ctx : Context) : Context :=
  { ctx with resources := rs }

end Context

end CerbLean.CN.TypeChecking
