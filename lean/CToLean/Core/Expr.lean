/-
  Core IR expression AST
  Based on cerberus/frontend/ott/core-ott/core.ott lines 287-434
-/

import CToLean.Core.Types
import CToLean.Core.Value
import CToLean.Core.Annot
import CToLean.Core.Undefined

namespace CToLean.Core

/-! ## Names -/

/-- Implementation-defined constants -/
inductive ImplConst where
  | intMax (ty : IntegerType)
  | intMin (ty : IntegerType)
  | sizeof_ (ty : Ctype)
  | alignof_ (ty : Ctype)
  | other (name : String)
  deriving Repr, BEq, Inhabited

/-- Names in Core (either symbols or implementation constants) -/
inductive Name where
  | sym (s : Sym)
  | impl (c : ImplConst)
  deriving Repr, BEq, Inhabited

/-! ## Patterns -/

/-- Pattern for matching -/
inductive Pattern where
  | base (sym : Option Sym) (ty : BaseType)
  | ctor (c : Ctor) (args : List Pattern)
  deriving Repr, Inhabited

/-- Annotated pattern -/
structure APattern where
  annots : Annots
  pat : Pattern
  deriving Repr, Inhabited

/-! ## Pure Expressions -/

/-- Pure expressions (no side effects) -/
inductive Pexpr : Type where
  | sym (s : Sym)
  | impl (c : ImplConst)
  | val (v : Value)
  | undef (loc : Loc) (ub : UndefinedBehavior)
  | error (msg : String) (e : Pexpr)
  | ctor (c : Ctor) (args : List Pexpr)
  | case_ (scrut : Pexpr) (branches : List (APattern × Pexpr))
  | arrayShift (ptr : Pexpr) (ty : Ctype) (idx : Pexpr)
  | memberShift (ptr : Pexpr) (tag : Sym) (member : Identifier)
  | not_ (e : Pexpr)
  | op (op : Binop) (e1 : Pexpr) (e2 : Pexpr)
  | struct_ (tag : Sym) (members : List (Identifier × Pexpr))
  | union_ (tag : Sym) (member : Identifier) (value : Pexpr)
  | cfunction (e : Pexpr)
  | memberof (tag : Sym) (member : Identifier) (e : Pexpr)
  | call (name : Name) (args : List Pexpr)
  | let_ (pat : APattern) (e1 : Pexpr) (e2 : Pexpr)
  | if_ (cond : Pexpr) (then_ : Pexpr) (else_ : Pexpr)
  | isScalar (e : Pexpr)
  | isInteger (e : Pexpr)
  | isSigned (e : Pexpr)
  | isUnsigned (e : Pexpr)
  | areCompatible (e1 : Pexpr) (e2 : Pexpr)
  -- Integer conversion and overflow operations
  | convInt (ty : IntegerType) (e : Pexpr)
  | wrapI (ty : IntegerType) (op : Iop) (e1 : Pexpr) (e2 : Pexpr)
  | catchExceptionalCondition (ty : IntegerType) (op : Iop) (e1 : Pexpr) (e2 : Pexpr)
  -- BMC assume (for model checking)
  | bmcAssume (e : Pexpr)
  -- Pure memory operations
  | pureMemop (op : String) (args : List Pexpr)
  -- Constrained values (for memory model)
  | constrained (constraints : List (String × Pexpr))

instance : Inhabited Pexpr := ⟨.val .unit⟩

/-- Annotated pure expression with optional type -/
structure APexpr where
  annots : Annots
  ty : Option BaseType  -- type annotation (for typed Core)
  expr : Pexpr

instance : Inhabited APexpr := ⟨{ annots := [], ty := none, expr := default }⟩

/-! ## Memory Actions -/

/-- Memory actions -/
inductive Action where
  | create (align : APexpr) (size : APexpr) (prefix_ : SymPrefix)
  | createReadonly (align : APexpr) (size : APexpr) (init : APexpr) (prefix_ : SymPrefix)
  | alloc (align : APexpr) (size : APexpr) (prefix_ : SymPrefix)
  | kill (kind : KillKind) (ptr : APexpr)
  | store (locking : Bool) (ty : APexpr) (ptr : APexpr) (val : APexpr) (order : MemoryOrder)
  | load (ty : APexpr) (ptr : APexpr) (order : MemoryOrder)
  | rmw (ty : APexpr) (ptr : APexpr) (expected : APexpr) (desired : APexpr)
      (successOrd : MemoryOrder) (failOrd : MemoryOrder)
  | fence (order : MemoryOrder)
  | compareExchangeStrong (ty : APexpr) (ptr : APexpr) (expected : APexpr) (desired : APexpr)
      (successOrd : MemoryOrder) (failOrd : MemoryOrder)
  | compareExchangeWeak (ty : APexpr) (ptr : APexpr) (expected : APexpr) (desired : APexpr)
      (successOrd : MemoryOrder) (failOrd : MemoryOrder)
  -- Sequential read-modify-write (for BMC)
  | seqRmw (isUpdate : Bool) (ty : APexpr) (ptr : APexpr) (sym : Sym) (val : APexpr)
  deriving Inhabited

/-- Annotated action with location -/
structure AAction where
  loc : Loc
  action : Action
  deriving Inhabited

/-- Polarized action -/
structure Paction where
  polarity : Polarity
  action : AAction
  deriving Inhabited

/-! ## Effectful Expressions -/

/-- Effectful expressions (can have side effects) -/
inductive Expr where
  | pure (e : APexpr)
  | memop (op : Memop) (args : List APexpr)
  | action (a : Paction)
  | case_ (scrut : APexpr) (branches : List (APattern × Expr))
  | let_ (pat : APattern) (e1 : APexpr) (e2 : Expr)
  | if_ (cond : APexpr) (then_ : Expr) (else_ : Expr)
  | ccall (funPtr : APexpr) (funTy : APexpr) (args : List APexpr)
  | proc (name : Name) (args : List APexpr)
  -- Sequencing (for concurrency - we focus on sequential for now)
  | unseq (es : List Expr)       -- unsequenced
  | wseq (pat : APattern) (e1 : Expr) (e2 : Expr)  -- weak sequencing
  | sseq (pat : APattern) (e1 : Expr) (e2 : Expr)  -- strong sequencing
  | bound (e : Expr)
  | nd (es : List Expr)          -- nondeterministic choice
  | save (retSym : Sym) (retTy : BaseType) (args : List (Sym × BaseType × APexpr)) (body : Expr)
  | run (label : Sym) (args : List APexpr)
  -- Concurrency (out of scope initially)
  | par (es : List Expr)
  | wait (tid : Nat)
  deriving Inhabited

/-- Annotated expression -/
structure AExpr where
  annots : Annots
  expr : Expr
  deriving Inhabited

end CToLean.Core
