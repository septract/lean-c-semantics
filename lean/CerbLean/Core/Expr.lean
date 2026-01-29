/-
  Core IR expression AST

  Corresponds to: cerberus/frontend/ott/core-ott/core.ott
  Audited: 2025-12-31
  Deviations: None
-/

import CerbLean.Core.Types
import CerbLean.Core.Value
import CerbLean.Core.Annot
import CerbLean.Core.Undefined
import CerbLean.Core.DynAnnot

namespace CerbLean.Core

/-! ## Names -/

/-- Implementation-defined constants
    Corresponds to: Implementation__implementation_constant in core.ott lines 181-184
    Audited: 2025-12-31
    Deviations: None -/
inductive ImplConst where
  | intMax (ty : IntegerType)
  | intMin (ty : IntegerType)
  | sizeof_ (ty : Ctype)
  | alignof_ (ty : Ctype)
  | other (name : String)
  deriving Repr, BEq, Inhabited

/-- Names in Core (either symbols or implementation constants)
    Corresponds to: generic_name in core.ott lines 190-192
    Audited: 2025-12-31
    Deviations: None -/
inductive Name where
  | sym (s : Sym)
  | impl (c : ImplConst)
  deriving Repr, BEq, Inhabited

/-! ## Patterns -/

/-- Pattern for matching
    Corresponds to: generic_pattern_aux in core.ott lines 292-294
    Audited: 2025-12-31
    Deviations: None -/
inductive Pattern where
  | base (sym : Option Sym) (ty : BaseType)
  | ctor (c : Ctor) (args : List Pattern)
  deriving Repr, Inhabited

/-- Annotated pattern
    Corresponds to: generic_pattern in core.ott lines 296-297
    Audited: 2025-12-31
    Deviations: None -/
structure APattern where
  annots : Annots
  pat : Pattern
  deriving Repr, Inhabited

/-! ## Pure Expressions -/

/-- Pure expressions (no side effects)
    Corresponds to: generic_pexpr_aux in core.ott lines 309-334
    Audited: 2025-12-31
    Deviations: None -/
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

/-- Annotated pure expression with optional type
    Corresponds to: generic_pexpr in core.ott lines 336-337
    Audited: 2025-12-31
    Deviations: None -/
structure APexpr where
  annots : Annots
  ty : Option BaseType  -- type annotation (for typed Core)
  expr : Pexpr

instance : Inhabited APexpr := ⟨{ annots := [], ty := none, expr := default }⟩

/-! ## Memory Actions -/

/-- Memory actions
    Corresponds to: generic_action_aux in core.ott lines 363-377
    Audited: 2025-12-31
    Deviations: Linux-specific actions (LinuxFence, LinuxLoad, etc.) not included -/
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

/-- Annotated action with location
    Corresponds to: generic_action in core.ott lines 379-380
    Audited: 2025-12-31
    Deviations: None -/
structure AAction where
  loc : Loc
  action : Action
  deriving Inhabited

/-- Polarized action (memory action with polarity for sequencing)
    Corresponds to: generic_paction in core.ott lines 382-385
    Audited: 2025-12-31
    Deviations: None -/
structure Paction where
  polarity : Polarity
  action : AAction
  deriving Inhabited

/-! ## Effectful Expressions

In Cerberus (core.ott lines 413-434):
- `generic_expr_aux` is the inner expression type (our `Expr`)
- `generic_expr` is `annots generic_expr_aux` (our `AExpr`)
- `Ewseq` and `Esseq` take `generic_expr` (annotated expressions)

To match Cerberus exactly, `Expr` and `AExpr` must be mutually recursive.
-/

mutual
  /-- Effectful expressions (can have side effects)
      Corresponds to: generic_expr_aux in core.ott lines 413-430
      Audited: 2025-12-31
      Deviations: None
      CRITICAL: Sequencing constructs (wseq, sseq, etc.) take AExpr to match Cerberus -/
  inductive Expr where
    | pure (e : APexpr)
    | memop (op : Memop) (args : List APexpr)
    | action (a : Paction)
    | case_ (scrut : APexpr) (branches : List (APattern × AExpr))
    | let_ (pat : APattern) (e1 : APexpr) (e2 : AExpr)
    | if_ (cond : APexpr) (then_ : AExpr) (else_ : AExpr)
    | ccall (funPtr : APexpr) (funTy : APexpr) (args : List APexpr)
    | proc (name : Name) (args : List APexpr)
    -- Sequencing (for concurrency - we focus on sequential for now)
    | unseq (es : List AExpr)       -- unsequenced
    | wseq (pat : APattern) (e1 : AExpr) (e2 : AExpr)  -- weak sequencing
    | sseq (pat : APattern) (e1 : AExpr) (e2 : AExpr)  -- strong sequencing
    | bound (e : AExpr)
    | nd (es : List AExpr)          -- nondeterministic choice
    | save (retSym : Sym) (retTy : BaseType) (args : List (Sym × BaseType × APexpr)) (body : AExpr)
    | run (label : Sym) (args : List APexpr)
    -- Concurrency (out of scope initially)
    | par (es : List AExpr)
    | wait (tid : Nat)
    -- Dynamic annotations for race detection
    -- Corresponds to: Eannot in core.lem:339
    -- Audited: 2026-01-28
    | annot (dynAnnots : DynAnnotations) (e : AExpr)
    -- Excluded wrapper for neg action transformation
    -- Corresponds to: Eexcluded in core.lem:337
    -- The exclusion ID is used to mark the action's annotation with DA_neg
    -- Audited: 2026-01-28
    | excluded (exclId : Nat) (act : Paction)

  /-- Annotated expression
      Corresponds to: generic_expr in core.ott lines 432-433
      Audited: 2025-12-31
      Deviations: None -/
  structure AExpr where
    annots : Annots
    expr : Expr
end

instance : Inhabited Expr := ⟨.pure default⟩
instance : Inhabited AExpr := ⟨{ annots := [], expr := default }⟩

end CerbLean.Core
