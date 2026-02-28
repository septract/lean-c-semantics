/-
  Typing Rules for Core Proof System

  Defines the typing context, label invariants, and the main typing
  judgments (PureHasType and HasType) for reasoning about Core expressions
  in a separation-logic setting.

  The judgments use CN base types (CerbLean.CN.Types.BaseType) as the
  return type of expressions, since the proof system reasons at the
  specification level.
-/

import CerbLean.ProofSystem.SLProp
import CerbLean.ProofSystem.Convert  -- for ofPrecondition/ofPostcondition in proc
import CerbLean.ProofSystem.Models   -- for SLProp.entails in consequence
import CerbLean.Core.Expr
import CerbLean.Core.Value
import CerbLean.CN.Types.Spec
import CerbLean.CN.Types.Base
import CerbLean.Core.Types

namespace CerbLean.ProofSystem

open CerbLean.Core (Sym Ctype Identifier AExpr Expr APexpr Pexpr APattern Pattern
                     Paction Annots Binop Value LoadedValue ObjectValue
                     Action AAction MemoryOrder Polarity KillKind SymPrefix Loc Name)
open CerbLean.CN.Types (IndexTerm LogicalConstraint FunctionSpec Init QPredicate
                         Term AnnotTerm BinOp UnOp)

/-- CN base types, used as the return type of the typing judgment.
    Aliased to disambiguate from CerbLean.Core.BaseType. -/
abbrev CNBaseType := CerbLean.CN.Types.BaseType

/-! ## Helper Functions -/

/-- Convert a Core Pexpr to an IndexTerm for use in path conditions.
    Only handles simple cases (symbol references). -/
def condTermOfPexpr : Pexpr → Option IndexTerm
  | .sym s => some (AnnotTerm.mk (.sym s) .bool default)
  | _ => none

/-- Negate an index term by wrapping in logical NOT. -/
def negateIndexTerm (it : IndexTerm) : IndexTerm :=
  AnnotTerm.mk (.unop .not it) .bool default

/-- Determine the CN base type of a Core binary operation result.
    Arithmetic ops preserve the left operand's type; comparison/logical ops return bool. -/
def opResultType : Binop → CNBaseType → CNBaseType → Option CNBaseType
  | .add, τ, _ | .sub, τ, _ | .mul, τ, _ | .div, τ, _
  | .rem_t, τ, _ | .rem_f, τ, _ | .exp, τ, _ => some τ
  | .eq, _, _ | .gt, _, _ | .lt, _, _ | .ge, _, _ | .le, _, _
  | .and, _, _ | .or, _, _ => some .bool

/-! ## Value-Type Compatibility -/

/-- Relates a Core value to its CN base type.
    Used as a premise in `PureHasType.val` to ensure the value actually
    matches the claimed type. -/
def valueHasType : Value → CNBaseType → Prop
  | .loaded (.specified (.integer _)), .bits _ _ => True
  | .loaded (.specified (.integer _)), .integer => True
  | .loaded (.specified (.pointer _)), .loc => True
  | .unit, .unit => True
  | .true_, .bool => True
  | .false_, .bool => True
  | .ctype _, .ctype => True
  | _, _ => False  -- FIXME: extend for structs, arrays, etc.

/-! ## Label Invariant -/

/-- Loop label invariant — describes the contract for a `save`/`run` label.
    The invariant is a separation-logic proposition that must hold on each
    iteration, and the parameters are the bindings available inside the loop body. -/
structure LabelInv where
  /-- Parameter bindings available to the loop body -/
  params : List (Sym × CNBaseType)
  /-- The separation-logic invariant that must hold at the label -/
  invariant : SLProp

/-! ## Typing Context -/

/-- Typing context for the Core proof system.
    Collects variable bindings, path conditions, function specs,
    loop invariants, and struct definitions. -/
structure Ctx where
  /-- Variable type bindings: (symbol, CN base type) -/
  vars : List (Sym × CNBaseType)
  /-- Path conditions accumulated from conditionals -/
  pathConds : List LogicalConstraint
  /-- Known function specifications -/
  funSpecs : List (Sym × FunctionSpec)
  /-- Loop label invariants -/
  labelInvs : List (Sym × LabelInv)
  /-- Struct tag definitions: (tag, list of (field name, field ctype)) -/
  tagDefs : List (Sym × List (Identifier × Ctype))

namespace Ctx

/-- Empty context with no bindings -/
def empty : Ctx :=
  { vars := [], pathConds := [], funSpecs := [], labelInvs := [], tagDefs := [] }

/-- Add a variable binding to the context -/
def addVar (ctx : Ctx) (s : Sym) (ty : CNBaseType) : Ctx :=
  { ctx with vars := (s, ty) :: ctx.vars }

/-- Look up a variable's type in the context -/
def lookupVar (ctx : Ctx) (s : Sym) : Option CNBaseType :=
  ctx.vars.find? (·.1 == s) |>.map (·.2)

/-- Look up a function specification in the context -/
def lookupFunSpec (ctx : Ctx) (s : Sym) : Option FunctionSpec :=
  ctx.funSpecs.find? (·.1 == s) |>.map (·.2)

/-- Look up a label invariant in the context -/
def lookupLabelInv (ctx : Ctx) (s : Sym) : Option LabelInv :=
  ctx.labelInvs.find? (·.1 == s) |>.map (·.2)

/-- Add a path condition to the context -/
def addPathCond (ctx : Ctx) (lc : LogicalConstraint) : Ctx :=
  { ctx with pathConds := lc :: ctx.pathConds }

/-- Add multiple parameter bindings to the context (for loop invariant params). -/
def addParams (ctx : Ctx) (params : List (Sym × CNBaseType)) : Ctx :=
  params.foldl (fun acc (s, ty) => acc.addVar s ty) ctx

end Ctx

/-- Add variable bindings from a pattern match branch into the context.
    For base patterns with a named variable, the binding type must be
    supplied externally (from the scrutinee type). -/
def Ctx.addPatternBinding (ctx : Ctx) (pat : APattern) (τ : CNBaseType) : Ctx :=
  match pat.pat with
  | .base (some x) _bty => ctx.addVar x τ
  | _ => ctx

/-! ## Pure Expression Typing -/

/-- Typing judgment for pure expressions (Pexpr).

    `PureHasType Γ pe τ` means: in context Γ, annotated pure expression `pe`
    has CN base type `τ`. Pure expressions have no heap effects. -/
inductive PureHasType : Ctx → APexpr → CNBaseType → Prop where
  /-- A value literal has the claimed type, provided the value matches it.
      The `valueHasType` premise ensures the Core value is compatible with
      the claimed CN base type. -/
  | val : ∀ {Γ : Ctx} {annots : Annots} {coreTy} {v : Value} {τ : CNBaseType},
    valueHasType v τ →
    PureHasType Γ ⟨annots, coreTy, .val v⟩ τ
  /-- A symbol reference has the type from the context. -/
  | sym : ∀ {Γ : Ctx} {annots : Annots} {s : Sym} {coreTy} {τ : CNBaseType},
    Γ.lookupVar s = some τ →
    PureHasType Γ ⟨annots, coreTy, .sym s⟩ τ
  /-- A binary operation: if both operands type-check and the operator
      is well-typed, the result has the appropriate type.
      The `opResultType` premise constrains the result type based on the
      operator and operand types. -/
  | op : ∀ {Γ : Ctx} {annots : Annots} {coreTy} {binop : Binop}
      {e₁ e₂ : Pexpr} {τ₁ τ₂ τ : CNBaseType},
    PureHasType Γ ⟨annots, coreTy, e₁⟩ τ₁ →
    PureHasType Γ ⟨annots, coreTy, e₂⟩ τ₂ →
    opResultType binop τ₁ τ₂ = some τ →
    PureHasType Γ ⟨annots, coreTy, .op binop e₁ e₂⟩ τ
  /-- A conditional pure expression: if the condition is boolean and both
      branches have the same type, the result has that type. -/
  | if_ : ∀ {Γ : Ctx} {annots : Annots} {coreTy}
      {cond then_ else_ : Pexpr} {τ : CNBaseType},
    PureHasType Γ ⟨annots, coreTy, cond⟩ .bool →
    PureHasType Γ ⟨annots, coreTy, then_⟩ τ →
    PureHasType Γ ⟨annots, coreTy, else_⟩ τ →
    PureHasType Γ ⟨annots, coreTy, .if_ cond then_ else_⟩ τ

/-! ## Main Typing Judgment -/

/-- Main typing judgment for effectful Core expressions.

    `HasType Γ H₁ e τ H₂` means: in context Γ, starting with heap described
    by `H₁`, expression `e` has CN base type `τ` and produces heap `H₂`.

    This is a Hoare-triple-style judgment embedded in the typing relation:
    - `H₁` is the precondition (resources available before)
    - `H₂` is the postcondition (resources available after)
    - The frame rule allows carrying extra resources through unchanged. -/
inductive HasType : Ctx → SLProp → AExpr → CNBaseType → SLProp → Prop where
  /-- **Pure**: A pure expression does not change the heap.
      If `pe` has type `τ` in context `Γ`, then wrapping it as `Expr.pure pe`
      preserves the heap `H` unchanged. -/
  | pure : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots} {pe : APexpr} {τ : CNBaseType},
    PureHasType Γ pe τ →
    HasType Γ H ⟨annots, .pure pe⟩ τ H

  /-- **Let binding**: Bind a pure expression result in a body.
      If `pe` has type `τ₁`, and after binding `x : τ₁` the body has type `τ₂`,
      then the let expression has type `τ₂`. The heap threads through the body. -/
  | let_ : ∀ {Γ : Ctx} {H₁ H₂ : SLProp} {annots patAnnots : Annots}
      {x : Sym} {bty : CerbLean.Core.BaseType}
      {pe : APexpr} {body : AExpr} {τ₁ τ₂ : CNBaseType},
    PureHasType Γ pe τ₁ →
    HasType (Γ.addVar x τ₁) H₁ body τ₂ H₂ →
    HasType Γ H₁ ⟨annots, .let_ ⟨patAnnots, .base (some x) bty⟩ pe body⟩ τ₂ H₂

  /-- **Let binding (wildcard)**: Like `let_` but the pattern binds no variable.
      The result of the pure expression is discarded. -/
  | let_wild : ∀ {Γ : Ctx} {H₁ H₂ : SLProp} {annots patAnnots : Annots}
      {bty : CerbLean.Core.BaseType}
      {pe : APexpr} {body : AExpr} {τ₁ τ₂ : CNBaseType},
    PureHasType Γ pe τ₁ →
    HasType Γ H₁ body τ₂ H₂ →
    HasType Γ H₁ ⟨annots, .let_ ⟨patAnnots, .base none bty⟩ pe body⟩ τ₂ H₂

  /-- **Strong sequencing**: Sequence two effectful expressions.
      The first expression produces heap `H₂` which feeds into the second.
      The bound variable from the first expression is available in the second. -/
  | sseq : ∀ {Γ : Ctx} {H₁ H₂ H₃ : SLProp} {annots patAnnots : Annots}
      {x : Sym} {bty : CerbLean.Core.BaseType}
      {e₁ e₂ : AExpr} {τ₁ τ₂ : CNBaseType},
    HasType Γ H₁ e₁ τ₁ H₂ →
    HasType (Γ.addVar x τ₁) H₂ e₂ τ₂ H₃ →
    HasType Γ H₁ ⟨annots, .sseq ⟨patAnnots, .base (some x) bty⟩ e₁ e₂⟩ τ₂ H₃

  /-- **Strong sequencing (wildcard)**: Like `sseq` but the pattern binds no variable.
      The result of the first expression is discarded. -/
  | sseq_wild : ∀ {Γ : Ctx} {H₁ H₂ H₃ : SLProp} {annots patAnnots : Annots}
      {bty : CerbLean.Core.BaseType}
      {e₁ e₂ : AExpr} {τ₁ τ₂ : CNBaseType},
    HasType Γ H₁ e₁ τ₁ H₂ →
    HasType Γ H₂ e₂ τ₂ H₃ →
    HasType Γ H₁ ⟨annots, .sseq ⟨patAnnots, .base none bty⟩ e₁ e₂⟩ τ₂ H₃

  /-- **Weak sequencing**: Like strong sequencing, but for weakly-sequenced
      expressions. In Core, `wseq` and `sseq` differ only in concurrency
      semantics; for sequential execution they are equivalent. -/
  | wseq : ∀ {Γ : Ctx} {H₁ H₂ H₃ : SLProp} {annots patAnnots : Annots}
      {x : Sym} {bty : CerbLean.Core.BaseType}
      {e₁ e₂ : AExpr} {τ₁ τ₂ : CNBaseType},
    HasType Γ H₁ e₁ τ₁ H₂ →
    HasType (Γ.addVar x τ₁) H₂ e₂ τ₂ H₃ →
    HasType Γ H₁ ⟨annots, .wseq ⟨patAnnots, .base (some x) bty⟩ e₁ e₂⟩ τ₂ H₃

  /-- **Weak sequencing (wildcard)**: Like `wseq` but the pattern binds no variable. -/
  | wseq_wild : ∀ {Γ : Ctx} {H₁ H₂ H₃ : SLProp} {annots patAnnots : Annots}
      {bty : CerbLean.Core.BaseType}
      {e₁ e₂ : AExpr} {τ₁ τ₂ : CNBaseType},
    HasType Γ H₁ e₁ τ₁ H₂ →
    HasType Γ H₂ e₂ τ₂ H₃ →
    HasType Γ H₁ ⟨annots, .wseq ⟨patAnnots, .base none bty⟩ e₁ e₂⟩ τ₂ H₃

  /-- **Conditional**: Both branches must produce the same type and post-heap.
      The condition must be a boolean pure expression.
      The true branch gets the condition as a path condition; the else branch
      gets the negated condition. `condTermOfPexpr` connects the path condition
      to the actual condition expression. -/
  | if_ : ∀ {Γ : Ctx} {H₁ H₂ : SLProp} {annots : Annots}
      {cond : APexpr} {condTerm : IndexTerm}
      {thenBranch elseBranch : AExpr} {τ : CNBaseType},
    PureHasType Γ cond .bool →
    condTermOfPexpr cond.expr = some condTerm →
    HasType (Γ.addPathCond (.t condTerm)) H₁ thenBranch τ H₂ →
    HasType (Γ.addPathCond (.t (negateIndexTerm condTerm))) H₁ elseBranch τ H₂ →
    HasType Γ H₁ ⟨annots, .if_ cond thenBranch elseBranch⟩ τ H₂

  /-- **Case**: Pattern match on a scrutinee. The scrutinee must be well-typed.
      Each branch must produce the same type and post-heap.
      Pattern bindings from each branch are added to the context. -/
  | case_ : ∀ {Γ : Ctx} {H₁ H₂ : SLProp} {annots : Annots}
      {scrut : APexpr} {branches : List (APattern × AExpr)} {τ τs : CNBaseType},
    PureHasType Γ scrut τs →
    (∀ branch, branch ∈ branches →
      HasType (Γ.addPatternBinding branch.1 τs) H₁ branch.2 τ H₂) →
    HasType Γ H₁ ⟨annots, .case_ scrut branches⟩ τ H₂

  /-- **Bound**: Transparent wrapper (e.g., for stack depth tracking).
      Does not affect typing. -/
  | bound : ∀ {Γ : Ctx} {H₁ H₂ : SLProp} {annots : Annots}
      {e : AExpr} {τ : CNBaseType},
    HasType Γ H₁ e τ H₂ →
    HasType Γ H₁ ⟨annots, .bound e⟩ τ H₂

  -- Memory Action Rules

  /-- **Load**: Read from an owned pointer. Consumes and re-emits the
      `Owned<ct>(ptr,val)` resource — the heap is unchanged.
      Returns the value stored at the pointer — the return type is
      determined by the value's base type annotation (`val.bt`). -/
  | action_load : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots} {locAnn : Loc}
      {ct : Ctype} {ptr val : IndexTerm} {tyPe ptrPe : APexpr},
    HasType Γ (.star (.owned ct .init ptr val) R)
      ⟨annots, .action ⟨.pos, ⟨locAnn, .load tyPe ptrPe .na⟩⟩⟩
      val.bt
      (.star (.owned ct .init ptr val) R)

  /-- **Store**: Write to an owned pointer. Consumes `Owned<ct>(ptr,valOld)`
      and produces `Owned<ct>(ptr,valNew)` with the new value.
      The stored value expression must be well-typed. -/
  | action_store : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots} {locAnn : Loc}
      {ct : Ctype} {ptr valOld valNew : IndexTerm}
      {tyPe ptrPe valPe : APexpr} {τ : CNBaseType},
    PureHasType Γ valPe τ →
    HasType Γ (.star (.owned ct .init ptr valOld) R)
      ⟨annots, .action ⟨.pos, ⟨locAnn, .store false tyPe ptrPe valPe .na⟩⟩⟩
      .unit
      (.star (.owned ct .init ptr valNew) R)

  /-- **Create**: Allocate fresh memory. Produces a `Block<ct>(ptr)` resource
      representing the newly allocated (but uninitialized) memory.
      Returns the pointer (type `loc`). -/
  | action_create : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots} {locAnn : Loc}
      {ct : Ctype} {ptr : IndexTerm} {alignPe sizePe : APexpr} {prefix_ : SymPrefix},
    HasType Γ H
      ⟨annots, .action ⟨.pos, ⟨locAnn, .create alignPe sizePe prefix_⟩⟩⟩
      .loc
      (.star (.block ct ptr) H)

  /-- **Kill (owned)**: Deallocate memory that has an `Owned` resource.
      Consumes the `Owned<ct>(ptr,val)` resource, leaving the remainder. -/
  | action_kill_owned : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots} {locAnn : Loc}
      {ct : Ctype} {initState : Init} {ptr val : IndexTerm}
      {ptrPe : APexpr} {kind : KillKind},
    HasType Γ (.star (.owned ct initState ptr val) R)
      ⟨annots, .action ⟨.pos, ⟨locAnn, .kill kind ptrPe⟩⟩⟩
      .unit R

  /-- **Kill (block)**: Deallocate memory that has a `Block` resource.
      Consumes the `Block<ct>(ptr)` resource, leaving the remainder. -/
  | action_kill_block : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots} {locAnn : Loc}
      {ct : Ctype} {ptr : IndexTerm} {ptrPe : APexpr} {kind : KillKind},
    HasType Γ (.star (.block ct ptr) R)
      ⟨annots, .action ⟨.pos, ⟨locAnn, .kill kind ptrPe⟩⟩⟩
      .unit R

  -- Procedure Calls

  /-- **Procedure call**: Call a named function with a known specification.
      Consumes precondition resources and produces postcondition resources.
      Pre/post SLProps are derived directly from the spec's requires/ensures. -/
  | proc : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots}
      {s : Sym} {args : List APexpr}
      {spec : FunctionSpec} {τ : CNBaseType},
    Γ.lookupFunSpec s = some spec →
    HasType Γ (.star (SLProp.ofPrecondition spec.requires) R)
      ⟨annots, .proc (Name.sym s) args⟩
      τ
      (.star (SLProp.ofPostcondition spec.ensures) R)

  /-- **C function call through pointer**: Like `proc` but the function is
      identified by a pointer expression rather than a direct symbol. The
      specification must be supplied (in a full system, connected via the
      function pointer's type annotation).
      The function pointer must be well-typed as a location (pointer). -/
  | ccall : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots}
      {funPtr funTy : APexpr} {args : List APexpr}
      {spec : FunctionSpec} {τ : CNBaseType},
    PureHasType Γ funPtr .loc →
    HasType Γ (.star (SLProp.ofPrecondition spec.requires) R)
      ⟨annots, .ccall funPtr funTy args⟩
      τ
      (.star (SLProp.ofPostcondition spec.ensures) R)

  -- Continuations (Loops)

  /-- **Save (label definition)**: Define a labeled continuation for looping.
      The body type-checks under the loop invariant, with invariant parameters
      bound in the context. The precondition must satisfy the invariant for
      the initial argument values.
      Corresponds to Core `Esave`: evaluates default args, then executes body.
      The body may use `run` to loop back. -/
  | save : ∀ {Γ : Ctx} {H₂ : SLProp} {annots : Annots}
      {retSym : Sym} {retTy : CerbLean.Core.BaseType}
      {params : List (Sym × CerbLean.Core.BaseType × APexpr)}
      {body : AExpr} {τ : CNBaseType} {inv : LabelInv},
    Γ.lookupLabelInv retSym = some inv →
    HasType (Γ.addParams inv.params) inv.invariant body τ H₂ →
    HasType Γ inv.invariant ⟨annots, .save retSym retTy params body⟩ τ H₂

  /-- **Run (continuation jump)**: Jump to a labeled continuation.
      The precondition must satisfy the label's invariant.
      Since `run` transfers control (does not return), the return type `τ`
      and post-heap `H₂` are unconstrained — like `absurd` or divergence.
      Corresponds to Core `Erun`: evaluates args and restarts the label body. -/
  | run : ∀ {Γ : Ctx} {H₂ : SLProp} {annots : Annots}
      {label : Sym} {args : List APexpr}
      {inv : LabelInv} {τ : CNBaseType},
    Γ.lookupLabelInv label = some inv →
    HasType Γ inv.invariant ⟨annots, .run label args⟩ τ H₂

  -- Structural Rules

  /-- **Frame rule**: Extra resources `R` can be carried through unchanged.
      This is the key structural rule of separation logic: if an expression
      only needs `H₁` and produces `H₂`, then it also works when extra
      disjoint resources `R` are present, and those resources are preserved. -/
  | frame : ∀ {Γ : Ctx} {H₁ H₂ : SLProp} {e : AExpr} {τ : CNBaseType}
      {R : SLProp},
    HasType Γ H₁ e τ H₂ →
    HasType Γ (.star H₁ R) e τ (.star H₂ R)

  /-- **Consequence**: Strengthen the pre-heap or weaken the post-heap.
      Uses semantic entailment (`SLProp.entails`) instead of equality,
      allowing the rule to bridge between logically equivalent but
      syntactically different heap descriptions. -/
  | consequence : ∀ {Γ : Ctx} {H₁ H₁' H₂ H₂' : SLProp} {e : AExpr} {τ : CNBaseType},
    SLProp.entails H₁' H₁ →
    SLProp.entails H₂ H₂' →
    HasType Γ H₁ e τ H₂ →
    HasType Γ H₁' e τ H₂'

end CerbLean.ProofSystem
