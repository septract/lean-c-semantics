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

open CerbLean.Core (Sym Ctype Ctype_ Identifier AExpr Expr APexpr Pexpr APattern Pattern
                     Paction Annots Binop Iop Value LoadedValue ObjectValue
                     Action AAction MemoryOrder Polarity KillKind SymPrefix Loc Name
                     IntegerType IntBaseKind BasicType Memop)
open CerbLean.CN.Types (IndexTerm LogicalConstraint FunctionSpec Precondition
                         Init QPredicate Term AnnotTerm BinOp UnOp Subst BaseType)

/-- CN base types, used as the return type of the typing judgment.
    Aliased to disambiguate from CerbLean.Core.BaseType. -/
abbrev CNBaseType := CerbLean.CN.Types.BaseType

/-! ## Helper Functions -/

/-- Width in bits for each integer base kind.
    Delegates to `IntBaseKind.width` (Core/IntegerType.lean).
    Uses LP64 data model (matching Cerberus default target). -/
def intBaseKindWidth (k : IntBaseKind) : Nat := k.width

/-- Map a Core `IntegerType` to a CN `BaseType`.
    Used to constrain the result type of `convInt` and `wrapI` rules. -/
def intTypeToBaseType : IntegerType → CNBaseType
  | .signed k => .bits .signed (intBaseKindWidth k)
  | .unsigned k => .bits .unsigned (intBaseKindWidth k)
  | .char => .bits .unsigned 8       -- char signedness impl-defined, use unsigned
  | .bool => .bool
  | .enum _ => .bits .signed 32      -- enums are int-width
  | .size_t => .bits .unsigned 64    -- LP64
  | .wchar_t => .bits .signed 32
  | .wint_t => .bits .signed 32
  | .ptrdiff_t => .bits .signed 64   -- LP64
  | .ptraddr_t => .bits .unsigned 64 -- CHERI, treat as pointer-width

/-- Convert the inner Ctype_ to a CN BaseType. Structurally recursive on Ctype_.
    Handles array (→ list) and atomic (→ unwrap) types. -/
private def ctype_ToBaseType : Ctype_ → Option CNBaseType
  | .basic (.integer ity) => some (intTypeToBaseType ity)
  | .basic (.floating _) => some .real
  | .pointer _ _ => some .loc
  | .struct_ tag => some (.struct_ tag)
  | .union_ tag => some (.struct_ tag)
  | .void => some .unit
  | .array elem _ => ctype_ToBaseType elem |>.map (.list ·)
  | .atomic inner => ctype_ToBaseType inner
  | _ => none

def ctypeToBaseType (ct : Ctype) : Option CNBaseType :=
  ctype_ToBaseType ct.ty

/-- Negate an index term by wrapping in logical NOT. -/
def negateIndexTerm (it : IndexTerm) : IndexTerm :=
  AnnotTerm.mk (.unop .not it) .bool default

/-- Convert simple Pexprs to IndexTerms for use as comparison operands.
    Handles symbol references and integer literals.
    Symbols get `.integer` type — correct for comparison operands (v > 0)
    but would need context lookup for general symbol typing. -/
def pexprToIndexTerm : Pexpr → Option IndexTerm
  | .sym s => some (AnnotTerm.mk (.sym s) .integer default)
  | .val (.loaded (.specified (.integer ⟨n, _⟩))) =>
    some (AnnotTerm.mk (.const (.z n)) .integer default)
  | _ => none

/-- Convert a Core Pexpr to an IndexTerm for use in path conditions.
    Handles symbol references, negated conditions, and comparison operators. -/
def condTermOfPexpr : Pexpr → Option IndexTerm
  | .sym s => some (AnnotTerm.mk (.sym s) .bool default)
  | .not_ e => condTermOfPexpr e |>.map negateIndexTerm
  | .op binop e1 e2 =>
    match binop with
    | .eq | .lt | .le | .gt | .ge =>
      match pexprToIndexTerm e1, pexprToIndexTerm e2 with
      | some t1, some t2 =>
        match binop with
        | .gt => some (AnnotTerm.mk (.binop .lt t2 t1) .bool default)
        | .ge => some (AnnotTerm.mk (.binop .le t2 t1) .bool default)
        | .eq => some (AnnotTerm.mk (.binop .eq t1 t2) .bool default)
        | .lt => some (AnnotTerm.mk (.binop .lt t1 t2) .bool default)
        | .le => some (AnnotTerm.mk (.binop .le t1 t2) .bool default)
        | _ => none
      | _, _ => none
    | _ => none
  | _ => none

/-- Determine the CN base type of a Core binary operation result.
    Arithmetic ops preserve the left operand's type; comparison/logical ops return bool. -/
def opResultType : Binop → CNBaseType → CNBaseType → Option CNBaseType
  | .add, τ, _ | .sub, τ, _ | .mul, τ, _ | .div, τ, _
  | .rem_t, τ, _ | .rem_f, τ, _ | .exp, τ, _ => some τ
  | .eq, _, _ | .gt, _, _ | .lt, _, _ | .ge, _, _ | .le, _, _
  | .and, _, _ | .or, _, _ => some .bool

/-! ## Core ↔ CN Bridge Relations

`PexprMatchesTerm` connects Core-level pure expressions (`Pexpr`) to CN-level
index terms (`IndexTerm`). This ensures that the memory addresses and values
referenced in typing rules actually correspond to the Core expressions being
typed — the key connection that prevents constructing unsound derivations.
-/

/-- Maps Core binary operators to their CN counterparts (direct mapping). -/
def CoreBinopMatchesCN : Binop → BinOp → Prop
  | .add, .add => True  | .sub, .sub => True  | .mul, .mul => True
  | .div, .div => True  | .eq, .eq => True    | .lt, .lt => True
  | .le, .le => True    | .and, .and_ => True | .or, .or_ => True
  | .rem_t, .rem => True | .rem_f, .mod_ => True | .exp, .exp => True
  | _, _ => False

/-- Maps Core binary operators to CN with flipped operands.
    Core has `.gt`/`.ge` but CN represents `a > b` as `b < a`. -/
def CoreBinopFlipped : Binop → BinOp → Prop
  | .gt, .lt => True  | .ge, .le => True  | _, _ => False

/-- Core `Pexpr` corresponds to CN `IndexTerm` — they evaluate to the same
    value under compatible state/valuation pairs. This is the key connective
    ensuring the Core program and SLProp assertions reference the same entities.

    Deliberately incomplete: covers symbols, integer literals, and binary
    operations. Can be extended with new constructors as needed. -/
inductive PexprMatchesTerm : Pexpr → IndexTerm → Prop where
  /-- A symbol reference matches its index-term counterpart. -/
  | sym : ∀ (s : Sym) (bt : BaseType) (loc : Loc),
    PexprMatchesTerm (.sym s) ⟨.sym s, bt, loc⟩
  /-- An integer literal matches a `z` constant. -/
  | intVal : ∀ (n : Int) (optTy) (bt : BaseType) (loc : Loc),
    PexprMatchesTerm
      (.val (.loaded (.specified (.integer ⟨n, optTy⟩))))
      ⟨.const (.z n), bt, loc⟩
  /-- An integer literal matches a `bits` constant. -/
  | bitsVal : ∀ (n : Int) (optTy) (sign : CerbLean.CN.Types.Sign) (width : Nat)
      (bt : BaseType) (loc : Loc),
    PexprMatchesTerm
      (.val (.loaded (.specified (.integer ⟨n, optTy⟩))))
      ⟨.const (.bits sign width n), bt, loc⟩
  /-- A binary operation matches if the operator and operands match. -/
  | op : ∀ (coreOp : Binop) (cnOp : BinOp)
      (e1 e2 : Pexpr) (t1 t2 : IndexTerm) (bt : BaseType) (loc : Loc),
    CoreBinopMatchesCN coreOp cnOp →
    PexprMatchesTerm e1 t1 →
    PexprMatchesTerm e2 t2 →
    PexprMatchesTerm (.op coreOp e1 e2) ⟨.binop cnOp t1 t2, bt, loc⟩
  /-- A flipped binary operation: Core `a > b` ↔ CN `b < a`. -/
  | op_flip : ∀ (coreOp : Binop) (cnOp : BinOp)
      (e1 e2 : Pexpr) (t1 t2 : IndexTerm) (bt : BaseType) (loc : Loc),
    CoreBinopFlipped coreOp cnOp →
    PexprMatchesTerm e1 t1 →
    PexprMatchesTerm e2 t2 →
    PexprMatchesTerm (.op coreOp e1 e2) ⟨.binop cnOp t2 t1, bt, loc⟩
  /-- Unary logical not. -/
  | not_ : ∀ (e : Pexpr) (t : IndexTerm) (bt : BaseType) (loc : Loc),
    PexprMatchesTerm e t →
    PexprMatchesTerm (.not_ e) ⟨.unop .not t, bt, loc⟩
  /-- Pointer array shift (pointer arithmetic). -/
  | arrayShift : ∀ (ptr : Pexpr) (ct : Ctype) (idx : Pexpr)
      (ptrT idxT : IndexTerm) (bt : BaseType) (loc : Loc),
    PexprMatchesTerm ptr ptrT → PexprMatchesTerm idx idxT →
    PexprMatchesTerm (.arrayShift ptr ct idx) ⟨.arrayShift ptrT ct idxT, bt, loc⟩
  /-- Pointer member shift (struct field offset). -/
  | memberShift : ∀ (ptr : Pexpr) (tag : Sym) (member : Identifier)
      (ptrT : IndexTerm) (bt : BaseType) (loc : Loc),
    PexprMatchesTerm ptr ptrT →
    PexprMatchesTerm (.memberShift ptr tag member) ⟨.memberShift ptrT tag member, bt, loc⟩
  /-- Struct construction: all members match pairwise (names equal). -/
  | struct_ : ∀ (tag : Sym)
      (members : List (Identifier × Pexpr))
      (memberTerms : List (Identifier × IndexTerm))
      (bt : BaseType) (loc : Loc),
    members.length = memberTerms.length →
    (∀ i (hm : i < members.length) (ht : i < memberTerms.length),
      (members[i]).1 = (memberTerms[i]).1) →
    (∀ i (hm : i < members.length) (ht : i < memberTerms.length),
      PexprMatchesTerm (members[i]).2 (memberTerms[i]).2) →
    PexprMatchesTerm (.struct_ tag members) ⟨.struct_ tag memberTerms, bt, loc⟩
  /-- Struct member access. -/
  | memberof : ∀ (tag : Sym) (member : Identifier)
      (e : Pexpr) (t : IndexTerm) (bt : BaseType) (loc : Loc),
    PexprMatchesTerm e t →
    PexprMatchesTerm (.memberof tag member e) ⟨.structMember t member, bt, loc⟩
  /-- Conditional pure expression. -/
  | if_ : ∀ (cond then_ else_ : Pexpr) (condT thenT elseT : IndexTerm)
      (bt : BaseType) (loc : Loc),
    PexprMatchesTerm cond condT → PexprMatchesTerm then_ thenT →
    PexprMatchesTerm else_ elseT →
    PexprMatchesTerm (.if_ cond then_ else_) ⟨.ite condT thenT elseT, bt, loc⟩
  /-- Integer conversion / cast. -/
  | convInt : ∀ (ity : CerbLean.Core.IntegerType) (e : Pexpr) (t : IndexTerm)
      (bt : BaseType) (loc : Loc),
    PexprMatchesTerm e t →
    PexprMatchesTerm (.convInt ity e) ⟨.cast bt t, bt, loc⟩
  /-- Null pointer literal: `PointerValueBase.null ty` matches CN `.const .null`. -/
  | nullVal : ∀ (ty : Ctype) (prov : CerbLean.Core.Provenance) (bt : BaseType) (loc : Loc),
    PexprMatchesTerm
      (.val (.loaded (.specified (.pointer ⟨prov, .null ty⟩))))
      ⟨.const .null, bt, loc⟩

/-! ## Value-Type Compatibility -/

/-- Relates a Core value to its CN base type.
    Used as a premise in `PureHasType.val` to ensure the value actually
    matches the claimed type.
    Tightened: structs/unions check tag equality, `.loaded (.unspecified _)` excluded
    (uninitialized values don't satisfy any type), arrays remain permissive
    (no element type in ObjectValue.array). -/
def valueHasType : Value → CNBaseType → Prop
  -- Loaded (specified) values — from value literals in Core AST
  | .loaded (.specified (.integer _)), .bits _ _ => True
  | .loaded (.specified (.integer _)), .integer => True
  | .loaded (.specified (.pointer _)), .loc => True
  | .loaded (.specified (.floating _)), .real => True
  -- DIVERGES-FROM-CN: Array element types not checked. ObjectValue.array
  -- doesn't carry element type info, so we can't verify element types here.
  -- Would need LoadedValue type annotation or Ctype context to check properly.
  | .loaded (.specified (.array _)), .list _ => True
  | .loaded (.specified (.struct_ tag _)), .struct_ tag' => tag == tag'
  | .loaded (.specified (.union_ tag _ _)), .struct_ tag' => tag == tag'
  -- NOTE: `.loaded (.unspecified ct)` intentionally excluded. Unspecified values have
  -- no concrete content; using them in conditionals/arithmetic is UB in Cerberus
  -- (UB_unspec_conditional). They should NOT satisfy any type predicate.
  -- Object values — produced by interpreter (evalIntOp, convertInt, wrapIntOp, etc.)
  -- evalPexpr always produces .object form for computed values (Cerberus Vcval).
  | .object (.integer _), .bits _ _ => True
  | .object (.integer _), .integer => True
  | .object (.pointer _), .loc => True
  | .object (.floating _), .real => True
  | .object (.array _), .list _ => True
  | .object (.struct_ tag _), .struct_ tag' => tag == tag'
  | .object (.union_ tag _ _), .struct_ tag' => tag == tag'
  -- Non-object values
  | .unit, .unit => True
  | .true_, .bool => True
  | .false_, .bool => True
  | .ctype _, .ctype => True
  | _, _ => False

/-- Restricted value-type compatibility for "operable" values.
    Only `.object`-form values (Cerberus Vcval) and non-object values
    (.unit, .true_, .false_, .ctype) satisfy this predicate.
    `.loaded` values (from memory reads via `valueFromMemValue`) are excluded
    because pure expression operations (`valueToInt`, `evalBinop`, `convertInt`,
    `wrapIntOp`, `arrayShift`, `memberShift`) only accept `.object` form.

    Used in `PureHasType.val` to ensure value literals are operable (Core
    value literals, Vcval, are always in `.object` form). -/
def pureValueHasType : Value → CNBaseType → Prop
  | .object (.integer _), .bits _ _ => True
  | .object (.integer _), .integer => True
  | .object (.pointer _), .loc => True
  | .object (.floating _), .real => True
  | .object (.array _), .list _ => True
  | .object (.struct_ tag _), .struct_ tag' => tag == tag'
  | .object (.union_ tag _ _), .struct_ tag' => tag == tag'
  | .unit, .unit => True
  | .true_, .bool => True
  | .false_, .bool => True
  | .ctype _, .ctype => True
  | _, _ => False

/-- Every `pureValueHasType` instance implies `valueHasType`.
    The converse is false: `.loaded (.specified _)` satisfies `valueHasType`
    but not `pureValueHasType`. -/
theorem pureValueHasType_implies_valueHasType
    {v : Value} {τ : CNBaseType}
    (h : pureValueHasType v τ) : valueHasType v τ := by
  unfold pureValueHasType at h
  unfold valueHasType
  cases v with
  | object ov => cases ov <;> cases τ <;> simp_all
  | unit => cases τ <;> simp_all
  | true_ => cases τ <;> simp_all
  | false_ => cases τ <;> simp_all
  | ctype => cases τ <;> simp_all
  | loaded lv => cases lv <;> cases τ <;> simp_all
  | list => cases τ <;> simp_all
  | tuple => cases τ <;> simp_all

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

/-- Look up a struct tag definition in the context -/
def lookupTagDef (ctx : Ctx) (tag : Sym) : Option (List (Identifier × Ctype)) :=
  ctx.tagDefs.find? (·.1 == tag) |>.map (·.2)

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
      Uses `valueHasType` (not `pureValueHasType`) because Core value literals
      are `.loaded (.specified _)` form in the AST (Cerberus represents literals
      as `Specified(object_value)`). The `val` case is fine for soundness —
      `evalPexpr` just returns the value as-is without requiring `.object` form.
      The `.loaded`-vs-`.object` issue only arises for operation operands. -/
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
  /-- Logical NOT returns bool. -/
  | not_ : ∀ {Γ : Ctx} {annots : Annots} {coreTy} {e : Pexpr},
    PureHasType Γ ⟨annots, coreTy, e⟩ .bool →
    PureHasType Γ ⟨annots, coreTy, .not_ e⟩ .bool
  /-- Pure let binding: bind result of `e₁` in `e₂`. -/
  | let_ : ∀ {Γ : Ctx} {annots : Annots} {coreTy} {patAnnots : Annots}
      {x : Sym} {bty : CerbLean.Core.BaseType}
      {e₁ e₂ : Pexpr} {τ₁ τ₂ : CNBaseType},
    PureHasType Γ ⟨annots, coreTy, e₁⟩ τ₁ →
    PureHasType (Γ.addVar x τ₁) ⟨annots, coreTy, e₂⟩ τ₂ →
    PureHasType Γ ⟨annots, coreTy,
      .let_ ⟨patAnnots, .base (some x) bty⟩ e₁ e₂⟩ τ₂
  /-- Pointer array shift returns a pointer. -/
  | arrayShift : ∀ {Γ : Ctx} {annots : Annots} {coreTy}
      {ptr : Pexpr} {ct : Ctype} {idx : Pexpr},
    PureHasType Γ ⟨annots, coreTy, ptr⟩ .loc →
    PureHasType Γ ⟨annots, coreTy, .arrayShift ptr ct idx⟩ .loc
  /-- Pointer member shift returns a pointer. -/
  | memberShift : ∀ {Γ : Ctx} {annots : Annots} {coreTy}
      {ptr : Pexpr} {tag : Sym} {member : Identifier},
    PureHasType Γ ⟨annots, coreTy, ptr⟩ .loc →
    PureHasType Γ ⟨annots, coreTy, .memberShift ptr tag member⟩ .loc
  /-- Struct construction: each field must be well-typed.
      The `fieldTypes` list witnesses the type of each field. -/
  | struct_ : ∀ {Γ : Ctx} {annots : Annots} {coreTy}
      {tag : Sym} {members : List (Identifier × Pexpr)}
      {fieldTypes : List CNBaseType},
    fieldTypes.length = members.length →
    (∀ i (hf : i < fieldTypes.length) (hm : i < members.length),
      PureHasType Γ ⟨annots, coreTy, (members[i]).2⟩ (fieldTypes[i])) →
    PureHasType Γ ⟨annots, coreTy, .struct_ tag members⟩ (.struct_ tag)
  /-- Struct member access: result type constrained by the field's Ctype.
      Requires the struct tag definition in context to look up the member type. -/
  | memberof : ∀ {Γ : Ctx} {annots : Annots} {coreTy}
      {tag : Sym} {member : Identifier} {e : Pexpr}
      {fields : List (Identifier × Ctype)} {fieldCt : Ctype} {τ : CNBaseType},
    PureHasType Γ ⟨annots, coreTy, e⟩ (.struct_ tag) →
    Γ.lookupTagDef tag = some fields →
    fields.find? (·.1 == member) = some (member, fieldCt) →
    ctypeToBaseType fieldCt = some τ →
    PureHasType Γ ⟨annots, coreTy, .memberof tag member e⟩ τ
  /-- Integer conversion: cast to a possibly different integer type.
      Result type determined by the target IntegerType via `intTypeToBaseType`. -/
  | convInt : ∀ {Γ : Ctx} {annots : Annots} {coreTy}
      {ity : IntegerType} {e : Pexpr} {τ₁ : CNBaseType},
    PureHasType Γ ⟨annots, coreTy, e⟩ τ₁ →
    PureHasType Γ ⟨annots, coreTy, .convInt ity e⟩ (intTypeToBaseType ity)
  /-- Type predicate `is_scalar` returns bool.
      Requires `.ctype` input — evalPexpr's isScalar branch fails on non-ctype. -/
  | isScalar : ∀ {Γ : Ctx} {annots : Annots} {coreTy} {e : Pexpr},
    PureHasType Γ ⟨annots, coreTy, e⟩ .ctype →
    PureHasType Γ ⟨annots, coreTy, .isScalar e⟩ .bool
  /-- Type predicate `is_integer` returns bool.
      Requires `.ctype` input — evalPexpr's isInteger branch fails on non-ctype. -/
  | isInteger : ∀ {Γ : Ctx} {annots : Annots} {coreTy} {e : Pexpr},
    PureHasType Γ ⟨annots, coreTy, e⟩ .ctype →
    PureHasType Γ ⟨annots, coreTy, .isInteger e⟩ .bool
  /-- Type predicate `is_signed` returns bool.
      Requires `.ctype` input — evalPexpr's isSigned branch fails on non-ctype. -/
  | isSigned : ∀ {Γ : Ctx} {annots : Annots} {coreTy} {e : Pexpr},
    PureHasType Γ ⟨annots, coreTy, e⟩ .ctype →
    PureHasType Γ ⟨annots, coreTy, .isSigned e⟩ .bool
  /-- Type predicate `is_unsigned` returns bool.
      Requires `.ctype` input — evalPexpr's isUnsigned branch fails on non-ctype. -/
  | isUnsigned : ∀ {Γ : Ctx} {annots : Annots} {coreTy} {e : Pexpr},
    PureHasType Γ ⟨annots, coreTy, e⟩ .ctype →
    PureHasType Γ ⟨annots, coreTy, .isUnsigned e⟩ .bool
  /-- Type predicate `are_compatible` returns bool.
      Requires `.ctype` inputs — evalPexpr's areCompatible branch fails on non-ctype. -/
  | areCompatible : ∀ {Γ : Ctx} {annots : Annots} {coreTy}
      {e₁ e₂ : Pexpr},
    PureHasType Γ ⟨annots, coreTy, e₁⟩ .ctype →
    PureHasType Γ ⟨annots, coreTy, e₂⟩ .ctype →
    PureHasType Γ ⟨annots, coreTy, .areCompatible e₁ e₂⟩ .bool
  /-- Pure case expression: scrutinee well-typed, all branches same type. -/
  | case_ : ∀ {Γ : Ctx} {annots : Annots} {coreTy}
      {scrut : Pexpr} {branches : List (APattern × Pexpr)} {τs τ : CNBaseType},
    PureHasType Γ ⟨annots, coreTy, scrut⟩ τs →
    (∀ branch, branch ∈ branches →
      PureHasType (Γ.addPatternBinding branch.1 τs) ⟨annots, coreTy, branch.2⟩ τ) →
    PureHasType Γ ⟨annots, coreTy, .case_ scrut branches⟩ τ
  /-- Wrapping integer arithmetic (overflow wrap).
      Result type determined by the target IntegerType via `intTypeToBaseType`. -/
  | wrapI : ∀ {Γ : Ctx} {annots : Annots} {coreTy}
      {ity : IntegerType} {iop : Iop}
      {e₁ e₂ : Pexpr} {τ₁ τ₂ : CNBaseType},
    PureHasType Γ ⟨annots, coreTy, e₁⟩ τ₁ →
    PureHasType Γ ⟨annots, coreTy, e₂⟩ τ₂ →
    PureHasType Γ ⟨annots, coreTy, .wrapI ity iop e₁ e₂⟩ (intTypeToBaseType ity)

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

  /-- **Annot**: Transparent annotation wrapper (dynamic checks, debug info).
      Does not affect typing. -/
  | annot : ∀ {Γ : Ctx} {H₁ H₂ : SLProp} {annots : Annots}
      {dynAnnots : CerbLean.Core.DynAnnotations} {e : AExpr} {τ : CNBaseType},
    HasType Γ H₁ e τ H₂ →
    HasType Γ H₁ ⟨annots, .annot dynAnnots e⟩ τ H₂

  /-- **Excluded**: Neg-action wrapper for unsequenced race checking.
      Same typing as the inner action expression. -/
  | excluded : ∀ {Γ : Ctx} {H₁ H₂ : SLProp} {annots : Annots}
      {exclId : Nat} {act : Paction} {τ : CNBaseType},
    HasType Γ H₁ ⟨annots, .action act⟩ τ H₂ →
    HasType Γ H₁ ⟨annots, .excluded exclId act⟩ τ H₂

  -- Memory Action Rules

  /-- **Load**: Read from an owned pointer. Consumes and re-emits the
      `Owned<ct>(ptr,val)` resource — the heap is unchanged.
      Returns the value stored at the pointer — the return type is
      determined by the value's base type annotation (`val.bt`).
      The `tyPe.expr = .val (.ctype ct)` premise connects the type annotation
      in the Core expression to the Ctype in the Owned resource.
      The `PexprMatchesTerm` premise connects the Core pointer expression
      to the SLProp pointer term, ensuring we load from the claimed location. -/
  | action_load : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots} {locAnn : Loc}
      {ct : Ctype} {ptr val : IndexTerm} {tyPe ptrPe : APexpr},
    tyPe.expr = .val (.ctype ct) →
    PexprMatchesTerm ptrPe.expr ptr →
    PureHasType Γ ptrPe .loc →
    HasType Γ (.star (.owned ct .init ptr val) R)
      ⟨annots, .action ⟨.pos, ⟨locAnn, .load tyPe ptrPe .na⟩⟩⟩
      val.bt
      (.star (.owned ct .init ptr val) R)

  /-- **Store**: Write to an owned pointer. Consumes `Owned<ct>(ptr,valOld)`
      and produces `Owned<ct>(ptr,valNew)` with the new value.
      The `tyPe.expr = .val (.ctype ct)` premise connects the type annotation
      to the Ctype in the Owned resource.
      `PexprMatchesTerm` premises connect the Core pointer and value
      expressions to the SLProp terms, ensuring we write the claimed value
      at the claimed location. -/
  | action_store : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots} {locAnn : Loc}
      {ct : Ctype} {ptr valOld valNew : IndexTerm}
      {tyPe ptrPe valPe : APexpr} {τ : CNBaseType},
    tyPe.expr = .val (.ctype ct) →
    PexprMatchesTerm ptrPe.expr ptr →
    PexprMatchesTerm valPe.expr valNew →
    PureHasType Γ ptrPe .loc →
    PureHasType Γ valPe τ →
    valNew.bt = τ →  -- stored value's type annotation must match its actual type
    HasType Γ (.star (.owned ct .init ptr valOld) R)
      ⟨annots, .action ⟨.pos, ⟨locAnn, .store false tyPe ptrPe valPe .na⟩⟩⟩
      .unit
      (.star (.owned ct .init ptr valNew) R)

  /-- **Store (block→owned)**: Write to a freshly allocated (block) pointer.
      Consumes `Block<ct>(ptr)` and produces `Owned<ct>(init, ptr, valNew)`.
      The interpreter's `storeImpl` doesn't distinguish first write from
      subsequent writes, so a store to a Block produces Owned(init). -/
  | action_store_block : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots} {locAnn : Loc}
      {ct : Ctype} {ptr valNew : IndexTerm}
      {tyPe ptrPe valPe : APexpr} {τ : CNBaseType},
    tyPe.expr = .val (.ctype ct) →
    PexprMatchesTerm ptrPe.expr ptr →
    PexprMatchesTerm valPe.expr valNew →
    PureHasType Γ ptrPe .loc →
    PureHasType Γ valPe τ →
    valNew.bt = τ →  -- stored value's type annotation must match its actual type
    HasType Γ (.star (.block ct ptr) R)
      ⟨annots, .action ⟨.pos, ⟨locAnn, .store false tyPe ptrPe valPe .na⟩⟩⟩
      .unit
      (.star (.owned ct .init ptr valNew) R)

  /-- **Create**: Allocate fresh memory. Produces a `Block<ct>(ptr)` resource
      representing the newly allocated (but uninitialized) memory.
      Returns the pointer (type `loc`).
      The `sizePe.expr = .val (.ctype ct)` premise connects the size expression
      to the Ctype in the Block resource (the interpreter evaluates sizePe to get the type).
      The pointer is restricted to a logical variable (`⟨.sym ptrSym, .loc, default⟩`)
      to prevent claiming allocations at specific concrete addresses. -/
  | action_create : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots} {locAnn : Loc}
      {ct : Ctype} {ptrSym : Sym} {alignPe sizePe : APexpr} {prefix_ : SymPrefix},
    sizePe.expr = .val (.ctype ct) →
    HasType Γ H
      ⟨annots, .action ⟨.pos, ⟨locAnn, .create alignPe sizePe prefix_⟩⟩⟩
      .loc
      (.star (.block ct ⟨.sym ptrSym, .loc, default⟩) H)

  /-- **Kill (owned)**: Deallocate memory that has an `Owned` resource.
      Consumes the `Owned<ct>(ptr,val)` resource, leaving the remainder.
      `PexprMatchesTerm` connects the Core pointer to the SLProp pointer. -/
  | action_kill_owned : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots} {locAnn : Loc}
      {ct : Ctype} {initState : Init} {ptr val : IndexTerm}
      {ptrPe : APexpr} {kind : KillKind},
    PexprMatchesTerm ptrPe.expr ptr →
    HasType Γ (.star (.owned ct initState ptr val) R)
      ⟨annots, .action ⟨.pos, ⟨locAnn, .kill kind ptrPe⟩⟩⟩
      .unit R

  /-- **Kill (block)**: Deallocate memory that has a `Block` resource.
      Consumes the `Block<ct>(ptr)` resource, leaving the remainder.
      `PexprMatchesTerm` connects the Core pointer to the SLProp pointer. -/
  | action_kill_block : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots} {locAnn : Loc}
      {ct : Ctype} {ptr : IndexTerm} {ptrPe : APexpr} {kind : KillKind},
    PexprMatchesTerm ptrPe.expr ptr →
    HasType Γ (.star (.block ct ptr) R)
      ⟨annots, .action ⟨.pos, ⟨locAnn, .kill kind ptrPe⟩⟩⟩
      .unit R

  -- Procedure Calls

  /-- **Procedure call**: Call a named function with a known specification.
      Consumes precondition resources and produces postcondition resources.
      Return type is constrained to `spec.returnType` (from the function spec).
      Actual arguments are connected to formal parameters via `PexprMatchesTerm`,
      and the spec's pre/post are substituted with actual argument terms (`σ`).
      This ensures the pre/post conditions reference actual argument values. -/
  | proc : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots}
      {s : Sym} {args : List APexpr}
      {spec : FunctionSpec}
      {argTerms : List IndexTerm}
      {σ : Subst},
    Γ.lookupFunSpec s = some spec →
    args.length = spec.params.length →
    argTerms.length = args.length →
    σ = Subst.fromMapping
      (spec.params.zip argTerms |>.map fun ((sym, _), term) => (sym.id, term)) →
    (∀ i (ha : i < args.length) (ht : i < argTerms.length),
      PexprMatchesTerm (args[i]).expr (argTerms[i])) →
    HasType Γ (.star (SLProp.ofPrecondition (spec.requires.substTotal σ)) R)
      ⟨annots, .proc (Name.sym s) args⟩
      spec.returnType
      (.star (SLProp.ofPostcondition (spec.ensures.substTotal σ)) R)

  /-- **C function call through pointer**: Like `proc` but the function is
      identified by a pointer expression rather than a direct symbol.
      The function pointer must resolve to a known symbol with a spec.
      Return type is constrained to `spec.returnType`.
      `PexprMatchesTerm` connects the pointer to a symbol, and the spec
      is looked up from the context for that symbol — preventing unsound
      derivations that use an arbitrary spec. -/
  | ccall : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots}
      {funPtr funTy : APexpr} {args : List APexpr}
      {spec : FunctionSpec}
      {argTerms : List IndexTerm}
      {σ : Subst}
      {funSym : Sym},
    PureHasType Γ funPtr .loc →
    PexprMatchesTerm funPtr.expr ⟨.sym funSym, .loc, default⟩ →
    Γ.lookupFunSpec funSym = some spec →
    args.length = spec.params.length →
    argTerms.length = args.length →
    σ = Subst.fromMapping
      (spec.params.zip argTerms |>.map fun ((sym, _), term) => (sym.id, term)) →
    (∀ i (ha : i < args.length) (ht : i < argTerms.length),
      PexprMatchesTerm (args[i]).expr (argTerms[i])) →
    HasType Γ (.star (SLProp.ofPrecondition (spec.requires.substTotal σ)) R)
      ⟨annots, .ccall funPtr funTy args⟩
      spec.returnType
      (.star (SLProp.ofPostcondition (spec.ensures.substTotal σ)) R)

  -- Memory Operations (Memops)

  /-- **Pointer comparison memop**: pointer equality/ordering tests.
      Returns bool, heap unchanged. -/
  | memop_ptrCmp : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots}
      {op : Memop} {args : List APexpr},
    (op = .ptrEq ∨ op = .ptrNe ∨ op = .ptrLt ∨ op = .ptrGt
     ∨ op = .ptrLe ∨ op = .ptrGe) →
    HasType Γ H ⟨annots, .memop op args⟩ .bool H

  /-- **Pointer validity memop**: deref validity and alignment checks.
      Returns bool, heap unchanged. -/
  | memop_ptrValid : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots}
      {op : Memop} {args : List APexpr},
    (op = .ptrValidForDeref ∨ op = .ptrWellAligned) →
    HasType Γ H ⟨annots, .memop op args⟩ .bool H

  /-- **Pointer array shift memop**: returns a pointer (loc), heap unchanged. -/
  | memop_ptrArrayShift : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots}
      {args : List APexpr},
    HasType Γ H ⟨annots, .memop .ptrArrayShift args⟩ .loc H

  /-- **Pointer member shift memop**: returns a pointer (loc), heap unchanged. -/
  | memop_ptrMemberShift : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots}
      {tag : Sym} {member : Identifier} {args : List APexpr},
    HasType Γ H ⟨annots, .memop (.ptrMemberShift tag member) args⟩ .loc H

  /-- **Integer-from-pointer cast**: returns an unsigned 64-bit integer. -/
  | memop_intFromPtr : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots}
      {args : List APexpr},
    HasType Γ H ⟨annots, .memop .intFromPtr args⟩ (.bits .unsigned 64) H

  /-- **Pointer-from-integer cast**: returns a pointer. -/
  | memop_ptrFromInt : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots}
      {args : List APexpr},
    HasType Γ H ⟨annots, .memop .ptrFromInt args⟩ .loc H

  /-- **Pointer difference**: returns a signed 64-bit integer. -/
  | memop_ptrdiff : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots}
      {args : List APexpr},
    HasType Γ H ⟨annots, .memop .ptrdiff args⟩ (.bits .signed 64) H

  /-- **memcpy**: copies `n` bytes from `src` to `dst`.
      CN-faithful rule using byte-level `each` resources
      (matches CN's `memcpy_proxy_ft` in check.ml:2820-2861).

      Pre-heap: destination has `n` uninit bytes, source has `n` init bytes.
      Post-heap: destination has `n` init bytes (content copied from source),
      source unchanged.

      The byte QPredicate `qpDst`/`qpSrc` quantifies over indices `0..n-1`
      with step type `byte` (Ctype.byte). The `PexprMatchesTerm` premises
      connect the Core memcpy arguments (dst, src, size) to the SLProp terms.

      See docs/2026-03-01_HASTYPE_SOUNDNESS_AUDIT.md issue #1 for why the
      previous `H → H` rule was unsound. -/
  | memop_memcpy : ∀ {Γ : Ctx} {R : SLProp} {annots : Annots}
      {args : List APexpr}
      {qpDst qpSrc : QPredicate}
      {dstOut srcOut dstOut' : IndexTerm},
    -- Connect Core arguments to SLProp QPredicate pointers
    args.length ≥ 3 →
    PexprMatchesTerm (args[0]!).expr qpDst.pointer →
    PexprMatchesTerm (args[1]!).expr qpSrc.pointer →
    -- QPredicate constraints
    qpDst.name = .owned (some Ctype.byte) .uninit →
    qpSrc.name = .owned (some Ctype.byte) .init →
    qpDst.step = Ctype.byte →
    qpSrc.step = Ctype.byte →
    -- Post-heap destination content equals source content
    dstOut'.bt = srcOut.bt →
    HasType Γ
      (.star (.each qpDst dstOut) (.star (.each qpSrc srcOut) R))
      ⟨annots, .memop .memcpy args⟩
      .unit
      (.star (.each (⟨.owned (some Ctype.byte) .init, qpDst.pointer,
                      qpDst.q, qpDst.qLoc, Ctype.byte,
                      qpDst.permission, qpDst.iargs⟩)
                    dstOut')
             (.star (.each qpSrc srcOut) R))

  /-- **memcmp**: compares memory. Returns a signed 32-bit integer.
      Heap unchanged (read-only). -/
  | memop_memcmp : ∀ {Γ : Ctx} {H : SLProp} {annots : Annots}
      {args : List APexpr},
    HasType Γ H ⟨annots, .memop .memcmp args⟩ (.bits .signed 32) H

  -- Continuations (Loops)

  /-- **Save (label definition)**: Define a labeled continuation for looping.
      The body type-checks under the loop invariant, with invariant parameters
      bound in the context. The precondition is the invariant with initial
      argument values substituted for the formal parameter symbols (`σ`).
      Corresponds to Core `Esave`: evaluates default args, then executes body.
      The body may use `run` to loop back. -/
  | save : ∀ {Γ : Ctx} {H₂ : SLProp} {annots : Annots}
      {retSym : Sym} {retTy : CerbLean.Core.BaseType}
      {params : List (Sym × CerbLean.Core.BaseType × APexpr)}
      {body : AExpr} {τ : CNBaseType} {inv : LabelInv}
      {argTerms : List IndexTerm}
      {σ : Subst},
    Γ.lookupLabelInv retSym = some inv →
    params.length = inv.params.length →
    argTerms.length = params.length →
    σ = Subst.fromMapping
      (inv.params.zip argTerms |>.map fun ((sym, _), term) => (sym.id, term)) →
    (∀ i (hp : i < params.length) (ht : i < argTerms.length),
      PexprMatchesTerm (params[i]).2.2.expr (argTerms[i])) →
    HasType (Γ.addParams inv.params) inv.invariant body τ H₂ →
    HasType Γ (inv.invariant.substTotal σ)
      ⟨annots, .save retSym retTy params body⟩ τ H₂

  /-- **Run (continuation jump)**: Jump to a labeled continuation.
      The precondition is the invariant with actual argument values substituted (`σ`).
      Since `run` transfers control (does not return), the return type `τ`
      and post-heap `H₂` are unconstrained — like `absurd` or divergence.
      Corresponds to Core `Erun`: evaluates args and restarts the label body. -/
  | run : ∀ {Γ : Ctx} {H₂ : SLProp} {annots : Annots}
      {label : Sym} {args : List APexpr}
      {inv : LabelInv} {τ : CNBaseType}
      {argTerms : List IndexTerm}
      {σ : Subst},
    Γ.lookupLabelInv label = some inv →
    args.length = inv.params.length →
    argTerms.length = args.length →
    σ = Subst.fromMapping
      (inv.params.zip argTerms |>.map fun ((sym, _), term) => (sym.id, term)) →
    (∀ i (ha : i < args.length) (ht : i < argTerms.length),
      PexprMatchesTerm (args[i]).expr (argTerms[i])) →
    HasType Γ (inv.invariant.substTotal σ)
      ⟨annots, .run label args⟩ τ H₂

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

/-! ## Bridge Lemmas (Value and Evaluation)

Bridge lemmas that reference `valueHasType`, `PexprMatchesTerm`, and other
definitions from this file. Placed here (not in Models.lean) to avoid
circular imports.
See docs/2026-03-01_HASTYPE_SOUNDNESS_AUDIT.md issues #6, #8.
-/

open CerbLean.Core (MemValue IntegerType PointerValue FloatingType FloatingValue
                     StructMember Qualifiers)
open CerbLean.CN.Semantics (HeapValue HeapFragment Valuation heapValueOfMemValue)

/-- Specification relation for `memValueFromValue` (Semantics/Eval.lean:310).
    Since `memValueFromValue` is `partial`, it cannot appear in theorem
    statements. This inductive relation specifies its input/output behavior
    for the cases relevant to soundness proofs.

    `MemValueFromValue ct v mv` holds when `memValueFromValue ct v = some mv`.

    Each constructor mirrors one successful branch of `memValueFromValue`.
    Covers: unspecified, integer, floating, pointer. Array and struct cases
    can be added as needed (they require recursive cases). -/
inductive MemValueFromValue : Ctype → Value → MemValue → Prop where
  /-- Unspecified value passes through.
      Corresponds to: Eval.lean:321 -/
  | unspecified : ∀ (ct : Ctype) (ty : Ctype),
      MemValueFromValue ct (.loaded (.unspecified ty)) (.unspecified ty)
  /-- Integer object value with matching integer type.
      Corresponds to: Eval.lean:323 -/
  | integerObj : ∀ (ct : Ctype) (ity : IntegerType) (iv : CerbLean.Core.IntegerValue),
      ct.ty = .basic (.integer ity) →
      MemValueFromValue ct (.object (.integer iv)) (.integer ity iv)
  /-- Integer loaded value with matching integer type.
      Corresponds to: Eval.lean:324 -/
  | integerLoaded : ∀ (ct : Ctype) (ity : IntegerType) (iv : CerbLean.Core.IntegerValue),
      ct.ty = .basic (.integer ity) →
      MemValueFromValue ct (.loaded (.specified (.integer iv))) (.integer ity iv)
  /-- Byte-typed integer object value (byte = unsigned ichar).
      Corresponds to: Eval.lean:326 -/
  | byteObj : ∀ (ct : Ctype) (iv : CerbLean.Core.IntegerValue),
      ct.ty = .byte →
      MemValueFromValue ct (.object (.integer iv)) (.integer (.unsigned .ichar) iv)
  /-- Byte-typed integer loaded value (byte = unsigned ichar).
      Corresponds to: Eval.lean:327 -/
  | byteLoaded : ∀ (ct : Ctype) (iv : CerbLean.Core.IntegerValue),
      ct.ty = .byte →
      MemValueFromValue ct (.loaded (.specified (.integer iv))) (.integer (.unsigned .ichar) iv)
  /-- Floating object value with matching floating type.
      Corresponds to: Eval.lean:329 -/
  | floatingObj : ∀ (ct : Ctype) (fty : FloatingType) (fv : FloatingValue),
      ct.ty = .basic (.floating fty) →
      MemValueFromValue ct (.object (.floating fv)) (.floating fty fv)
  /-- Floating loaded value with matching floating type.
      Corresponds to: Eval.lean:330 -/
  | floatingLoaded : ∀ (ct : Ctype) (fty : FloatingType) (fv : FloatingValue),
      ct.ty = .basic (.floating fty) →
      MemValueFromValue ct (.loaded (.specified (.floating fv))) (.floating fty fv)
  /-- Pointer object value.
      Corresponds to: Eval.lean:332-333 -/
  | pointerObj : ∀ (ct : Ctype) (qual : Qualifiers) (refTy : Ctype_)
      (pv : PointerValue),
      ct.ty = .pointer qual refTy →
      MemValueFromValue ct (.object (.pointer pv))
        (.pointer ⟨[], refTy⟩ pv)
  /-- Pointer loaded value.
      Corresponds to: Eval.lean:334-335 -/
  | pointerLoaded : ∀ (ct : Ctype) (qual : Qualifiers) (refTy : Ctype_)
      (pv : PointerValue),
      ct.ty = .pointer qual refTy →
      MemValueFromValue ct (.loaded (.specified (.pointer pv)))
        (.pointer ⟨[], refTy⟩ pv)

/-- Value-to-HeapValue type bridge.
    If a Core `Value` has CN type τ (via `valueHasType`), and it converts
    to a `MemValue` (via `MemValueFromValue`, specifying the partial
    `memValueFromValue` from Semantics/Eval.lean:310), then the resulting
    `HeapValue` (via `heapValueOfMemValue`) has that type.

    This bridges the interpreter's value representation with the proof
    system's heap model. Needed for `action_store` soundness.
    See audit issue #6. -/
theorem valueHasType_implies_heapValueHasType
    {ct : Ctype} {v : Value} {τ : CNBaseType} {mv : MemValue}
    (_hvt : valueHasType v τ)
    (_hmv : MemValueFromValue ct v mv) :
    heapValueHasType (heapValueOfMemValue mv) τ := by
  sorry

/-- Compatibility relation between interpreter environments and valuations.
    States that every symbol in the Core environment has a corresponding
    heap value in the valuation that is type-compatible. This is the key
    invariant maintained by the soundness proof across expression
    evaluation steps. -/
def envValuationCompat (env : List (Sym × Value)) (ρ : Valuation) : Prop :=
  ∀ s v, (s, v) ∈ env →
    ∃ hv, ρ.lookup s = some hv ∧
      ∀ τ, valueHasType v τ → heapValueHasType hv τ

/-- Look up the value of a Pexpr symbol in an interpreter environment.
    For `Pexpr.sym s`, returns the value bound to `s`.
    Other Pexpr forms are not directly looked up (they compose sub-lookups). -/
def pexprEnvLookup (env : List (Sym × Value)) : Pexpr → Option Value
  | .sym s => env.lookup s
  | _ => none

/-- PexprMatchesTerm correctness: if a Core Pexpr matches an IndexTerm,
    then under compatible env/valuation pairs, looking up the Pexpr's
    value in the env and evaluating the IndexTerm in the valuation yield
    type-compatible results.

    This connects the syntactic `PexprMatchesTerm` relation to actual
    semantic agreement. Needed for all rules with `PexprMatchesTerm`
    premises (load, store, kill, proc, ccall).
    See audit issue #8.

    Note: The full statement would reference `evalPexpr` from
    Semantics/Eval.lean:832, but that function has a monadic return type
    (`InterpM Value`) with fuel parameter. The abstract version here avoids
    the import dependency; the proof would be done in a file that imports
    both HasType and Eval. -/
theorem pexprMatchesTerm_eval_compat
    {pe : Pexpr} {it : IndexTerm} {ρ : Valuation}
    {env : List (Sym × Value)}
    (_hmatch : PexprMatchesTerm pe it)
    (_hcompat : envValuationCompat env ρ) :
    ∀ v, pexprEnvLookup env pe = some v →
      ∀ τ, valueHasType v τ →
        ∃ hv, evalIndexTerm ρ it = some hv ∧ heapValueHasType hv τ := by
  sorry

end CerbLean.ProofSystem
