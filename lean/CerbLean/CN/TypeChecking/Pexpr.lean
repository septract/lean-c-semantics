/-
  CN Pure Expression Checking
  Corresponds to: cn/lib/check.ml (check_pexpr parts)

  Converts Core pure expressions (Pexpr) to CN index terms (IndexTerm).
  This is part of Level 2 (separation logic verification) - it evaluates
  pure expressions to symbolic values that can be used in resource predicates.

  Audited: 2026-01-20 against cn/lib/check.ml
-/

import CerbLean.CN.TypeChecking.Monad
import CerbLean.CN.Types
import CerbLean.Core.Expr
import CerbLean.Core.Value

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Identifier Pexpr APexpr Value Binop Pattern APattern ObjectValue)
open CerbLean.CN.Types

/-! ## Helper Functions -/

/-- Extract a location from an annotation -/
def getAnnotLoc : Core.Annot → Option Core.Loc
  | .loc l => some l
  | .inlinedLabel l _ _ => some l
  | _ => none

/-- Extract location from a list of annotations -/
def getAnnotsLoc (annots : List Core.Annot) : Core.Loc :=
  annots.findSome? getAnnotLoc |>.getD Core.Loc.t.unknown

/-! ## Value Conversion

Convert Core values to CN index terms.
Corresponds to: value handling in check.ml
-/

/-- Convert a Core Value to a CN Const.
    Corresponds to: value cases in check.ml -/
def valueToConst (v : Value) (loc : Core.Loc) : Except TypeError Const := do
  match v with
  | .unit => return .unit
  | .true_ => return .bool true
  | .false_ => return .bool false
  | .object (.integer iv) =>
    -- IntegerValue has val : Int and prov : Provenance
    return .z iv.val
  | .object (.pointer pv) =>
    match pv.base with
    | .null _ => return .null
    | .concrete _ addr =>
      -- Convert provenance to allocation ID
      match pv.prov with
      | .some allocId => return .pointer ⟨allocId, addr⟩
      | _ => return .pointer ⟨0, addr⟩  -- Use 0 for unknown provenance
    | .function _sym =>
      -- Function pointers - represent as a special term
      -- For now, just use a default pointer
      return .pointer ⟨0, 0⟩
  | .ctype ct => return .ctypeConst ct
  | .list _ _ => throw (.other "List values not yet supported")
  | .tuple _ => throw (.other "Tuple values not yet supported")
  | .object _ => throw (.other "Object values not yet supported")
  | .loaded _ => throw (.other "Loaded values not yet supported")

/-- Convert a Core Value to a CN IndexTerm. -/
def valueToTerm (v : Value) (loc : Core.Loc) : Except TypeError IndexTerm := do
  let c ← valueToConst v loc
  let bt := baseTypeOfConst c
  return AnnotTerm.mk (.const c) bt loc
where
  baseTypeOfConst : Const → BaseType
    | .z _ => .integer
    | .bits sign width _ => .bits sign width
    | .q _ _ => .real
    | .memByte _ => .memByte
    | .pointer _ => .loc
    | .allocId _ => .allocId
    | .bool _ => .bool
    | .unit => .unit
    | .null => .loc
    | .ctypeConst _ => .ctype
    | .default bt => bt

/-! ## Binary Operator Conversion

Convert Core binary operators to CN binary operators.
-/

/-- Convert Core Binop to CN BinOp.
    Returns the operator and the result base type given operand types. -/
def convertBinop (op : Binop) (bt1 bt2 : BaseType) (loc : Core.Loc)
    : Except TypeError (BinOp × BaseType) := do
  match op with
  -- Arithmetic
  | .add => return (.add, bt1)
  | .sub => return (.sub, bt1)
  | .mul => return (.mul, bt1)
  | .div => return (.div, bt1)
  | .rem_t => return (.rem, bt1)  -- truncated remainder
  | .rem_f => return (.mod_, bt1)  -- floored remainder
  | .exp => return (.exp, bt1)
  -- Comparison
  | .lt => return (.lt, .bool)
  | .le => return (.le, .bool)
  | .gt => return (.lt, .bool)  -- x > y ≡ y < x (swap args)
  | .ge => return (.le, .bool)  -- x >= y ≡ y <= x (swap args)
  | .eq => return (.eq, .bool)
  -- Logical
  | .and => return (.and_, .bool)
  | .or => return (.or_, .bool)

/-! ## Pattern Matching

Convert Core patterns to variable bindings.
-/

/-- Result of binding a pattern -/
structure PatternBindings where
  /-- Variables bound by this pattern -/
  boundVars : List (Sym × BaseType)
  deriving Inhabited

/-- Convert Core.BaseType to CN.BaseType -/
def coreBaseTypeToCN (bt : Core.BaseType) : BaseType :=
  match bt with
  | .unit => .unit
  | .boolean => .bool
  | .ctype => .ctype
  | .list _ => .unit  -- TODO: proper list type
  | .tuple _ => .unit  -- TODO: proper tuple type
  | .object _ => .loc  -- object types map to locations
  | .loaded _ => .loc  -- loaded types map to locations
  | .storable => .unit

/-- Bind a pattern to a value, returning the bound variables.
    Corresponds to: check_and_match_pattern in check.ml -/
def bindPattern (pat : APattern) (value : IndexTerm) : TypingM PatternBindings := do
  match pat.pat with
  | .base (some sym) bt =>
    -- Bind variable to value
    let loc := value.loc
    let cnBt := coreBaseTypeToCN bt
    TypingM.addAValue sym value loc s!"pattern binding {sym.name.getD ""}"
    return { boundVars := [(sym, cnBt)] }
  | .base none _ =>
    -- Wildcard - no binding
    return { boundVars := [] }
  | .ctor _c _args =>
    -- Constructor patterns not yet implemented
    TypingM.fail (.other "Constructor patterns not yet supported")

/-- Remove pattern bindings from context.
    Called after pattern scope ends. -/
def unbindPattern (_bindings : PatternBindings) : TypingM Unit := do
  -- For now, we don't actually remove from context
  -- In a more complete implementation, we'd track scopes
  pure ()

/-! ## Variable Lookup

Look up variables in the typing context.
-/

/-- Look up a variable and return its value as an IndexTerm.
    Corresponds to: variable lookup in check_pexpr -/
def lookupVar (s : Sym) (loc : Core.Loc) : TypingM IndexTerm := do
  let ctx ← TypingM.getContext
  -- First check computational variables
  match ctx.getA s with
  | some (.value it) => return it
  | some (.baseType bt) =>
    -- Variable declared but no concrete value - return symbolic reference
    return AnnotTerm.mk (.sym s) bt loc
  | none =>
    -- Check logical variables
    match ctx.getL s with
    | some (.value it) => return it
    | some (.baseType bt) =>
      return AnnotTerm.mk (.sym s) bt loc
    | none =>
      TypingM.fail (.unboundVariable s)

/-! ## Pure Expression Checking

Main function to check pure expressions and convert to index terms.
Corresponds to: check_pexpr in check.ml
-/

/-- Check a pure expression and convert to an IndexTerm.
    Corresponds to: check_pexpr in cn/lib/check.ml -/
partial def checkPexpr (pe : APexpr) : TypingM IndexTerm := do
  let loc := getAnnotsLoc pe.annots
  match pe.expr with
  -- Variable reference
  | .sym s => lookupVar s loc

  -- Literal value
  | .val v =>
    match valueToTerm v loc with
    | .ok term => return term
    | .error err => TypingM.fail err

  -- Binary operation
  | .op op e1 e2 =>
    let pe1 : APexpr := ⟨[], pe.ty, e1⟩  -- Wrap in APexpr
    let pe2 : APexpr := ⟨[], pe.ty, e2⟩
    let t1 ← checkPexpr pe1
    let t2 ← checkPexpr pe2
    match convertBinop op t1.bt t2.bt loc with
    | .ok (cnOp, resBt) =>
      -- Handle operators that need result negation or arg swap (gt, ge)
      match op with
      | .gt => return AnnotTerm.mk (.binop .lt t2 t1) .bool loc  -- swap args
      | .ge => return AnnotTerm.mk (.binop .le t2 t1) .bool loc  -- swap args
      | _ => return AnnotTerm.mk (.binop cnOp t1 t2) resBt loc
    | .error err => TypingM.fail err

  -- Logical negation
  | .not_ e =>
    let pe' : APexpr := ⟨[], some .boolean, e⟩
    let t ← checkPexpr pe'
    return AnnotTerm.mk (.unop .not t) .bool loc

  -- Conditional
  | .if_ cond thenE elseE =>
    let peCond : APexpr := ⟨[], some .boolean, cond⟩
    let peThen : APexpr := ⟨[], pe.ty, thenE⟩
    let peElse : APexpr := ⟨[], pe.ty, elseE⟩
    let tCond ← checkPexpr peCond
    let tThen ← checkPexpr peThen
    let tElse ← checkPexpr peElse
    return AnnotTerm.mk (.ite tCond tThen tElse) tThen.bt loc

  -- Let binding
  | .let_ pat e1 e2 =>
    let pe1 : APexpr := ⟨[], none, e1⟩
    let v1 ← checkPexpr pe1
    let bindings ← bindPattern pat v1
    let pe2 : APexpr := ⟨[], pe.ty, e2⟩
    let result ← checkPexpr pe2
    unbindPattern bindings
    return result

  -- Struct member access
  | .memberof _tag member e =>
    let pe' : APexpr := ⟨[], none, e⟩
    let tStruct ← checkPexpr pe'
    -- Return the appropriate base type based on member
    -- For now, use a generic approach
    let resBt := pe.ty.map coreBaseTypeToCN |>.getD .unit
    return AnnotTerm.mk (.structMember tStruct member) resBt loc

  -- Array/pointer shift
  | .arrayShift ptr ty idx =>
    let pePtr : APexpr := ⟨[], some (.object .pointer), ptr⟩
    let peIdx : APexpr := ⟨[], some (.object .integer), idx⟩
    let tPtr ← checkPexpr pePtr
    let tIdx ← checkPexpr peIdx
    return AnnotTerm.mk (.arrayShift tPtr ty tIdx) .loc loc

  -- Member shift (pointer to member)
  | .memberShift ptr tag member =>
    let pePtr : APexpr := ⟨[], some (.object .pointer), ptr⟩
    let tPtr ← checkPexpr pePtr
    return AnnotTerm.mk (.memberShift tPtr tag member) .loc loc

  -- Constructor
  | .ctor c args =>
    let argTerms ← args.mapM fun arg => do
      let peArg : APexpr := ⟨[], none, arg⟩
      checkPexpr peArg
    let resBt := pe.ty.map coreBaseTypeToCN |>.getD .unit
    match c with
    | .tuple =>
      return AnnotTerm.mk (.tuple argTerms) resBt loc
    | _ =>
      TypingM.fail (.other s!"Constructor not yet supported: {repr c}")

  -- Function call (pure)
  | .call name args =>
    let argTerms ← args.mapM fun arg => do
      let peArg : APexpr := ⟨[], none, arg⟩
      checkPexpr peArg
    let fnSym := match name with
      | .sym s => s
      | .impl _ => { id := 0, name := some "impl_const" : Sym }  -- Placeholder
    let resBt := pe.ty.map coreBaseTypeToCN |>.getD .unit
    return AnnotTerm.mk (.apply fnSym argTerms) resBt loc

  -- Case/match expression
  | .case_ scrut branches =>
    let peScrut : APexpr := ⟨[], none, scrut⟩
    let tScrut ← checkPexpr peScrut
    -- Convert branches
    let cnBranches ← branches.mapM fun (pat, body) => do
      let bindings ← bindPattern pat tScrut
      let peBody : APexpr := ⟨[], pe.ty, body⟩
      let tBody ← checkPexpr peBody
      unbindPattern bindings
      -- Convert APattern to CN Pattern
      let cnPat := convertPattern pat tScrut.bt loc
      return (cnPat, tBody)
    let resBt := pe.ty.map coreBaseTypeToCN |>.getD .unit
    return AnnotTerm.mk (.match_ tScrut cnBranches) resBt loc

  -- Struct literal
  | .struct_ tag members =>
    let memberTerms ← members.mapM fun (id, expr) => do
      let peExpr : APexpr := ⟨[], none, expr⟩
      let tExpr ← checkPexpr peExpr
      return (id, tExpr)
    let resBt := pe.ty.map coreBaseTypeToCN |>.getD (.struct_ tag)
    return AnnotTerm.mk (.struct_ tag memberTerms) resBt loc

  -- Undefined behavior marker
  | .undef _uloc ub =>
    -- Encountering undef in pure expression is an error
    TypingM.fail (.other s!"Undefined behavior in pure expression: {repr ub}")

  -- Error expression
  | .error msg _ =>
    TypingM.fail (.other s!"Error in pure expression: {msg}")

  -- Implementation constants (sizeof, alignof, etc.)
  | .impl c =>
    match c with
    | .sizeof_ ct =>
      return AnnotTerm.mk (.sizeOf ct) .integer loc
    | .alignof_ ct =>
      -- alignof not directly in CN terms, use sizeof as approximation
      return AnnotTerm.mk (.sizeOf ct) .integer loc
    | .intMax ty =>
      -- Maximum value of integer type
      let maxVal := intTypeMax ty
      return AnnotTerm.mk (.const (.z maxVal)) .integer loc
    | .intMin ty =>
      -- Minimum value of integer type
      let minVal := intTypeMin ty
      return AnnotTerm.mk (.const (.z minVal)) .integer loc
    | .other name =>
      TypingM.fail (.other s!"Unknown implementation constant: {name}")

  -- Other cases not yet implemented
  | _ =>
    TypingM.fail (.other s!"Pure expression not yet supported")
where
  /-- Convert Core APattern to CN Pattern -/
  convertPattern (pat : APattern) (bt : BaseType) (loc : Core.Loc) : CerbLean.CN.Types.Pattern :=
    match pat.pat with
    | .base (some s) _ => .mk (.sym s) bt loc
    | .base none _ => .mk .wild bt loc
    | .ctor c args =>
      -- For constructor patterns, convert each sub-pattern
      let cnArgs := args.map fun p =>
        let subPat := convertPattern ⟨[], p⟩ bt loc
        -- Pattern_.constructor expects (Identifier × Pattern)
        let id : Identifier := { loc := Core.Loc.t.unknown, name := "" }
        (id, subPat)
      .mk (.constructor (ctorToSym c) cnArgs) bt loc

  /-- Convert a Core.Ctor to a Sym for CN patterns -/
  ctorToSym (c : Core.Ctor) : Sym :=
    match c with
    | .nil _ => { id := 0, name := some "Nil" }
    | .cons => { id := 0, name := some "Cons" }
    | .tuple => { id := 0, name := some "Tuple" }
    | .array => { id := 0, name := some "Array" }
    | .specified => { id := 0, name := some "Specified" }
    | .unspecified => { id := 0, name := some "Unspecified" }
    | _ => { id := 0, name := some "Unknown" }

  /-- Get maximum value of integer type -/
  intTypeMax : CerbLean.Core.IntegerType → Int
    | .char => 127
    | .bool => 1
    | .signed .short => 32767
    | .signed .int_ => 2147483647
    | .signed .long => 9223372036854775807
    | .signed .longLong => 9223372036854775807
    | .unsigned .short => 65535
    | .unsigned .int_ => 4294967295
    | .unsigned .long => 18446744073709551615
    | .unsigned .longLong => 18446744073709551615
    | .size_t => 18446744073709551615
    | .ptrdiff_t => 9223372036854775807
    | .ptraddr_t => 18446744073709551615
    | _ => 0

  /-- Get minimum value of integer type -/
  intTypeMin : CerbLean.Core.IntegerType → Int
    | .char => -128
    | .bool => 0
    | .signed .short => -32768
    | .signed .int_ => -2147483648
    | .signed .long => -9223372036854775808
    | .signed .longLong => -9223372036854775808
    | .unsigned _ => 0
    | .size_t => 0
    | .ptrdiff_t => -9223372036854775808
    | .ptraddr_t => 0
    | _ => 0

end CerbLean.CN.TypeChecking
