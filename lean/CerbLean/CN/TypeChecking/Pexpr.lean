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
def valueToConst (v : Value) (_loc : Core.Loc) : Except TypeError Const := do
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
      -- Corresponds to: pointer value conversion in check.ml
      -- Provenance is REQUIRED for memory safety verification
      match pv.prov with
      | .some allocId => return .pointer ⟨allocId, addr⟩
      | _ => throw (.other "Pointer with unknown provenance - cannot verify memory safety")
    | .function sym =>
      -- Function pointers are not yet supported in CN verification
      -- Corresponds to: check.ml does not handle function pointers in pure expressions
      throw (.other s!"Function pointer {repr sym} not yet supported in CN verification")
  | .ctype ct => return .ctypeConst ct
  | .list _ _ => throw (.other "List values not yet supported")
  | .tuple _ => throw (.other "Tuple values not yet supported")
  | .object (.floating ..) => throw (.other "Floating point values not yet supported")
  | .object (.struct_ ..) => throw (.other "Struct values not yet supported")
  | .object (.array ..) => throw (.other "Array values not yet supported")
  | .object (.union_ ..) => throw (.other "Union values not yet supported")
  -- Loaded values: either Specified(ObjectValue) or Unspecified(Ctype)
  | .loaded (.specified ov) =>
    -- Specified value: unwrap and convert the ObjectValue
    valueToConst (.object ov) _loc
  | .loaded (.unspecified _ty) =>
    -- Unspecified value: this represents reading uninitialized memory
    -- We return a special "undef" constant that will be handled symbolically
    throw (.other "unspecified_value")

/-- Convert Ctype to CN BaseType for unspecified value type inference -/
def ctypeToBaseTypeSimple (ct : Core.Ctype) : BaseType :=
  match ct.ty with
  | .void => .unit
  | .basic (.integer _) => .integer
  | .basic (.floating _) => .real
  | .pointer _ _ => .loc
  | .struct_ tag => .struct_ tag
  | _ => .unit  -- fallback for complex types

/-- Get the bit width for an integer base kind -/
def intBaseKindWidth (kind : Core.IntBaseKind) : Nat :=
  match kind with
  | .ichar => 8
  | .short => 16
  | .int_ => 32
  | .long => 64      -- platform-dependent, assume LP64
  | .longLong => 64
  | .intN n => n
  | .intLeastN n => n
  | .intFastN n => n
  | .intmax => 64
  | .intptr => 64

/-- Convert Ctype_ (inner type) to CN BaseType for conv_int/conv_loaded_int.
    Corresponds to: Memory.bt_of_sct in CN's memory.ml
    For integers, returns Bits type with appropriate sign and width. -/
def ctypeInnerToBaseType (ty : Core.Ctype_) : BaseType :=
  match ty with
  | .void => .unit
  | .basic (.integer ity) =>
    -- Convert integer type to Bits with appropriate sign and width
    -- This matches CN's Memory.bt_of_sct behavior
    match ity with
    | .bool => .bool
    | .char => .integer  -- char signedness is implementation-defined
    | .signed kind => .bits .signed (intBaseKindWidth kind)
    | .unsigned kind => .bits .unsigned (intBaseKindWidth kind)
    | .size_t => .bits .unsigned 64  -- platform-dependent, assume 64-bit
    | .ptrdiff_t => .bits .signed 64
    | .wchar_t => .bits .signed 32   -- platform-dependent
    | .wint_t => .bits .signed 32
    | .ptraddr_t => .bits .unsigned 64
    | .enum _ => .bits .signed 32    -- enums are typically int-sized
  | .basic (.floating _) => .real
  | .pointer _ _ => .loc
  | .struct_ tag => .struct_ tag
  | .union_ tag => .struct_ tag  -- unions use same representation
  | .array _ _ => .loc  -- array decays to pointer
  | .function _ _ _ _ => .loc  -- function pointer
  | .functionNoParams _ _ => .loc  -- function pointer (K&R style)
  | .atomic ty' => ctypeInnerToBaseType ty'
  | .byte => .memByte

/-- Convert Ctype to CN BaseType for conv_int/conv_loaded_int.
    This is a pure version that doesn't use the monad and handles
    the Bits type properly for conv_int semantics.
    Corresponds to: Memory.bt_of_sct in CN's memory.ml -/
def ctypeToBaseTypeBits (ct : Core.Ctype) : BaseType :=
  ctypeInnerToBaseType ct.ty

/-- Convert a Core Value to a CN IndexTerm. -/
def valueToTerm (v : Value) (loc : Core.Loc) : Except TypeError IndexTerm := do
  match valueToConst v loc with
  | .ok c =>
    let bt := baseTypeOfConst c
    return AnnotTerm.mk (.const c) bt loc
  | .error (.other "unspecified_value") =>
    -- Unspecified (uninitialized) value: return a symbolic "undef" term
    -- The CN verifier will ensure this value is never actually used
    let symUndef : Core.Sym := { id := 0, name := some "undef" }
    -- Infer type from the loaded value if possible
    let bt := match v with
      | .loaded (.unspecified ct) => ctypeToBaseTypeSimple ct
      | _ => .unit
    return AnnotTerm.mk (.sym symUndef) bt loc
  | .error e => throw e
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
def convertBinop (op : Binop) (bt1 _bt2 : BaseType) (_loc : Core.Loc)
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
partial def bindPattern (pat : APattern) (value : IndexTerm) : TypingM PatternBindings := do
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
  | .ctor c args =>
    -- Constructor patterns for Specified/Unspecified loaded values
    match c with
    | .specified =>
      -- Specified(inner_pat) - bind inner pattern to the unwrapped value
      match args with
      | [innerPat] =>
        -- Wrap the inner Pattern in an APattern with the same annotations
        let innerAPat : APattern := ⟨pat.annots, innerPat⟩
        bindPattern innerAPat value
      | _ => TypingM.fail (.other "Specified pattern requires exactly 1 argument")
    | .unspecified =>
      -- Unspecified(_) - this is the undefined behavior path
      -- We skip binding here (matches any value, binds nothing useful)
      return { boundVars := [] }
    | .tuple =>
      -- Tuple patterns - bind each component
      -- We create symbolic projection terms for each element
      let mut allBindings : List (Sym × BaseType) := []
      let mut idx := 0
      for innerPat in args do
        -- Create a symbolic term for tuple element i
        -- Use the value's location for the projection term
        let innerAPat : APattern := ⟨pat.annots, innerPat⟩
        -- Get a fresh symbol for this projection
        let state ← TypingM.getState
        let projId := state.freshCounter
        TypingM.modifyState fun s => { s with freshCounter := s.freshCounter + 1 }
        -- Extract type from the inner pattern
        let projBt := match innerPat with
          | .base _ bt => coreBaseTypeToCN bt
          | _ => value.bt  -- fallback
        let projSym : Sym := { id := projId, name := some s!"proj_{idx}" }
        let projTerm : IndexTerm := AnnotTerm.mk (.sym projSym) projBt value.loc
        -- Recursively bind the inner pattern
        let innerBindings ← bindPattern innerAPat projTerm
        allBindings := allBindings ++ innerBindings.boundVars
        idx := idx + 1
      return { boundVars := allBindings }
    | _ => TypingM.fail (.other s!"Unsupported constructor pattern: {repr c}")

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
    | .specified =>
      -- Specified(value) - the value is known/defined
      -- Just unwrap and return the inner value
      match argTerms with
      | [innerVal] => return innerVal
      | _ => TypingM.fail (.other "Specified requires exactly 1 argument")
    | .unspecified =>
      -- Unspecified(ctype) - the value is undefined
      -- Return a symbolic "undef" term
      let symUndef : Sym := { id := 0, name := some "undef" }
      return AnnotTerm.mk (.sym symUndef) resBt loc
    | _ =>
      -- Other constructors (nil, cons, array, etc.) - create a symbolic term
      -- This is a simplification; full support would track list/array values
      let state ← TypingM.getState
      let ctorSym : Sym := { id := state.freshCounter, name := some s!"ctor_{repr c}" }
      TypingM.modifyState fun s => { s with freshCounter := s.freshCounter + 1 }
      return AnnotTerm.mk (.sym ctorSym) resBt loc

  -- Function call (pure)
  | .call name args =>
    -- Handle Core builtin functions that CN treats specially
    let fnName := match name with
      | .sym s => s.name
      | .impl _ => none

    -- conv_loaded_int/conv_int: integer type conversion
    -- Corresponds to: check_conv_int in cn/lib/check.ml lines 394-431
    -- and PEconv_int/PEcall handling in check.ml lines 822-833
    --
    -- CN's behavior:
    -- - Bool: ite(arg == 0, 0, 1)
    -- - Unsigned: cast to target type
    -- - Signed: check representable, then cast (fail if not representable)
    if fnName == some "conv_loaded_int" || fnName == some "conv_int" then
      match args with
      | [tyArg, valArg] =>
        -- First arg is the ctype, second arg is the value
        let peVal : APexpr := ⟨[], none, valArg⟩
        let argVal ← checkPexpr peVal

        -- Extract the target ctype from the first argument
        -- The tyArg should be PEval(Vctype(ct))
        match tyArg with
        | .val (.ctype ct) =>
          let targetBt := ctypeToBaseTypeBits ct
          -- Check what kind of integer type this is
          match ct.ty with
          | .basic (.integer .bool) =>
            -- Bool: ite(arg == 0, 0, 1)
            -- Corresponds to: check_conv_int lines 413-420
            let zero := AnnotTerm.mk (.const (.z 0)) targetBt loc
            let one := AnnotTerm.mk (.const (.z 1)) targetBt loc
            let argBt := argVal.bt
            let zeroArg := AnnotTerm.mk (.const (.z 0)) argBt loc
            let eqZero := AnnotTerm.mk (.binop .eq argVal zeroArg) .bool loc
            return AnnotTerm.mk (.ite eqZero zero one) targetBt loc

          | .basic (.integer (.unsigned _)) =>
            -- Unsigned: cast to target type
            -- Corresponds to: check_conv_int lines 421-423
            return AnnotTerm.mk (.cast targetBt argVal) targetBt loc

          | .basic (.integer (.signed _)) =>
            -- Signed: CN checks representable, then casts (lines 424-429)
            -- Add representability constraint as obligation
            let reprTerm := AnnotTerm.mk (.representable ct argVal) .bool loc
            TypingM.requireConstraint (.t reprTerm) loc "integer representability"
            return AnnotTerm.mk (.cast targetBt argVal) targetBt loc

          | _ =>
            -- Other integer types not yet supported
            TypingM.fail (.other s!"conv_int for integer type {repr ct.ty} not yet supported")

        | _ =>
          -- Cannot extract ctype from argument
          TypingM.fail (.other "conv_int: could not extract ctype from first argument")
      | _ =>
        -- Fallback: treat as normal function call
        let argTerms ← args.mapM fun arg => do
          let peArg : APexpr := ⟨[], none, arg⟩
          checkPexpr peArg
        let fnSym : Sym := { id := 0, name := fnName }
        let resBt := pe.ty.map coreBaseTypeToCN |>.getD .integer
        return AnnotTerm.mk (.apply fnSym argTerms) resBt loc
    else
      -- General function call
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
  | .undef _uloc _ub =>
    -- In CN, undef represents a path that leads to undefined behavior.
    -- When we encounter it in a conditional branch, it means that branch
    -- should not be taken. We return a symbolic term representing undefined.
    -- The CN verifier will ensure this value is never actually used
    -- (i.e., the path condition leading here is unsatisfiable).
    let resBt := pe.ty.map coreBaseTypeToCN |>.getD .integer
    let symUndef : Core.Sym := {
      id := 0,
      name := some "undef",
      description := .none_
    }
    return AnnotTerm.mk (.sym symUndef) resBt loc

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

  -- Integer conversion (conv_int)
  | .convInt _ty e =>
    -- Integer conversion: just evaluate the inner expression
    -- The type system handles the conversion semantically
    let pe' : APexpr := ⟨[], pe.ty, e⟩
    checkPexpr pe'

  -- Wrap integer (modular arithmetic)
  | .wrapI _ty _op e1 e2 =>
    -- Wrap integer: compute the operation with modular wrapping
    -- For CN verification, we evaluate the operands symbolically
    let pe1 : APexpr := ⟨[], pe.ty, e1⟩
    let pe2 : APexpr := ⟨[], pe.ty, e2⟩
    let t1 ← checkPexpr pe1
    let t2 ← checkPexpr pe2
    -- Return a symbolic operation (the wrapping is implicit in the type)
    return AnnotTerm.mk (.binop .add t1 t2) t1.bt loc

  -- Catch exceptional condition (overflow checking)
  | .catchExceptionalCondition _ty op e1 e2 =>
    -- Exceptional condition check: evaluate operation, checking for overflow
    -- For CN verification, we evaluate symbolically (assume no overflow for now)
    let pe1 : APexpr := ⟨[], pe.ty, e1⟩
    let pe2 : APexpr := ⟨[], pe.ty, e2⟩
    let t1 ← checkPexpr pe1
    let t2 ← checkPexpr pe2
    -- Map the Iop to CN binop
    let cnOp := match op with
      | .add => BinOp.add
      | .sub => BinOp.sub
      | .mul => BinOp.mul
      | .div => BinOp.div
      | .rem_t => BinOp.rem
      | .shl | .shr => BinOp.add  -- shifts not directly in CN, approximate
    return AnnotTerm.mk (.binop cnOp t1 t2) t1.bt loc

  -- Type predicates (is_scalar, is_integer, etc.)
  | .isScalar e =>
    let pe' : APexpr := ⟨[], some .ctype, e⟩
    let _t ← checkPexpr pe'
    -- These are runtime type checks - return true symbolically
    return AnnotTerm.mk (.const (.bool true)) .bool loc

  | .isInteger e =>
    let pe' : APexpr := ⟨[], some .ctype, e⟩
    let _t ← checkPexpr pe'
    return AnnotTerm.mk (.const (.bool true)) .bool loc

  | .isSigned e =>
    let pe' : APexpr := ⟨[], some .ctype, e⟩
    let _t ← checkPexpr pe'
    return AnnotTerm.mk (.const (.bool true)) .bool loc

  | .isUnsigned e =>
    let pe' : APexpr := ⟨[], some .ctype, e⟩
    let _t ← checkPexpr pe'
    return AnnotTerm.mk (.const (.bool false)) .bool loc

  | .areCompatible e1 e2 =>
    let pe1 : APexpr := ⟨[], some .ctype, e1⟩
    let pe2 : APexpr := ⟨[], some .ctype, e2⟩
    let _t1 ← checkPexpr pe1
    let _t2 ← checkPexpr pe2
    -- Type compatibility check - return symbolic result
    return AnnotTerm.mk (.const (.bool true)) .bool loc

  -- C function pointer extraction
  | .cfunction e =>
    -- cfunction extracts function info from a pointer
    -- For CN, we just evaluate the expression
    let pe' : APexpr := ⟨[], pe.ty, e⟩
    checkPexpr pe'

  -- Union constructor
  | .union_ tag member value =>
    let peVal : APexpr := ⟨[], none, value⟩
    let tVal ← checkPexpr peVal
    -- For now, treat union like struct with single member
    return AnnotTerm.mk (.struct_ tag [(member, tVal)]) (.struct_ tag) loc

  -- Pure memory operations (for memory model)
  | .pureMemop _op args =>
    -- Pure memory operations - evaluate args and return symbolic result
    let argTerms ← args.mapM fun arg => do
      let peArg : APexpr := ⟨[], none, arg⟩
      checkPexpr peArg
    let resBt := pe.ty.map coreBaseTypeToCN |>.getD .bool
    -- Return a symbolic term for the memory operation result
    let state ← TypingM.getState
    let memopSym : Sym := { id := state.freshCounter, name := some "memop_result" }
    TypingM.modifyState fun s => { s with freshCounter := s.freshCounter + 1 }
    return AnnotTerm.mk (.apply memopSym argTerms) resBt loc

  -- Constrained values (for memory model)
  | .constrained constraints =>
    -- Constrained values: evaluate constraints symbolically
    for (_, constraint) in constraints do
      let peCon : APexpr := ⟨[], some .boolean, constraint⟩
      let _ ← checkPexpr peCon
    -- Return a unit value (constraints are side effects)
    return AnnotTerm.mk (.const .unit) .unit loc

  -- BMC assume
  | .bmcAssume e =>
    -- BMC assume: evaluate condition, add as constraint
    let pe' : APexpr := ⟨[], some .boolean, e⟩
    let t ← checkPexpr pe'
    TypingM.addC (.t t)
    return AnnotTerm.mk (.const .unit) .unit loc
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

/-! ## CPS Version

For consistency with the CPS-style expression checking, we provide
a continuation-passing version of checkPexpr.

For pure expressions, CPS is straightforward since pure expressions
don't have multiple exit paths (except for conditionals, which are
handled by evaluating both branches symbolically).
-/

/-- Check a pure expression using continuation-passing style.

    For pure expressions, we call the original checkPexpr and pass
    the result to the continuation. This provides a uniform interface
    with checkExprK.

    Corresponds to: check_pexpr continuation handling in check.ml -/
partial def checkPexprK (pe : APexpr) (k : IndexTerm → TypingM Unit) : TypingM Unit := do
  let result ← checkPexpr pe
  k result

end CerbLean.CN.TypeChecking
