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

/-- Convert a Core IntegerType to CN BaseType.
    Uses the same width logic as Resolve.lean for consistency.
    Corresponds to: Memory.bt_of_sct in CN's memory.ml -/
def integerTypeToBaseType (ity : Core.IntegerType) : BaseType :=
  match ity with
  | .bool => .bool
  | .char => .integer  -- char signedness is implementation-defined
  | .signed kind =>
    let width := match kind with
      | .ichar => 8
      | .short => 16
      | .int_ => 32
      | .long => 64
      | .longLong => 64
      | .intN n => n
      | .intLeastN n => n
      | .intFastN n => n
      | .intmax => 64
      | .intptr => 64
    .bits .signed width
  | .unsigned kind =>
    let width := match kind with
      | .ichar => 8
      | .short => 16
      | .int_ => 32
      | .long => 64
      | .longLong => 64
      | .intN n => n
      | .intLeastN n => n
      | .intFastN n => n
      | .intmax => 64
      | .intptr => 64
    .bits .unsigned width
  | .size_t => .bits .unsigned 64
  | .ptrdiff_t => .bits .signed 64
  | .wchar_t => .bits .signed 32
  | .wint_t => .bits .signed 32
  | .ptraddr_t => .bits .unsigned 64
  | .enum _ => .bits .signed 32

/-- Create a numeric literal with the given base type.
    Corresponds to: CN's num_lit_ in indexTerms.ml lines 478-484

    CN's behavior:
    - For Bits types: creates Bits constant with sign/width
    - For Integer type: creates unbounded integer constant
    - For other types: falls back to integer -/
def numLit (n : Int) (bt : BaseType) (loc : Core.Loc) : IndexTerm :=
  match bt with
  | .bits sign width =>
    AnnotTerm.mk (.const (.bits sign width n)) bt loc
  | .integer =>
    AnnotTerm.mk (.const (.z n)) .integer loc
  | _ =>
    -- Fallback to integer for other types (matches CN's default)
    AnnotTerm.mk (.const (.z n)) .integer loc

/-- Extract a location from an annotation -/
def getAnnotLoc : Core.Annot → Option Core.Loc
  | .loc l => some l
  | .inlinedLabel l _ _ => some l
  | _ => none

/-- Extract location from a list of annotations -/
def getAnnotsLoc (annots : List Core.Annot) : Core.Loc :=
  annots.findSome? getAnnotLoc |>.getD Core.Loc.t.unknown

/-! ## Ctype Extraction for Memops

CN memops like PtrValidForDeref take a ctype as their first argument.
The ctype is passed as a pure expression containing a ctype constant.
Corresponds to: check_pexpr_good_ctype_const in cn/lib/check.ml
-/

/-- Extract a Ctype constant from a pure expression.
    Used for memop type arguments.
    Corresponds to: check_pexpr_good_ctype_const in check.ml -/
def extractCtypeConst (pe : APexpr) : Except TypeError Core.Ctype :=
  match pe.expr with
  | .val (.ctype ct) => .ok ct
  | _ => .error (.other "Expected ctype constant in memop argument")

/-- Calculate alignment of a C type inner representation.
    Returns none for types that require TypeEnv lookup (struct, union, array).
    Corresponds to: Memory.align_of_ctype in CN's memory.ml -/
def alignOfCtype_ (ct : Core.Ctype_) : Option Nat :=
  match ct with
  | .void => some 1
  | .basic (.integer ity) =>
    some <| match ity with
    | .bool => 1
    | .char => 1
    | .signed k | .unsigned k =>
      match k with
      | .ichar => 1
      | .short => 2
      | .int_ => 4
      | .long | .longLong | .intptr => 8
      | .intN n | .intLeastN n | .intFastN n => min ((n + 7) / 8) 16
      | .intmax => 8
    | .size_t | .ptrdiff_t | .ptraddr_t => 8
    | .wchar_t | .wint_t => 4
    | .enum _ => 4
  | .basic (.floating fty) =>
    some <| match fty with
    | .realFloating .float => 4
    | .realFloating .double => 8
    | .realFloating .longDouble => 16
  | .pointer _ _ => some 8  -- 64-bit architecture
  | .function _ _ _ _ | .functionNoParams _ _ => some 1  -- function types have alignment 1
  | .atomic ct' => alignOfCtype_ ct'  -- Recurse on inner Ctype_
  | .byte => some 1
  -- Types requiring TypeEnv lookup - fail explicitly
  | .array _ _ => none
  | .struct_ _ => none
  | .union_ _ => none

/-- Calculate alignment of a C type.
    Returns none for types that require TypeEnv lookup (struct, union, array).
    Corresponds to: Memory.align_of_ctype in CN's memory.ml -/
def alignOfCtype (ct : Core.Ctype) : Option Nat :=
  alignOfCtype_ ct.ty

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

/-- Convert Ctype to CN BaseType for unspecified value type inference.
    Returns none for unsupported types (arrays, unions, functions, atomics). -/
def ctypeToBaseTypeSimple (ct : Core.Ctype) : Option BaseType :=
  match ct.ty with
  | .void => some .unit
  | .basic (.integer _) => some .integer
  | .basic (.floating _) => some .real
  | .pointer _ _ => some .loc
  | .struct_ tag => some (.struct_ tag)
  | .array _ _ => none  -- Arrays not supported
  | .union_ _ => none   -- Unions not supported
  | .function _ _ _ _ => none  -- Functions not supported
  | .functionNoParams _ _ => none  -- K&R functions not supported
  | .atomic _ => none   -- Atomics not supported
  | .byte => none  -- Byte type not supported

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

/-- Convert a Core Value to a CN IndexTerm.
    If expectedBt is provided and is a Bits type, use it for integer literals
    (matches CN's type-aware literal creation via num_lit_). -/
def valueToTerm (v : Value) (loc : Core.Loc) (expectedBt : Option BaseType := none) : Except TypeError IndexTerm := do
  match valueToConst v loc with
  | .ok c =>
    -- For integer constants, use expected type if it's Bits
    -- This matches CN's num_lit_ which creates Bits literals at construction time
    match c, expectedBt with
    | .z n, some (.bits sign width) =>
      return AnnotTerm.mk (.const (.bits sign width n)) (.bits sign width) loc
    | _, _ =>
      let bt := baseTypeOfConst c
      return AnnotTerm.mk (.const c) bt loc
  | .error (.other "unspecified_value") =>
    -- Unspecified (uninitialized) value: return a symbolic "undef" term
    -- The CN verifier will ensure this value is never actually used
    let symUndef : Core.Sym := { id := 0, name := some "undef" }
    -- Infer type from the loaded value - MUST have valid type
    let bt ← match v with
      | .loaded (.unspecified ct) =>
        match ctypeToBaseTypeSimple ct with
        | some bt => pure bt
        | none => throw (.other s!"Unsupported type in unspecified value: {repr ct.ty}")
      | _ => throw (.other "Cannot determine type for unspecified value")
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

/-- Convert Core.BaseType to CN.BaseType.
    For object and loaded types with integer content, returns proper Bits type.
    Corresponds to: CN's handling of object/loaded types for integers.
    Returns none for unsupported types (list, tuple, storable). -/
def coreBaseTypeToCN (bt : Core.BaseType) : Option BaseType :=
  match bt with
  | .unit => some .unit
  | .boolean => some .bool
  | .ctype => some .ctype
  | .list _ => none  -- Lists not supported in CN base types
  | .tuple _ => none  -- Tuples not supported (should use tuple element types)
  | .object ot => objectTypeToCN ot
  | .loaded ot => objectTypeToCN ot  -- loaded types use the inner object type
  | .storable => none  -- Storable not supported
where
  /-- Convert Core.ObjectType to CN.BaseType -/
  objectTypeToCN : Core.ObjectType → Option BaseType
    | .integer => some (.bits .signed 32)  -- Default to signed 32-bit for unspecified integers
    | .floating => some .real
    | .pointer => some .loc
    | .array _ => some .loc  -- Arrays are accessed via pointers
    | .struct_ tag => some (.struct_ tag)
    | .union_ tag => some (.struct_ tag)  -- Unions use same representation as structs

/-- Require a Core.BaseType to be convertible to CN.BaseType, failing otherwise.
    Use this instead of `.getD` patterns which silently mask type errors. -/
def requireCoreBaseTypeToCN (bt : Option Core.BaseType) (context : String) : TypingM BaseType := do
  match bt with
  | none => TypingM.fail (.other s!"{context}: no Core type annotation available")
  | some coreBt =>
    match coreBaseTypeToCN coreBt with
    | some cnBt => pure cnBt
    | none => TypingM.fail (.other s!"{context}: unsupported Core type {repr coreBt}")

/-- Bind a pattern to a value, returning the bound variables.
    Corresponds to: check_and_match_pattern in check.ml -/
partial def bindPattern (pat : APattern) (value : IndexTerm) : TypingM PatternBindings := do
  match pat.pat with
  | .base (some sym) bt =>
    -- Bind variable to value
    let loc := value.loc
    let cnBt ← match coreBaseTypeToCN bt with
      | some t => pure t
      | none => TypingM.fail (.other s!"Unsupported Core base type in pattern: {repr bt}")
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
      --
      -- Type handling: Extract element types from the tuple type.
      -- If value.bt is BaseType.tuple elemTypes, use elemTypes[idx] for each element.
      -- This ensures proper type propagation through tuple destructuring.
      let elemTypes ← match value.bt with
        | .tuple ts => pure ts
        | other =>
          -- Non-tuple value being destructured as tuple - this indicates a type error
          -- Fall back to pattern-declared types if args have base patterns with types
          -- Otherwise fail explicitly
          if args.all (fun p => match p with | .base _ _ => true | _ => false) then
            pure []  -- Will use pattern types for each element
          else
            TypingM.fail (.other s!"Tuple pattern applied to non-tuple value of type: {repr other}")

      let mut allBindings : List (Sym × BaseType) := []
      let mut idx := 0
      for innerPat in args do
        let innerAPat : APattern := ⟨pat.annots, innerPat⟩
        -- Get a fresh symbol for this projection
        let state ← TypingM.getState
        let projId := state.freshCounter
        TypingM.modifyState fun s => { s with freshCounter := s.freshCounter + 1 }

        -- Determine element type: prefer tuple element type, then pattern type
        let projBt ← match elemTypes[idx]? with
          | some elemBt =>
            -- Have tuple element type - use it
            pure elemBt
          | none =>
            -- No tuple type info - must use pattern's declared type
            match innerPat with
            | .base _ bt =>
              match coreBaseTypeToCN bt with
              | some t => pure t
              | none => TypingM.fail (.other s!"Unsupported Core base type in tuple pattern element {idx}: {repr bt}")
            | .ctor _ _ =>
              -- Constructor pattern without tuple type info - need pattern's enclosing type
              -- For Specified/Unspecified patterns, the type should come from context
              TypingM.fail (.other s!"Cannot determine type for constructor pattern at index {idx} - value is not a proper tuple")

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
    | some (.baseType bt) => return AnnotTerm.mk (.sym s) bt loc
    | none => TypingM.fail (.unboundVariable s)

/-! ## Pure Expression Checking

Main function to check pure expressions and convert to index terms.
Corresponds to: check_pexpr in check.ml
-/

/-- Check a pure expression and convert to an IndexTerm.
    The optional expectedBt parameter provides the expected CN BaseType for
    type-aware literal creation (matching CN's num_lit_ behavior).
    Corresponds to: check_pexpr in cn/lib/check.ml -/
partial def checkPexpr (pe : APexpr) (expectedBt : Option BaseType := none) : TypingM IndexTerm := do
  let loc := getAnnotsLoc pe.annots
  match pe.expr with
  -- Variable reference
  | .sym s => lookupVar s loc

  -- Literal value
  -- Pass expected type to create Bits literals when type hint is available
  -- Prefer explicit expectedBt parameter over pe.ty hint
  | .val v =>
    let typeHint := expectedBt.orElse (fun _ => pe.ty.bind coreBaseTypeToCN)
    match valueToTerm v loc typeHint with
    | .ok term => return term
    | .error err => TypingM.fail err

  -- Binary operation
  -- Corresponds to: binop checking in check.ml
  -- Type propagation: check first operand, use its type as expected for second operand.
  -- This ensures literals get appropriate types from context (e.g., `x < 1000` where x is BitVec).
  | .op op e1 e2 =>
    let pe1 : APexpr := ⟨[], pe.ty, e1⟩
    -- Check first operand (with expected type if available)
    let t1 ← checkPexpr pe1 expectedBt
    -- Use first operand's type as expected type for second operand
    let pe2 : APexpr := ⟨[], pe.ty, e2⟩
    let t2 ← checkPexpr pe2 (some t1.bt)
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
  -- Propagate expected type to both branches
  | .if_ cond thenE elseE =>
    let peCond : APexpr := ⟨[], some .boolean, cond⟩
    let peThen : APexpr := ⟨[], pe.ty, thenE⟩
    let peElse : APexpr := ⟨[], pe.ty, elseE⟩
    let tCond ← checkPexpr peCond (some .bool)
    let tThen ← checkPexpr peThen expectedBt
    let tElse ← checkPexpr peElse expectedBt
    return AnnotTerm.mk (.ite tCond tThen tElse) tThen.bt loc

  -- Let binding
  -- Propagate expected type to body expression
  | .let_ pat e1 e2 =>
    let pe1 : APexpr := ⟨[], none, e1⟩
    let v1 ← checkPexpr pe1
    let bindings ← bindPattern pat v1
    let pe2 : APexpr := ⟨[], pe.ty, e2⟩
    let result ← checkPexpr pe2 expectedBt
    unbindPattern bindings
    return result

  -- Struct member access
  | .memberof _tag member e =>
    let pe' : APexpr := ⟨[], none, e⟩
    let tStruct ← checkPexpr pe'
    -- Return the appropriate base type based on member
    let resBt ← requireCoreBaseTypeToCN pe.ty s!"memberof {member.name}"
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
    match c with
    | .tuple =>
      -- For tuples, evaluate each arg without expected type (tuple elements are independent)
      let argTerms ← args.mapM fun arg => do
        let peArg : APexpr := ⟨[], none, arg⟩
        checkPexpr peArg
      let elemTypes := argTerms.map (·.bt)
      let tupleBt := BaseType.tuple elemTypes
      return AnnotTerm.mk (.tuple argTerms) tupleBt loc
    | .specified =>
      -- Specified(value) - the value is known/defined
      -- Propagate expected type to inner value (Specified wraps a value of that type)
      match args with
      | [innerArg] =>
        let peArg : APexpr := ⟨[], none, innerArg⟩
        let innerVal ← checkPexpr peArg expectedBt
        return innerVal
      | _ => TypingM.fail (.other "Specified requires exactly 1 argument")
    | .unspecified =>
      -- Unspecified(ctype) - the value is undefined
      -- Return a symbolic "undef" term
      -- Type must come from expected type or pattern annotation
      let unspecBt ← match expectedBt with
        | some bt => pure bt
        | none => match pe.ty.bind coreBaseTypeToCN with
          | some bt => pure bt
          | none => TypingM.fail (.other "Cannot determine type for Unspecified value")
      let symUndef : Sym := { id := 0, name := some "undef" }
      return AnnotTerm.mk (.sym symUndef) unspecBt loc
    | _ =>
      -- Other constructors (nil, cons, array, etc.) are not supported
      -- Do not create symbolic terms - fail explicitly
      TypingM.fail (.other s!"Unsupported constructor in expression: {repr c}")

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

          -- Helper to convert integer constants to Bits constants
          -- This matches CN's type-aware literal creation
          let convertToBits (v : IndexTerm) : IndexTerm :=
            match targetBt, v.term with
            | .bits sign width, .const (.z n) =>
              -- Convert integer constant to Bits constant
              AnnotTerm.mk (.const (.bits sign width n)) targetBt v.loc
            | .bits _ _, _ =>
              -- For non-constant values, wrap in cast (symbolic)
              AnnotTerm.mk (.cast targetBt v) targetBt v.loc
            | _, _ => v  -- Non-bits target, keep as-is

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
            return convertToBits argVal

          | .basic (.integer (.signed _)) =>
            -- Signed: CN checks representable, then casts (lines 424-429)
            -- Add representability constraint as obligation
            let reprTerm := AnnotTerm.mk (.representable ct argVal) .bool loc
            TypingM.requireConstraint (.t reprTerm) loc "integer representability"
            return convertToBits argVal

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
        let fnStr := fnName.getD "unknown"
        let resBt ← requireCoreBaseTypeToCN pe.ty s!"function call {fnStr}"
        return AnnotTerm.mk (.apply fnSym argTerms) resBt loc
    else
      -- General function call
      let argTerms ← args.mapM fun arg => do
        let peArg : APexpr := ⟨[], none, arg⟩
        checkPexpr peArg
      let fnSym := match name with
        | .sym s => s
        | .impl _ => { id := 0, name := some "impl_const" : Sym }  -- Placeholder
      let fnNameStr := match name with
        | .sym s => s.name.getD "unknown"
        | .impl _ => "impl"
      let resBt ← requireCoreBaseTypeToCN pe.ty s!"function call {fnNameStr}"
      return AnnotTerm.mk (.apply fnSym argTerms) resBt loc

  -- Case/match expression
  -- Propagate expected type to branch bodies
  | .case_ scrut branches =>
    let peScrut : APexpr := ⟨[], none, scrut⟩
    let tScrut ← checkPexpr peScrut
    -- Convert branches
    let cnBranches ← branches.mapM fun (pat, body) => do
      let bindings ← bindPattern pat tScrut
      let peBody : APexpr := ⟨[], pe.ty, body⟩
      let tBody ← checkPexpr peBody expectedBt
      unbindPattern bindings
      -- Convert APattern to CN Pattern
      let cnPat := convertPattern pat tScrut.bt loc
      return (cnPat, tBody)
    let resBt ← requireCoreBaseTypeToCN pe.ty "case/match expression"
    return AnnotTerm.mk (.match_ tScrut cnBranches) resBt loc

  -- Struct literal
  | .struct_ tag members =>
    let memberTerms ← members.mapM fun (id, expr) => do
      let peExpr : APexpr := ⟨[], none, expr⟩
      let tExpr ← checkPexpr peExpr
      return (id, tExpr)
    -- For struct literals, we know the type from the tag; use pe.ty if available for consistency
    let resBt ← match pe.ty.bind coreBaseTypeToCN with
      | some bt => pure bt
      | none => pure (.struct_ tag)  -- Struct tag provides the type when annotation missing
    return AnnotTerm.mk (.struct_ tag memberTerms) resBt loc

  -- Undefined behavior marker
  | .undef _uloc _ub =>
    -- In CN, undef represents a path that leads to undefined behavior.
    -- When we encounter it in a conditional branch, it means that branch
    -- should not be taken. We return a symbolic term representing undefined.
    -- The CN verifier will ensure this value is never actually used
    -- (i.e., the path condition leading here is unsatisfiable).
    let resBt ← requireCoreBaseTypeToCN pe.ty "undef expression"
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
    | .alignof_ _ct =>
      -- alignof not supported in CN terms
      TypingM.fail (.other "alignof not supported - CN does not have alignof terms")
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
  | .wrapI ty _op e1 e2 =>
    -- Wrap integer: compute the operation with modular wrapping
    -- Use the IntegerType to determine the proper Bits type for operands
    -- Corresponds to: CN's handling of integer operations with Bits types
    let opBt := integerTypeToBaseType ty
    let pe1 : APexpr := ⟨[], none, e1⟩
    let pe2 : APexpr := ⟨[], none, e2⟩
    let t1 ← checkPexpr pe1 (some opBt)
    let t2 ← checkPexpr pe2 (some t1.bt)
    -- Return a symbolic operation (the wrapping is implicit in the type)
    return AnnotTerm.mk (.binop .add t1 t2) t1.bt loc

  -- Catch exceptional condition (overflow checking)
  | .catchExceptionalCondition ty op e1 e2 =>
    -- Exceptional condition check: evaluate operation, checking for overflow
    -- Use the IntegerType to determine the proper Bits type for operands
    -- This is critical: ensures that 0 in "0 - x" (negation) gets Bits type
    -- Corresponds to: CN's handling of PEcatch_exceptional_condition
    let opBt := integerTypeToBaseType ty
    let pe1 : APexpr := ⟨[], none, e1⟩
    let pe2 : APexpr := ⟨[], none, e2⟩
    let t1 ← checkPexpr pe1 (some opBt)
    let t2 ← checkPexpr pe2 (some t1.bt)
    -- Map the Iop to CN binop
    let cnOp ← match op with
      | .add => pure BinOp.add
      | .sub => pure BinOp.sub
      | .mul => pure BinOp.mul
      | .div => pure BinOp.div
      | .rem_t => pure BinOp.rem
      | .shl => TypingM.fail (.other "shift left (shl) not supported in CN catch_exceptional_condition")
      | .shr => TypingM.fail (.other "shift right (shr) not supported in CN catch_exceptional_condition")
    return AnnotTerm.mk (.binop cnOp t1 t2) t1.bt loc

  -- Type predicates (is_scalar, is_integer, etc.)
  -- These require actual type checking, not constant returns
  | .isScalar _e =>
    TypingM.fail (.other "isScalar type predicate not implemented - requires type analysis")

  | .isInteger _e =>
    TypingM.fail (.other "isInteger type predicate not implemented - requires type analysis")

  | .isSigned _e =>
    TypingM.fail (.other "isSigned type predicate not implemented - requires type analysis")

  | .isUnsigned _e =>
    TypingM.fail (.other "isUnsigned type predicate not implemented - requires type analysis")

  | .areCompatible _e1 _e2 =>
    TypingM.fail (.other "areCompatible type predicate not implemented - requires type analysis")

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
    let resBt ← requireCoreBaseTypeToCN pe.ty "pureMemop"
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

    The optional expectedBt parameter is used when the caller knows the expected
    type (e.g., from a computational argument in AT). This allows type-aware
    literal creation matching CN's num_lit_ behavior.

    Corresponds to: check_pexpr continuation handling in check.ml -/
partial def checkPexprK (pe : APexpr) (k : IndexTerm → TypingM Unit)
    (expectedBt : Option BaseType := none) : TypingM Unit := do
  -- Pass expectedBt directly to checkPexpr for type-aware literal creation
  let result ← checkPexpr pe expectedBt
  k result

end CerbLean.CN.TypeChecking
