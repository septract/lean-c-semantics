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

open CerbLean.Core (Sym Identifier Pexpr APexpr Value Binop Pattern APattern ObjectValue Ctor)

/-- Check if a pattern contains an Unspecified constructor.
    CN's muCore transformation strips Unspecified branches from case expressions
    (since CN assumes loaded values are always Specified). We mirror this by
    skipping branches whose patterns contain Unspecified constructors.
    Corresponds to: core_to_mucore.ml stripping of Unspecified branches -/
def patternContainsUnspecified : Pattern → Bool
  | .base _ _ => false
  | .ctor c args =>
    c == .unspecified || goUnspec args
where
  goUnspec : List Pattern → Bool
    | [] => false
    | p :: ps => patternContainsUnspecified p || goUnspec ps

/-- Check if a pattern contains a Specified constructor -/
def patternContainsSpecified : Pattern → Bool
  | .base _ _ => false
  | .ctor c args =>
    c == .specified || goSpec args
where
  goSpec : List Pattern → Bool
    | [] => false
    | p :: ps => patternContainsSpecified p || goSpec ps

/-- Filter case branches to keep only Specified branches.
    CN's muCore transformation strips Unspecified branches from case
    expressions on loaded values. We mirror this by:
    1. Removing branches with Unspecified patterns
    2. If any remaining branch has Specified patterns, removing wildcard
       branches (which are catch-alls for the Unspecified case)
    Corresponds to: core_to_mucore.ml stripping of Unspecified branches -/
def filterSpecifiedBranches (branches : List (APattern × α))
    : List (APattern × α) :=
  -- Step 1: remove branches with explicit Unspecified patterns
  let filtered := branches.filter fun (pat, _) =>
    !patternContainsUnspecified pat.pat
  -- Step 2: if any branch has Specified, keep only Specified branches
  -- (removes wildcards that are catch-alls for the Unspecified case)
  let hasSpecified := filtered.any fun (pat, _) =>
    patternContainsSpecified pat.pat
  if hasSpecified then
    filtered.filter fun (pat, _) => patternContainsSpecified pat.pat
  else
    filtered
open CerbLean.CN.Types

/-- The canonical undef symbol used for undefined behavior markers.
    All code that creates undef terms should use this symbol for consistency.
    Code that detects undef terms (e.g., simplifyPointerForResource) checks
    against this symbol's id and name. -/
def undefSym : Core.Sym := { id := 0, name := some "undef", description := .none_ }

/-- Check if a symbol is the canonical undef marker -/
def isUndefSym (s : Core.Sym) : Bool := s.id == 0 && s.name == some "undef"

/-! ## Helpers for Built-in Function Evaluation

These support concrete evaluation of Cerberus built-in functions
(cfunction, params_length, params_nth, are_compatible) that appear
as guards around ccall. When evaluated concretely, the branch conditions
become literal true/false and conditional failure obligations become trivial.
-/

/-- Build a concrete cons-list index term from a list of items. -/
def buildConsList (elemBt : BaseType) (items : List IndexTerm) (loc : Core.Loc) : IndexTerm :=
  items.foldr (init := AnnotTerm.mk (.nil elemBt) (.list elemBt) loc)
    fun item acc => AnnotTerm.mk (.cons item acc) (.list elemBt) loc

/-- Destructure a cons-list index term into its elements.
    Returns none if the term is not a concrete list. -/
def destList : IndexTerm → Option (List IndexTerm)
  | ⟨.nil _, _, _⟩ => some []
  | ⟨.cons hd tl, _, _⟩ => do let rest ← destList tl; return hd :: rest
  | _ => none

/-- Create a boolean literal index term. -/
def boolLit (b : Bool) (loc : Core.Loc) : IndexTerm :=
  AnnotTerm.mk (.const (.bool b)) .bool loc

/-! ## Helper Functions -/

/-- Convert a Core IntegerType to CN BaseType.
    Uses the same width logic as Resolve.lean for consistency.
    Corresponds to: Memory.bt_of_sct in CN's memory.ml -/
def integerTypeToBaseType (ity : Core.IntegerType) : BaseType :=
  match ity with
  | .bool => .bool
  | .char => .bits .signed 8  -- Cerberus treats char as signed 8-bit
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
  | other =>
    -- numLit should only be called with Bits or Integer types.
    -- Any other type indicates a bug in the caller.
    panic! s!"numLit called with unexpected base type: {repr other}"

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
    | .char => .bits .signed 8  -- Cerberus treats char as signed 8-bit
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
  -- Handle function pointers specially: they are symbolic locations, not constants.
  -- In Core IR, function pointers appear as Specified(Cfunction(sym)) in ccall setup.
  -- CN treats function pointers as BT.Loc; the symbol is used for spec lookup.
  -- Corresponds to: function pointer handling in CN's core_to_mucore.ml
  match v with
  | .object (.pointer pv) =>
    match pv.base with
    | .function sym => return AnnotTerm.mk (.sym sym) .loc loc
    | _ => pure ()  -- Fall through to standard conversion below
  | .loaded (.specified (.pointer pv)) =>
    match pv.base with
    | .function sym => return AnnotTerm.mk (.sym sym) .loc loc
    | _ => pure ()
  | _ => pure ()
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
    -- Infer type from the loaded value - MUST have valid type
    let bt ← match v with
      | .loaded (.unspecified ct) =>
        match ctypeToBaseTypeSimple ct with
        | some bt => pure bt
        | none => throw (.other s!"Unsupported type in unspecified value: {repr ct.ty}")
      | _ => throw (.other "Cannot determine type for unspecified value")
    return AnnotTerm.mk (.sym undefSym) bt loc
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
  | .list .ctype => some (.list .ctype)  -- list ctype from cfunction() result
  | .list _ => none  -- Other list types not supported in CN base types
  | .tuple _ => none  -- Tuples not supported (should use tuple element types)
  | .object ot => objectTypeToCN ot
  | .loaded ot => objectTypeToCN ot  -- loaded types use the inner object type
  | .storable => none  -- Storable not supported
where
  /-- Convert Core.ObjectType to CN.BaseType -/
  objectTypeToCN : Core.ObjectType → Option BaseType
    -- Core's ObjectType.integer carries no sign/width info.
    -- CN uses Memory.bt_of_sct which takes the full Sctypes.t with exact integer type.
    -- We return none here because we genuinely don't know the precise type.
    -- Callers must get the actual type from the value or C-level type context.
    | .integer => none
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
    -- The actual CN type comes from the VALUE being bound, not the pattern annotation.
    -- Core's pattern annotations (e.g., `loaded integer`) are coarser than CN's types.
    -- CN's check_and_match_pattern uses the actual value's type for binding.
    -- We use coreBaseTypeToCN for the PatternBindings record only, falling back to
    -- the value's type when the pattern annotation is insufficient.
    let cnBt := match coreBaseTypeToCN bt with
      | some t => t
      | none => value.bt  -- Pattern annotation insufficient; use actual value type
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
      -- Tuple patterns - bind each component using nthTuple projections.
      --
      -- Corresponds to: Ctuple case in check_and_match_pattern, check.ml lines 60-75
      -- CN uses Simplify.IndexTerms.tuple_nth_reduce to extract the ith element:
      --   - If value is a concrete Tuple: extract element directly
      --   - Otherwise: create NthTuple(i, value) structural projection
      -- This preserves symbolic value flow through tuple destructuring.
      --
      -- Type handling: Extract element types from the tuple type.
      -- If value.bt is BaseType.tuple elemTypes, use elemTypes[idx] for each element.
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
              | none =>
                TypingM.fail (.other s!"Unsupported Core base type in tuple pattern: {repr bt}")
            | .ctor _ _ =>
              TypingM.fail (.other s!"Cannot determine type for constructor pattern at index {idx} - value is not a proper tuple")

        -- Use nthTuple projection with eager reduction (tuple_nth_reduce)
        -- Corresponds to: Simplify.IndexTerms.tuple_nth_reduce in simplify.ml:174-180
        let projTerm : IndexTerm ← match value.term with
          | .tuple elems =>
            -- Concrete tuple: extract element directly
            -- Corresponds to: Tuple items -> List.nth items n
            -- (OCaml List.nth raises Invalid_argument on out-of-bounds)
            match elems[idx]? with
            | some elem => pure elem
            | none => TypingM.fail (.other s!"Tuple index {idx} out of bounds (tuple has {elems.length} elements)")
          | _ =>
            -- Symbolic/non-concrete: create structural nthTuple projection
            -- Corresponds to: _ -> IT.nthTuple_ ~item_bt (n, it) loc
            pure (AnnotTerm.mk (.nthTuple idx value) projBt value.loc)

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
  -- Corresponds to: PEif in cn/lib/check.ml lines 1034-1056
  -- CN passes path conditions to each branch:
  --   check_pexpr (c :: path_cs) e1     -- then branch gets condition
  --   check_pexpr (not_ c :: path_cs) e2  -- else branch gets negated condition
  -- CN's `provable` wraps checks with: (and path_cs) => constraint
  -- In our post-hoc model, we add path conditions as constraints so that
  -- obligations generated inside branches (e.g., PEundef unreachability)
  -- have the branch condition in their assumptions.
  --
  -- **Lazy muCore**: When the else branch is PEundef, this is a Core IR safety
  -- guard pattern (e.g., PtrValidForDeref → ptr, else undef). CN's muCore
  -- transformation (core_to_mucore.ml) strips these guards entirely — the type
  -- checker never sees PEundef from guards. We match this by skipping the undef
  -- branch and returning only the then-branch result.
  | .if_ cond thenE elseE =>
    let peCond : APexpr := ⟨[], some .boolean, cond⟩
    let peThen : APexpr := ⟨[], pe.ty, thenE⟩
    let peElse : APexpr := ⟨[], pe.ty, elseE⟩
    let tCond ← checkPexpr peCond (some .bool)
    -- Lazy muCore: strip guard patterns where else branch is PEundef.
    -- CN's muCore transformation removes these entirely (core_to_mucore.ml).
    -- The safety is guaranteed by the resource system (Owned<T>(ptr) implies
    -- pointer validity), not by the PtrValidForDeref guard.
    match elseE with
    | .undef _ _ =>
      -- Guard pattern: ite(check, value, undef) → just return value
      -- Corresponds to: core_to_mucore.ml stripping PtrValidForDeref guards
      let tThen ← checkPexpr peThen expectedBt
      return tThen
    | _ =>
    -- Normal conditional (not a guard pattern)
    -- Save constraints before adding path conditions
    let savedConstraints ← TypingM.getConstraints
    -- Check then branch with condition as path constraint
    -- Corresponds to: check_pexpr (c :: path_cs) e1
    TypingM.addC (.t tCond)
    let tThen ← checkPexpr peThen expectedBt
    -- Restore constraints, add negation for else branch
    -- Corresponds to: check_pexpr (not_ c loc :: path_cs) e2
    TypingM.modifyContext (fun ctx => { ctx with constraints := savedConstraints })
    let notCond := AnnotTerm.mk (.unop .not tCond) .bool loc
    TypingM.addC (.t notCond)
    let tElse ← checkPexpr peElse expectedBt
    -- Restore original constraints (path conditions are scoped to branches)
    TypingM.modifyContext (fun ctx => { ctx with constraints := savedConstraints })
    -- Cross-propagate: if types differ and one is more specific, re-check
    let (tThen, tElse) ← match tThen.bt, tElse.bt with
      | .bits _ _, .integer =>
        -- Then has precise bits type, re-check else with that type
        TypingM.addC (.t notCond)
        let tElse' ← checkPexpr peElse (some tThen.bt)
        TypingM.modifyContext (fun ctx => { ctx with constraints := savedConstraints })
        pure (tThen, tElse')
      | .integer, .bits _ _ =>
        -- Else has precise bits type, re-check then with that type
        TypingM.addC (.t tCond)
        let tThen' ← checkPexpr peThen (some tElse.bt)
        TypingM.modifyContext (fun ctx => { ctx with constraints := savedConstraints })
        pure (tThen', tElse)
      | _, _ => pure (tThen, tElse)
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
  -- Corresponds to: check.ml lines 669-692 (PEarray_shift)
  | .arrayShift ptr ty idx =>
    let pePtr : APexpr := ⟨[], some (.object .pointer), ptr⟩
    let peIdx : APexpr := ⟨[], some (.object .integer), idx⟩
    let tPtr ← checkPexpr pePtr
    let tIdx ← checkPexpr peIdx
    -- Cast index to uintptr type (CN invariant: ArrayShift index must be uintptr)
    -- Corresponds to: cast_ Memory.uintptr_bt vt2 loc in check.ml:681
    let uintptrBt : BaseType := .bits .unsigned 64
    let castIdx := match tIdx.bt with
      | .bits .unsigned 64 => tIdx  -- Already uintptr: no-op (matches cast_ identity check)
      | _ => AnnotTerm.mk (.cast uintptrBt tIdx) uintptrBt loc
    return AnnotTerm.mk (.arrayShift tPtr ty castIdx) .loc loc

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
      -- Unwrap loaded type: Specified wraps an object value, so loaded(ot) → object(ot)
      -- Corresponds to: muCore stripping loaded wrapper from Specified values
      match args with
      | [innerArg] =>
        let innerTy := pe.ty.map fun
          | .loaded ot => .object ot
          | other => other
        let peArg : APexpr := ⟨[], innerTy, innerArg⟩
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
      return AnnotTerm.mk (.sym undefSym) unspecBt loc
    | .ivmax =>
      -- ivmax(ctype) - maximum value for integer type
      -- Corresponds to: Civmax in cn/lib/check.ml lines 584-595
      match args with
      | [ctypeArg] =>
        let peArg : APexpr := ⟨[], none, ctypeArg⟩
        let tArg ← checkPexpr peArg
        match tArg.term with
        | .const (.ctypeConst ct) =>
          match ct.ty with
          | .basic (.integer ity) =>
            let maxVal := intTypeMax ity
            -- CN uses Memory.bt_of_sct on the ctype argument to determine result type
            let resBt := integerTypeToBaseType ity
            return numLit maxVal resBt loc
          | _ => TypingM.fail (.other "ivmax requires integer ctype")
        | _ => TypingM.fail (.other "ivmax requires ctype constant argument")
      | _ => TypingM.fail (.other "ivmax requires exactly 1 argument")
    | .ivmin =>
      -- ivmin(ctype) - minimum value for integer type
      -- Corresponds to: Civmin in cn/lib/check.ml lines 584-595
      match args with
      | [ctypeArg] =>
        let peArg : APexpr := ⟨[], none, ctypeArg⟩
        let tArg ← checkPexpr peArg
        match tArg.term with
        | .const (.ctypeConst ct) =>
          match ct.ty with
          | .basic (.integer ity) =>
            let minVal := intTypeMin ity
            -- CN uses Memory.bt_of_sct on the ctype argument to determine result type
            let resBt := integerTypeToBaseType ity
            return numLit minVal resBt loc
          | _ => TypingM.fail (.other "ivmin requires integer ctype")
        | _ => TypingM.fail (.other "ivmin requires ctype constant argument")
      | _ => TypingM.fail (.other "ivmin requires exactly 1 argument")
    | .ivsizeof =>
      -- ivsizeof(ctype) - size of type in bytes
      -- Corresponds to: Civsizeof in cn/lib/check.ml lines 596-613
      match args with
      | [ctypeArg] =>
        let peArg : APexpr := ⟨[], none, ctypeArg⟩
        let tArg ← checkPexpr peArg
        match tArg.term with
        | .const (.ctypeConst ct) =>
          -- CN uses Memory.size_bt = Bits(Unsigned, 64) for sizeof result
          let resBt : BaseType := .bits .unsigned 64
          return AnnotTerm.mk (.sizeOf ct) resBt loc
        | _ => TypingM.fail (.other "ivsizeof requires ctype constant argument")
      | _ => TypingM.fail (.other "ivsizeof requires exactly 1 argument")
    | .ivalignof =>
      -- ivalignof(ctype) - alignment of type in bytes
      -- Corresponds to: Civalignof in cn/lib/check.ml lines 596-613
      match args with
      | [ctypeArg] =>
        let peArg : APexpr := ⟨[], none, ctypeArg⟩
        let tArg ← checkPexpr peArg
        match tArg.term with
        | .const (.ctypeConst ct) =>
          match alignOfCtype ct with
          | some align =>
            -- CN uses Memory.size_bt = Bits(Unsigned, 64) for alignof result
            let resBt : BaseType := .bits .unsigned 64
            return numLit (Int.ofNat align) resBt loc
          | none =>
            TypingM.fail (.other s!"ivalignof: cannot compute alignment for {repr ct.ty} (requires type environment)")
        | _ => TypingM.fail (.other "ivalignof requires ctype constant argument")
      | _ => TypingM.fail (.other "ivalignof requires exactly 1 argument")
    | .ivOR | .ivXOR | .ivAND =>
      -- ivOR/ivXOR/ivAND(ctype, x, y) - bitwise binary operations
      -- Corresponds to: CivAND | CivOR | CivXOR in cn/lib/check.ml lines 638-660
      -- First arg is ctype, used to determine result base type via Memory.bt_of_sct
      match args with
      | [ctypeArg, arg2, arg3] =>
        let peCtypeArg : APexpr := ⟨[], some .ctype, ctypeArg⟩
        let tCtype ← checkPexpr peCtypeArg (some .ctype)
        let ct ← match tCtype.term with
          | .const (.ctypeConst ct) => pure ct
          | _ => TypingM.fail (.other s!"{repr c} requires ctype constant as first argument")
        let resBt := ctypeToBaseTypeBits ct
        let peArg2 : APexpr := ⟨[], pe.ty, arg2⟩
        let peArg3 : APexpr := ⟨[], pe.ty, arg3⟩
        let t2 ← checkPexpr peArg2 (some resBt)
        let t3 ← checkPexpr peArg3 (some resBt)
        let op := match c with
          | .ivOR => BinOp.bwOr
          | .ivXOR => BinOp.bwXor
          | .ivAND => BinOp.bwAnd
          | _ => unreachable!
        return AnnotTerm.mk (.binop op t2 t3) resBt loc
      | _ => TypingM.fail (.other s!"{repr c} requires exactly 3 arguments (ctype, arg1, arg2)")
    | .ivCOMPL =>
      -- ivCOMPL(ctype, x) - bitwise complement
      -- Corresponds to: CivCOMPL in cn/lib/check.ml lines 621-637
      -- First arg is ctype, used to determine result base type via Memory.bt_of_sct
      match args with
      | [ctypeArg, arg2] =>
        let peCtypeArg : APexpr := ⟨[], some .ctype, ctypeArg⟩
        let tCtype ← checkPexpr peCtypeArg (some .ctype)
        let ct ← match tCtype.term with
          | .const (.ctypeConst ct) => pure ct
          | _ => TypingM.fail (.other "ivCOMPL requires ctype constant as first argument")
        let resBt := ctypeToBaseTypeBits ct
        let peArg : APexpr := ⟨[], pe.ty, arg2⟩
        let t ← checkPexpr peArg (some resBt)
        return AnnotTerm.mk (.unop .bwCompl t) resBt loc
      | _ => TypingM.fail (.other "ivCOMPL requires exactly 2 arguments (ctype, arg)")
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
            | _, _ =>
              -- CN asserts expect must be Bits in check_conv_int
              -- If targetBt isn't Bits, this is a type error
              panic! s!"convertToBits called with non-Bits target type: {repr targetBt}"

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

          | .basic (.integer .char) =>
            -- Char: signed 8-bit on most platforms (Cerberus treats as signed)
            -- Treat like signed with representability check
            let reprTerm := AnnotTerm.mk (.representable ct argVal) .bool loc
            TypingM.requireConstraint (.t reprTerm) loc "integer representability"
            return convertToBits argVal

          | .basic (.integer (.enum _)) =>
            -- Enum: typically int-sized (signed 32-bit)
            -- Treat like signed with representability check
            let reprTerm := AnnotTerm.mk (.representable ct argVal) .bool loc
            TypingM.requireConstraint (.t reprTerm) loc "integer representability"
            return convertToBits argVal

          | .basic (.integer .size_t) =>
            -- size_t: unsigned, cast directly
            return convertToBits argVal

          | .basic (.integer .ptrdiff_t) =>
            -- ptrdiff_t: signed, add representability check
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
    -- is_representable_integer: check if value fits in integer type
    -- Corresponds to: is_representable_integer in Core eval
    -- Returns a boolean representability term
    else if fnName == some "is_representable_integer" then
      match args with
      | [valArg, tyArg] =>
        let peVal : APexpr := ⟨[], none, valArg⟩
        let argVal ← checkPexpr peVal
        match tyArg with
        | .val (.ctype ct) =>
          return AnnotTerm.mk (.representable ct argVal) .bool loc
        | _ =>
          TypingM.fail (.other "is_representable_integer: could not extract ctype")
      | _ =>
        TypingM.fail (.other "is_representable_integer requires exactly 2 arguments")
    -- params_length: count elements in a concrete list
    -- Corresponds to: check.ml lines 863-875 (PEcall "params_length")
    -- CN evaluates the list argument and returns its length as an integer.
    else if fnName == some "params_length" then
      match args with
      | [listArg] =>
        let peList : APexpr := ⟨[], none, listArg⟩
        let listVal ← checkPexpr peList
        match destList listVal with
        | some items =>
          return AnnotTerm.mk (.const (.z (Int.ofNat items.length))) .integer loc
        | none => TypingM.fail (.other "params_length: argument is not a concrete list")
      | _ => TypingM.fail (.other "params_length: expected 1 argument")
    -- params_nth: extract nth element from a concrete list
    -- Corresponds to: check.ml lines 876-888 (PEcall "params_nth")
    -- CN evaluates the list and index, then extracts the element.
    else if fnName == some "params_nth" then
      match args with
      | [listArg, idxArg] =>
        let peList : APexpr := ⟨[], none, listArg⟩
        let listVal ← checkPexpr peList
        let peIdx : APexpr := ⟨[], none, idxArg⟩
        let idxVal ← checkPexpr peIdx
        match destList listVal with
        | some items =>
          match idxVal.term with
          | .const (.z n) =>
            let idx := n.toNat
            match items[idx]? with
            | some item => return item
            | none => TypingM.fail (.other s!"params_nth: index {n} out of bounds (list has {items.length} elements)")
          | _ => TypingM.fail (.other "params_nth: index is not a concrete integer")
        | none => TypingM.fail (.other "params_nth: first argument is not a concrete list")
      | _ => TypingM.fail (.other "params_nth: expected 2 arguments")
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
  -- Filter out Unspecified branches (CN muCore strips these).
  -- Then convert remaining branches.
  -- Corresponds to: core_to_mucore.ml stripping of Unspecified branches
  | .case_ scrut branches =>
    let peScrut : APexpr := ⟨[], none, scrut⟩
    let tScrut ← checkPexpr peScrut
    -- Filter branches: remove Unspecified patterns and wildcard catch-alls
    -- This mirrors CN's muCore transformation which strips non-Specified branches
    let branches := filterSpecifiedBranches branches
    -- Convert remaining branches
    let cnBranches ← branches.mapM fun (pat, body) => do
      let bindings ← bindPattern pat tScrut
      let peBody : APexpr := ⟨[], pe.ty, body⟩
      let tBody ← checkPexpr peBody expectedBt
      unbindPattern bindings
      -- Convert APattern to CN Pattern
      let cnPat := convertPattern pat tScrut.bt loc
      return (cnPat, tBody)
    -- Result type comes from the first branch body (CN strips case in muCore,
    -- so there's no PEcase type inference - the branches determine the type)
    let resBt ← match cnBranches.head? with
      | some (_, body) => pure body.bt
      | none => TypingM.fail (.other "case/match expression: no branches after filtering")
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
  -- Corresponds to: PEundef in cn/lib/check.ml lines 1067-1074
  -- CN calls `provable (LC.T (bool_ false))` to check if the path is unreachable:
  --   - If provable (path is dead): return default value
  --   - If not provable (UB is reachable): fail with Undefined_behaviour error
  -- In our post-hoc model, we add an obligation that `false` must hold under
  -- current assumptions. If SMT finds the path is reachable, this obligation
  -- will fail, correctly flagging the UB.
  | .undef _uloc ub =>
    let falseTerm := AnnotTerm.mk (.const (.bool false)) .bool loc
    TypingM.requireConstraint (.t falseTerm) loc s!"undefined behavior ({repr ub}) must be unreachable"
    -- Return a default value (matches CN's `default_ expect loc` for dead paths)
    let resBt ← match expectedBt with
      | some bt => pure bt
      | none => match pe.ty with
        | some (.loaded .integer) | some (.object .integer) =>
          pure .integer
        | _ => requireCoreBaseTypeToCN pe.ty "undef expression"
    return AnnotTerm.mk (.sym undefSym) resBt loc

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
  -- Corresponds to: check_conv_int in cn/lib/check.ml lines 394-431
  -- PEconv_int converts an integer expression to the target IntegerType.
  -- The target type determines the output BaseType (e.g., signed int → bits signed 32).
  | .convInt ty e =>
    let targetBt := integerTypeToBaseType ty
    let pe' : APexpr := ⟨[], pe.ty, e⟩
    let argVal ← checkPexpr pe' (some targetBt)
    -- Cast to target type (matches CN's cast_ which is no-op when types match)
    match targetBt, argVal.term with
    | .bits sign width, .const (.z n) =>
      -- Constant integer: directly create Bits literal
      return AnnotTerm.mk (.const (.bits sign width n)) targetBt argVal.loc
    | .bits _ _, _ =>
      -- Non-constant: wrap in cast (symbolic conversion)
      return AnnotTerm.mk (.cast targetBt argVal) targetBt argVal.loc
    | _, _ =>
      -- Non-Bits target type: pass through
      return argVal

  -- Wrap integer (modular arithmetic)
  -- Corresponds to: PEwrapI in cn/lib/check.ml lines 945-985
  -- CN performs the arithmetic operation; for bitvector types, modular wrapping
  -- is inherent in the bitvec semantics (no explicit wrapI_ wrapper needed).
  | .wrapI ty op e1 e2 =>
    let opBt := integerTypeToBaseType ty
    let pe1 : APexpr := ⟨[], none, e1⟩
    let pe2 : APexpr := ⟨[], none, e2⟩
    let t1 ← checkPexpr pe1 (some opBt)
    let t2 ← checkPexpr pe2 (some t1.bt)
    -- Map Iop to CN BinOp (matches CN's check.ml lines 966-983)
    let cnOp ← match op with
      | .add => pure BinOp.add
      | .sub => pure BinOp.sub
      | .mul => pure BinOp.mul
      | .div => pure BinOp.div
      | .rem_t => pure BinOp.rem
      | .shl => TypingM.fail (.other "shift left (shl) not yet supported in PEwrapI")
      | .shr => TypingM.fail (.other "shift right (shr) not yet supported in PEwrapI")
    return AnnotTerm.mk (.binop cnOp t1 t2) t1.bt loc

  -- Catch exceptional condition (overflow checking)
  -- Corresponds to: PEcatch_exceptional_condition in CN check.ml:986-1033
  -- CN computes at extended precision (2*width + 4 bits) and checks representability.
  -- We generate a verification obligation for the overflow check.
  | .catchExceptionalCondition ty op e1 e2 =>
    let opBt := integerTypeToBaseType ty
    let pe1 : APexpr := ⟨[], none, e1⟩
    let pe2 : APexpr := ⟨[], none, e2⟩
    let t1 ← checkPexpr pe1 (some opBt)
    let t2 ← checkPexpr pe2 (some t1.bt)
    let cnOp ← match op with
      | .add => pure BinOp.add
      | .sub => pure BinOp.sub
      | .mul => pure BinOp.mul
      | .div => pure BinOp.div
      | .rem_t => pure BinOp.rem
      | .shl => TypingM.fail (.other "shift left (shl) not supported in catch_exceptional_condition")
      | .shr => TypingM.fail (.other "shift right (shr) not supported in catch_exceptional_condition")
    -- Direct result at target precision (this is what gets returned to the caller)
    let directResult := AnnotTerm.mk (.binop cnOp t1 t2) opBt loc
    -- Extended-precision overflow check (CN check.ml:1003-1030)
    -- Compute at wider bitvector to detect overflow before modular wrapping
    let (_sign, width) ← match opBt with
      | .bits s w => pure (s, w)
      | _ => TypingM.fail (.other "catchExceptionalCondition: non-Bits operand type")
    let extWidth := 2 * width + 4
    let extBt : BaseType := .bits .signed extWidth
    -- Cast operands to extended precision (CN check.ml:1005: large x = cast_ large_bt x)
    let ext1 := AnnotTerm.mk (.cast extBt t1) extBt loc
    let ext2 := AnnotTerm.mk (.cast extBt t2) extBt loc
    -- Compute at extended precision (won't overflow with 2w+4 bits)
    let extResult := AnnotTerm.mk (.binop cnOp ext1 ext2) extBt loc
    -- Check representability: minInt ≤ extResult ≤ maxInt
    -- CN check.ml:296-306: is_representable_integer
    let minVal := intTypeMin ty
    let maxVal := intTypeMax ty
    let minTerm := AnnotTerm.mk (.const (.bits .signed extWidth minVal)) extBt loc
    let maxTerm := AnnotTerm.mk (.const (.bits .signed extWidth maxVal)) extBt loc
    let lowerBound := AnnotTerm.mk (.binop .le minTerm extResult) .bool loc
    let upperBound := AnnotTerm.mk (.binop .le extResult maxTerm) .bool loc
    let rangeCheck := AnnotTerm.mk (.binop .and_ lowerBound upperBound) .bool loc
    TypingM.requireConstraint (.t rangeCheck) loc "UB036: exceptional condition (overflow)"
    return directResult

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

  -- are_compatible: check if two ctypes are compatible
  -- Corresponds to: check.ml lines 897-901 (PEare_compatible)
  -- CN evaluates both arguments and compares them concretely.
  | .areCompatible e1 e2 =>
    let pe1 : APexpr := ⟨[], none, e1⟩
    let pe2 : APexpr := ⟨[], none, e2⟩
    let v1 ← checkPexpr pe1
    let v2 ← checkPexpr pe2
    match v1.term, v2.term with
    | .const (.ctypeConst ct1), .const (.ctypeConst ct2) =>
      -- Compare by inner type only, ignoring annotations.
      -- Corresponds to: Sctypes.equal in CN which works on annotation-free Sctypes.
      return boolLit (ct1.ty == ct2.ty) loc
    | _, _ =>
      let desc1 := match v1.term with
        | .const c => s!"const({repr c})"
        | .sym s => s!"sym({s.name.getD "?"})"
        | _ => "other"
      let desc2 := match v2.term with
        | .const c => s!"const({repr c})"
        | .sym s => s!"sym({s.name.getD "?"})"
        | _ => "other"
      TypingM.fail (.other s!"are_compatible: arguments are not concrete ctypes: {desc1} vs {desc2}")

  -- C function pointer extraction: returns (return_ctype, [param_ctypes], variadic, has_proto)
  -- Corresponds to: PEcfunction in check.ml lines 922-943
  -- CN looks up function info and returns a concrete 4-tuple.
  | .cfunction e =>
    let pe' : APexpr := ⟨[], none, e⟩
    let ptrVal ← checkPexpr pe'
    let funSym ← match ptrVal.term with
      | .sym s => pure s
      | _ => TypingM.fail (.other "cfunction: argument is not a known function pointer symbol")
    match ← TypingM.lookupFunInfo funSym with
    | some fi =>
      let retCt := AnnotTerm.mk (.const (.ctypeConst fi.returnType)) .ctype loc
      let paramCtypes := fi.params.map fun fp =>
        AnnotTerm.mk (.const (.ctypeConst fp.ty)) .ctype loc
      let paramList := buildConsList .ctype paramCtypes loc
      let variadic := boolLit fi.isVariadic loc
      let hasProto := boolLit fi.hasProto loc
      return AnnotTerm.mk (.tuple [retCt, paramList, variadic, hasProto])
        (.tuple [.ctype, .list .ctype, .bool, .bool]) loc
    | none => TypingM.fail (.other s!"cfunction: no function info for {funSym.name.getD "?"}")

  -- Union constructor
  -- CN does NOT support unions (check.ml:200: error "todo: union types")
  | .union_ _tag _member _value =>
    TypingM.fail (.other "union constructors not supported (CN: check.ml:200)")

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

  -- Constrained values: Core memory model construct, not a CN pure expression.
  -- CN's type checker never sees these directly.
  | .constrained _constraints =>
    TypingM.fail (.other "constrained values not supported in CN verification (Core memory model construct)")

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
    -- Remaining constructors are compile-time operations, not CN pattern constructors
    | .ivmax | .ivmin | .ivsizeof | .ivalignof
    | .ivCOMPL | .ivAND | .ivOR | .ivXOR
    | .fvfromint | .ivfromfloat =>
      panic! s!"ctorToSym: unsupported constructor: {repr c}"

  /-- Get maximum value of integer type.
      Uses 2^(w-1)-1 for signed, 2^w-1 for unsigned. -/
  intTypeMax : CerbLean.Core.IntegerType → Int
    | .char => 127  -- signed 8-bit (Cerberus default)
    | .bool => 1
    | .signed kind => 2 ^ (intBaseKindWidth kind - 1) - 1
    | .unsigned kind => 2 ^ intBaseKindWidth kind - 1
    | .size_t => 2 ^ 64 - 1  -- unsigned 64-bit
    | .ptrdiff_t => 2 ^ 63 - 1  -- signed 64-bit
    | .ptraddr_t => 2 ^ 64 - 1  -- unsigned 64-bit
    | .wchar_t => 2 ^ 31 - 1  -- signed 32-bit (platform-dependent)
    | .wint_t => 2 ^ 31 - 1  -- signed 32-bit
    | .enum _ => 2 ^ 31 - 1  -- enums are typically int-sized (signed 32-bit)

  /-- Get minimum value of integer type.
      Uses -2^(w-1) for signed, 0 for unsigned. -/
  intTypeMin : CerbLean.Core.IntegerType → Int
    | .char => -(2 ^ 7)  -- signed 8-bit (Cerberus default)
    | .bool => 0
    | .signed kind => -(2 ^ (intBaseKindWidth kind - 1))
    | .unsigned _ => 0
    | .size_t => 0  -- unsigned
    | .ptrdiff_t => -(2 ^ 63)  -- signed 64-bit
    | .ptraddr_t => 0  -- unsigned
    | .wchar_t => -(2 ^ 31)  -- signed 32-bit (platform-dependent)
    | .wint_t => -(2 ^ 31)  -- signed 32-bit
    | .enum _ => -(2 ^ 31)  -- enums are typically int-sized (signed 32-bit)

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
