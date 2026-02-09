/-
  CN Name Resolution

  This module resolves identifiers in parsed CN specifications to their
  corresponding symbols with correct unique IDs.

  ## Background

  When CN specs are parsed, identifiers are represented as symbols with
  placeholder ID (0) and the identifier name. Before type checking, we need
  to resolve these names to actual symbols from the context:

  - Parameter names (e.g., `p`, `x`) → parameter symbols with their actual IDs
  - `return` → the fresh return symbol created for this function
  - Resource output names (e.g., `v` in `take v = Owned<int>(p)`) → fresh symbols

  ## Correspondence to CN

  In CN, this is done by `Cabs_to_ail.desugar_cn_*` functions which call
  `resolve_cn_ident` to look up identifiers in the desugaring state.

  | CN                                        | Our Implementation              |
  |-------------------------------------------|----------------------------------|
  | `resolve_cn_ident CN_vars ident`          | `resolveInContext ctx name`      |
  | `register_additional_cn_var`              | Creates fresh symbols for bindings |
  | C desugaring state (parameters)           | `paramContext` parameter         |
  | CN desugaring state (`return` symbol)     | `returnSym` parameter            |

  Audited: 2026-01-27 against cerberus/ocaml_frontend/generated/cabs_to_ail_effect.ml
-/

import CerbLean.CN.Types
import CerbLean.Core
import CerbLean.Core.File

namespace CerbLean.CN.TypeChecking.Resolve

open CerbLean.Core (Sym Loc Ctype Ctype_ TagDefs)
open CerbLean.CN.Types

/-! ## Resolution Context

The context maps identifier names to their resolved symbols.
-/

/-- Context for name resolution.
    Stores both symbol IDs and their types so that resolved AnnotTerms get proper types. -/
structure ResolveContext where
  /-- Map from identifier name to resolved symbol AND its type -/
  nameToSymType : List (String × Sym × BaseType)
  /-- Counter for generating fresh symbol IDs -/
  nextFreshId : Nat
  /-- Map from parameter name to its C type (for pointer arithmetic elaboration).
      Corresponds to: CN's Loc(Some ct) carrying pointee types in BaseTypes.ml.
      Our BaseType.loc doesn't carry the pointee type, so we store it separately. -/
  paramCTypes : List (String × Ctype) := []
  /-- Tag definitions for resolving struct/union tags from parsed specs.
      Corresponds to: CN's Cabs_to_ail resolving struct tag names to Sym.t.
      The CN parser creates struct tags with id=0; we resolve them here. -/
  tagDefs : TagDefs := []
  deriving Inhabited

namespace ResolveContext

/-- Create an empty context -/
def empty : ResolveContext :=
  { nameToSymType := [], nextFreshId := 1000 }  -- Start high to avoid conflicts

/-- Look up a name in the context, returning both symbol and type -/
def lookup (ctx : ResolveContext) (name : String) : Option (Sym × BaseType) :=
  ctx.nameToSymType.find? (fun (n, _, _) => n == name) |>.map (fun (_, s, bt) => (s, bt))

/-- Look up just the symbol (for backwards compatibility) -/
def lookupSym (ctx : ResolveContext) (name : String) : Option Sym :=
  ctx.lookup name |>.map (·.1)

/-- Add a binding with type to the context -/
def add (ctx : ResolveContext) (name : String) (sym : Sym) (bt : BaseType) : ResolveContext :=
  { ctx with nameToSymType := (name, sym, bt) :: ctx.nameToSymType }

/-- Generate a fresh symbol with type and add it to the context -/
def fresh (ctx : ResolveContext) (name : String) (bt : BaseType) : ResolveContext × Sym :=
  let sym : Sym := { id := ctx.nextFreshId, name := some name }
  let ctx' := { ctx with
    nameToSymType := (name, sym, bt) :: ctx.nameToSymType
    nextFreshId := ctx.nextFreshId + 1
  }
  (ctx', sym)

end ResolveContext

/-! ## Struct Tag Resolution

The CN parser creates struct/union tags with placeholder id=0.
CN resolves these during Cabs_to_ail by looking up tag names in the C translation environment.
We do the same here using tagDefs from the Core file.
-/

/-- Resolve a struct tag by looking up its name in tagDefs.
    If the tag has id=0 (unresolved from parser), find the real tag by name.
    If the tag already has a real id, return it unchanged.
    Corresponds to: CN's resolve_cn_ident for struct tags in Cabs_to_ail -/
def resolveTag (tagDefs : TagDefs) (tag : Sym) : Sym :=
  if tag.id != 0 then tag  -- Already resolved
  else
    match tag.name with
    | some name =>
      match tagDefs.find? (fun (s, _) => s.name == some name) with
      | some (realTag, _) => realTag
      | none => panic! s!"resolveTag: struct/union tag '{name}' not found in tagDefs"
    | none => panic! s!"resolveTag: tag symbol has no name (id={tag.id})"

/-- Resolve struct/union tags in a Ctype_ inner type.
    Recursively fixes all struct/union tags with id=0. -/
partial def resolveCtypeInnerTag (tagDefs : TagDefs) : Ctype_ → Ctype_
  | .struct_ tag => .struct_ (resolveTag tagDefs tag)
  | .union_ tag => .union_ (resolveTag tagDefs tag)
  | .pointer q inner => .pointer q (resolveCtypeInnerTag tagDefs inner)
  | .array inner sz => .array (resolveCtypeInnerTag tagDefs inner) sz
  | .atomic inner => .atomic (resolveCtypeInnerTag tagDefs inner)
  | .function rq rt ps v =>
    .function rq (resolveCtypeInnerTag tagDefs rt)
      (ps.map fun (q, t, b) => (q, resolveCtypeInnerTag tagDefs t, b)) v
  | .functionNoParams rq rt => .functionNoParams rq (resolveCtypeInnerTag tagDefs rt)
  | other => other

/-- Resolve struct/union tags in a Ctype. -/
def resolveCtypeTag (tagDefs : TagDefs) (ct : Ctype) : Ctype :=
  { ct with ty := resolveCtypeInnerTag tagDefs ct.ty }

/-- Resolve struct/union tags in a ResourceName.
    Fixes the Ctype inside Owned<T> predicates. -/
def resolveResourceNameTag (tagDefs : TagDefs) (rn : ResourceName) : ResourceName :=
  match rn with
  | .owned ct init => .owned (resolveCtypeTag tagDefs ct) init
  | .pname _ => rn

/-- Resolve struct/union tags in a BaseType. -/
def resolveBaseTypeTag (tagDefs : TagDefs) (bt : BaseType) : BaseType :=
  match bt with
  | .struct_ tag => .struct_ (resolveTag tagDefs tag)
  | other => other

/-! ## Pointer Arithmetic Elaboration

CN's compile.ml (mk_binop, lines 447-463) converts pointer + integer to arrayShift
at elaboration time, before type checking. CN's Loc type carries the pointee Ctype
(`Loc of Sctypes.t option`), but our BaseType.loc does not. We recover the pointee
type from the ResolveContext's paramCTypes or from nested arrayShift terms.
-/

/-- Extract pointee Ctype from a C type (Pointer(T) → some T). -/
def getPointeeCtype (ct : Ctype) : Option Ctype :=
  match ct.ty with
  | .pointer _ pointeeTy => some { ty := pointeeTy }
  | _ => none

/-- Try to determine the pointee Ctype for a resolved pointer-typed AnnotTerm.
    - If it's a symbol reference: look up in paramCTypes, extract pointee
    - If it's an arrayShift: the element type is already known
    Corresponds to: CN's IT.bt returning Loc(Some ct)
-/
def tryGetPointeeCtype (ctx : ResolveContext) (t : AnnotTerm) : Option Ctype :=
  match t with
  | .mk (.sym s) _ _ =>
    -- Look up the symbol's C type from parameter info
    match s.name with
    | some name =>
      ctx.paramCTypes.find? (fun (n, _) => n == name) |>.bind fun (_, ct) =>
        getPointeeCtype ct
    | none => none
  | .mk (.arrayShift _ ct _) _ _ =>
    -- Nested pointer arithmetic: element type is preserved
    some ct
  | _ => none

/-! ## CN Builtin Functions

CN defines MIN/MAX builtins as zero-argument functions returning integer bounds.
Corresponds to: cn/lib/builtins.ml (min_bits_def, max_bits_def, max_min_bits)

These are called as e.g. MINi32(), MAXu8() and return the min/max representable
value for the given type as a Bits constant.
-/

/-- Try to resolve a CN builtin function call.
    Recognizes patterns: MIN/MAX + i/u + 8/16/32/64
    Returns (constant value, base type) if the name matches a builtin.

    Corresponds to: builtins.ml min_bits_def/max_bits_def -/
def resolveBuiltin (name : String) : Option (Const × BaseType) :=
  -- Parse the name: (MIN|MAX)(i|u)(8|16|32|64)
  let pfx := if name.startsWith "MIN" then some false  -- false = min
             else if name.startsWith "MAX" then some true  -- true = max
             else none
  match pfx with
  | none => none
  | some isMax =>
    let rest := name.drop 3  -- drop MIN or MAX
    if rest.length < 2 then none else
    let signChar := rest.get ⟨0⟩
    let widthStr := rest.drop 1
    let sign := if signChar == 'u' then some Sign.unsigned
                else if signChar == 'i' then some Sign.signed
                else none
    match sign with
    | none => none
    | some s =>
      match widthStr.toNat? with
      | none => none
      | some width =>
        if width != 8 && width != 16 && width != 32 && width != 64 then none else
        let bt := BaseType.bits s width
        let value : Int :=
          if isMax then
            match s with
            | .unsigned => (2 ^ width) - 1
            | .signed => (2 ^ (width - 1)) - 1
          else
            match s with
            | .unsigned => 0
            | .signed => -(2 ^ (width - 1))
        some (.bits s width value, bt)

/-! ## Output Type Computation

When processing Owned<T> resources, we need to compute the proper base type for
the output value. CN uses Bits types for integers, which we must match.

Corresponds to: Memory.bt_of_sct in CN's memory.ml
-/

/-- Get bit width for an integer base kind -/
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

/-- Convert the inner C type to CN BaseType for resource outputs.
    Matches CN's Memory.bt_of_sct: integers become Bits, not unbounded Integer.
    This is critical for correctness - CN relies on Bits semantics to constrain values. -/
def ctypeInnerToOutputBaseType : Core.Ctype_ → BaseType
  | .void => .unit
  | .basic (.integer ity) =>
    match ity with
    | .bool => .bool
    | .char => .bits .signed 8  -- Cerberus treats char as signed 8-bit
    | .signed kind => .bits .signed (intBaseKindWidth kind)
    | .unsigned kind => .bits .unsigned (intBaseKindWidth kind)
    | .size_t => .bits .unsigned 64
    | .ptrdiff_t => .bits .signed 64
    | .wchar_t => .bits .signed 32
    | .wint_t => .bits .signed 32
    | .ptraddr_t => .bits .unsigned 64
    | .enum _ => .bits .signed 32
  | .basic (.floating _) => .real
  | .pointer _ _ => .loc
  | .struct_ tag => .struct_ tag
  | .union_ tag => .struct_ tag
  | .array _ _ => .loc
  | .function _ _ _ _ => .loc
  | .functionNoParams _ _ => .loc
  | .atomic ty' => ctypeInnerToOutputBaseType ty'
  | .byte => .memByte

/-- Convert a C type to CN BaseType for resource outputs. -/
def ctypeToOutputBaseType (ct : Core.Ctype) : BaseType :=
  ctypeInnerToOutputBaseType ct.ty

/-- Extract the output base type from a resource request.
    For Owned<T>, returns the proper CN base type for T.
    For user-defined predicates, falls back to the original type. -/
def requestOutputBaseType (req : Request) (fallback : BaseType) : BaseType :=
  match req with
  | .p pred =>
    match pred.name with
    | .owned ct _ => ctypeToOutputBaseType ct
    | .pname _ => fallback  -- User-defined predicates keep their declared type
  | .q qpred =>
    match qpred.name with
    | .owned ct _ => ctypeToOutputBaseType ct
    | .pname _ => fallback

/-! ## Symbol Resolution

Resolve symbols in terms by looking them up in the context.
Unresolved symbols (ID = 0) are looked up by name.
Already-resolved symbols (ID ≠ 0) are left unchanged.
-/

/-- Check if a symbol needs resolution (has placeholder ID 0) -/
def needsResolution (s : Sym) : Bool :=
  s.id == 0

/-- Resolve a symbol using the context.
    Returns the resolved symbol AND its type, or none if not found.

    Note: Symbols created by `fresh()` have non-zero IDs but ARE in the context
    with their types. We must look them up to preserve type information. -/
def resolveSymWithType (ctx : ResolveContext) (s : Sym) : Option (Sym × BaseType) :=
  if needsResolution s then
    -- Placeholder symbol (ID = 0): resolve by name and get new ID + type
    match s.name with
    | some name =>
      match ctx.lookup name with
      | some (resolved, bt) => some (resolved, bt)
      | none => none  -- Not found
    | none => none  -- No name
  else
    -- Already has ID: still look up by name to get type (fresh symbols need this)
    match s.name with
    | some name =>
      match ctx.lookup name with
      | some (_, bt) => some (s, bt)  -- Keep symbol ID, use type from context
      | none => none  -- Not in context
    | none => none  -- No name

/-- Resolve a symbol using the context (symbol only).
    Returns none if the symbol cannot be resolved. -/
def resolveSym (ctx : ResolveContext) (s : Sym) : Option Sym :=
  (resolveSymWithType ctx s).map (·.1)

/-! ## Default Integer Type Selection

When CN infers a literal without an expected type, it picks the smallest Bits type
that can represent the value. This matches CN's `pick_integer_encoding_type` in
wellTyped.ml.

Priority order: Signed32 → Unsigned64 → Signed64 → Unsigned128 → Signed128
-/

/-- Check if an integer fits in a Bits type with given sign and width -/
def fitsInBits (sign : Sign) (width : Nat) (n : Int) : Bool :=
  match sign with
  | .signed =>
    let minVal : Int := -(2 ^ (width - 1))
    let maxVal : Int := 2 ^ (width - 1) - 1
    n >= minVal && n <= maxVal
  | .unsigned =>
    let maxVal : Int := 2 ^ width - 1
    n >= 0 && n <= maxVal

/-- Pick the smallest Bits type that fits the integer value.
    Matches CN's BT.pick_integer_encoding_type in baseTypes.ml.
    Priority: Signed32 → Unsigned64 → Signed64 → Unsigned128 → Signed128

    Returns none if no standard type fits - in CN, this triggers a type error.
    CN's WBT.pick_integer_encoding_type in wellTyped.ml calls this and fails on None.

    Corresponds to: BT.pick_integer_encoding_type in cn/lib/baseTypes.ml -/
def pickIntegerEncodingType (n : Int) : Option BaseType :=
  if fitsInBits .signed 32 n then some (.bits .signed 32)
  else if fitsInBits .unsigned 64 n then some (.bits .unsigned 64)
  else if fitsInBits .signed 64 n then some (.bits .signed 64)
  else if fitsInBits .unsigned 128 n then some (.bits .unsigned 128)
  else if fitsInBits .signed 128 n then some (.bits .signed 128)
  else none  -- CN fails here; callers in TypingM should fail too

/-! ## Term Resolution

Walk the term structure and resolve all symbols.
Uses bidirectional type checking: infer mode (no expected type) vs check mode (with expected type).

Corresponds to: CN's `infer_pexpr` and `check_pexpr` in wellTyped.ml.
For binary operations: infer left operand, check right operand against left's type.
-/

/-- Error type for resolution failures -/
inductive ResolveError where
  | symbolNotFound (name : String)
  | integerTooLarge (n : Int)
  /-- Pointer arithmetic on expression with unknown pointee type.
      Corresponds to: CN's Loc(None) case which would also fail. -/
  | unknownPointeeType (context : String)
  /-- General error for type checking failures during resolution -/
  | other (msg : String)
  deriving Repr, Inhabited

abbrev ResolveResult α := Except ResolveError α

mutual

/-- Resolve symbols in a term, threading expected type for literals.
    Uses CN's bidirectional type checking approach. -/
partial def resolveTerm (ctx : ResolveContext) (t : Term)
    (expectedBt : Option BaseType := none) : ResolveResult Term := do
  match t with
  | .const c =>
    -- Handle integer constants based on mode (CN's num_lit_ + pick_integer_encoding_type)
    match c, expectedBt with
    | .z n, some (.bits sign width) =>
      -- CHECK mode with Bits expected
      return .const (.bits sign width n)
    | .z n, none =>
      -- INFER mode: pick smallest fitting Bits type
      match pickIntegerEncodingType n with
      | some (.bits sign width) => return .const (.bits sign width n)
      | _ => throw (.integerTooLarge n)  -- CN fails here
    | .z n, some bt => throw (.other s!"integer literal {n} with non-Bits expected type {repr bt}")
    | _, _ => return .const c  -- Non-integer constants (bool, unit, ctype, null) pass through unchanged
  | .sym s =>
    match resolveSym ctx s with
    | some resolved => return .sym resolved
    | none => throw (.symbolNotFound (s.name.getD "?"))
  | .unop op arg =>
    return .unop op (← resolveAnnotTerm ctx arg expectedBt)
  | .binop op l r =>
    -- CN's algorithm: INFER left, CHECK right against left's type
    let l' ← resolveAnnotTerm ctx l none
    let r' ← resolveAnnotTerm ctx r (some l'.bt)
    return .binop op l' r'
  | .ite c t e =>
    -- Condition expects bool, branches expect the overall expected type
    return .ite (← resolveAnnotTerm ctx c (some .bool))
               (← resolveAnnotTerm ctx t expectedBt)
               (← resolveAnnotTerm ctx e expectedBt)
  | .eachI lo v hi body => return .eachI lo v hi (← resolveAnnotTerm ctx body expectedBt)
  | .tuple elems =>
    let elems' ← elems.mapM (resolveAnnotTerm ctx · none)
    return .tuple elems'
  | .nthTuple n tup => return .nthTuple n (← resolveAnnotTerm ctx tup none)
  | .struct_ tag members =>
    let members' ← members.mapM fun (id, t) => do return (id, ← resolveAnnotTerm ctx t none)
    return .struct_ (resolveTag ctx.tagDefs tag) members'
  | .structMember obj member => return .structMember (← resolveAnnotTerm ctx obj none) member
  | .structUpdate obj member value => return .structUpdate (← resolveAnnotTerm ctx obj none) member (← resolveAnnotTerm ctx value none)
  | .record members =>
    let members' ← members.mapM fun (id, t) => do return (id, ← resolveAnnotTerm ctx t none)
    return .record members'
  | .recordMember obj member => return .recordMember (← resolveAnnotTerm ctx obj none) member
  | .recordUpdate obj member value => return .recordUpdate (← resolveAnnotTerm ctx obj none) member (← resolveAnnotTerm ctx value none)
  | .constructor constr args =>
    let args' ← args.mapM fun (id, t) => do return (id, ← resolveAnnotTerm ctx t none)
    return .constructor constr args'
  | .memberShift ptr tag member => return .memberShift (← resolveAnnotTerm ctx ptr none) (resolveTag ctx.tagDefs tag) member
  | .arrayShift base ct idx => return .arrayShift (← resolveAnnotTerm ctx base none) ct (← resolveAnnotTerm ctx idx none)
  | .copyAllocId addr loc => return .copyAllocId (← resolveAnnotTerm ctx addr none) (← resolveAnnotTerm ctx loc none)
  | .hasAllocId ptr => return .hasAllocId (← resolveAnnotTerm ctx ptr none)
  | .sizeOf ct => return .sizeOf ct
  | .offsetOf tag member => return .offsetOf tag member
  | .nil bt => return .nil bt
  | .cons head tail => return .cons (← resolveAnnotTerm ctx head none) (← resolveAnnotTerm ctx tail none)
  | .head list => return .head (← resolveAnnotTerm ctx list none)
  | .tail list => return .tail (← resolveAnnotTerm ctx list none)
  | .representable ct value => return .representable ct (← resolveAnnotTerm ctx value none)
  | .good ct value => return .good ct (← resolveAnnotTerm ctx value none)
  | .aligned ptr align => return .aligned (← resolveAnnotTerm ctx ptr none) (← resolveAnnotTerm ctx align none)
  | .wrapI intTy value => return .wrapI intTy (← resolveAnnotTerm ctx value none)
  | .mapConst keyTy value => return .mapConst keyTy (← resolveAnnotTerm ctx value none)
  | .mapSet m k v => return .mapSet (← resolveAnnotTerm ctx m none) (← resolveAnnotTerm ctx k none) (← resolveAnnotTerm ctx v none)
  | .mapGet m k => return .mapGet (← resolveAnnotTerm ctx m none) (← resolveAnnotTerm ctx k none)
  | .mapDef var body => return .mapDef var (← resolveAnnotTerm ctx body none)
  | .apply fn args =>
    match resolveSym ctx fn with
    | some resolved =>
      let args' ← args.mapM (resolveAnnotTerm ctx · none)
      return .apply resolved args'
    | none => throw (.symbolNotFound (fn.name.getD "?"))
  | .let_ var binding body => return .let_ var (← resolveAnnotTerm ctx binding none) (← resolveAnnotTerm ctx body expectedBt)
  | .match_ scrutinee cases =>
    let scrut' ← resolveAnnotTerm ctx scrutinee none
    let cases' ← cases.mapM fun (p, t) => do return (p, ← resolveAnnotTerm ctx t expectedBt)
    return .match_ scrut' cases'
  | .cast targetTy value => return .cast targetTy (← resolveAnnotTerm ctx value none)
  | .cnNone bt => return .cnNone bt
  | .cnSome value => return .cnSome (← resolveAnnotTerm ctx value none)
  | .isSome opt => return .isSome (← resolveAnnotTerm ctx opt none)
  | .getOpt opt => return .getOpt (← resolveAnnotTerm ctx opt none)

/-- Resolve symbols in an annotated term, threading expected type.
    For symbol terms, looks up the type from context.
    For binops, threads left operand type to right operand.
    For integer constants with expected Bits type, creates Bits literals.

    Corresponds to: CN's type threading via Pexpr.expect field. -/
partial def resolveAnnotTerm (ctx : ResolveContext) (at_ : AnnotTerm)
    (expectedBt : Option BaseType := none) : ResolveResult AnnotTerm := do
  match at_ with
  | .mk (.sym s) _bt loc =>
    -- For symbols, look up the type from context
    match resolveSymWithType ctx s with
    | some (resolvedSym, resolvedBt) =>
      return .mk (.sym resolvedSym) resolvedBt loc
    | none =>
      throw (.symbolNotFound (s.name.getD "?"))
  | .mk (.const (.bits sign width n)) _bt loc =>
    -- Typed literal (e.g. 42i32, 0u8): type is already known
    return .mk (.const (.bits sign width n)) (.bits sign width) loc
  | .mk (.const (.z n)) _bt loc =>
    -- For integer constants, handle based on mode:
    -- CHECK mode (expectedBt = some): use expected type if it's Bits
    -- INFER mode (expectedBt = none): use pickIntegerEncodingType to pick default Bits type
    -- Corresponds to: CN's num_lit_ (indexTerms.ml:478) and pick_integer_encoding_type (wellTyped.ml)
    match expectedBt with
    | some (.bits sign width) =>
      -- CHECK mode with Bits expected: use expected type
      return .mk (.const (.bits sign width n)) (.bits sign width) loc
    | some _ =>
      -- CHECK mode with non-Bits expected: keep as unbounded Integer
      return .mk (.const (.z n)) .integer loc
    | none =>
      -- INFER mode: pick smallest fitting Bits type (CN's default behavior)
      match pickIntegerEncodingType n with
      | some (.bits sign width) => return .mk (.const (.bits sign width n)) (.bits sign width) loc
      | _ => throw (.integerTooLarge n)  -- CN fails here
  | .mk (.binop op l r) _bt loc =>
    -- For binops, use CN's exact algorithm (wellTyped.ml:1643-1650):
    -- 1. INFER left operand (no expected type)
    -- 2. CHECK right operand against left's inferred type
    -- This is asymmetric and matches CN exactly.
    let l' ← resolveAnnotTerm ctx l none  -- INFER left
    let r' ← resolveAnnotTerm ctx r (some l'.bt)  -- CHECK right against left's type
    -- Pointer arithmetic elaboration (CN's compile.ml:447-463, mk_binop):
    -- When left operand is a pointer and op is add/sub, convert to arrayShift.
    -- CN does this because Loc carries the pointee type (Loc of Sctypes.t option).
    -- We recover it from paramCTypes or nested arrayShift terms.
    match op, l'.bt with
    | .add, .loc =>
      match tryGetPointeeCtype ctx l' with
      | some ct =>
        -- Cast index to uintptr type (CN invariant: arrayShift index must be uintptr)
        -- Corresponds to: cast_ Memory.uintptr_bt vt2 loc in check.ml:681
        let uintptrBt : BaseType := .bits .unsigned 64
        let castIdx := match r'.bt with
          | .bits .unsigned 64 => r'  -- Already uintptr: no-op
          | _ => AnnotTerm.mk (.cast uintptrBt r') uintptrBt loc
        return .mk (.arrayShift l' ct castIdx) .loc loc
      | none =>
        throw (.unknownPointeeType "pointer + integer: cannot determine element type")
    | .sub, .loc =>
      match tryGetPointeeCtype ctx l' with
      | some ct =>
        -- ptr - int: arrayShift with negated index
        -- Corresponds to: compile.ml sub_ (int_lit_ 0) idx
        let uintptrBt : BaseType := .bits .unsigned 64
        let castIdx := match r'.bt with
          | .bits .unsigned 64 => r'
          | _ => AnnotTerm.mk (.cast uintptrBt r') uintptrBt loc
        let zeroLit := AnnotTerm.mk (.const (.bits .unsigned 64 0)) uintptrBt loc
        let negIdx := AnnotTerm.mk (.binop .sub zeroLit castIdx) uintptrBt loc
        return .mk (.arrayShift l' ct negIdx) .loc loc
      | none =>
        throw (.unknownPointeeType "pointer - integer: cannot determine element type")
    | _, _ =>
      -- Normal (non-pointer) binary operation
      let resultBt := match op with
        | .eq | .lt | .le | .and_ | .or_ | .implies => .bool
        | _ => l'.bt  -- Arithmetic ops: result type matches left operand
      return .mk (.binop op l' r') resultBt loc
  | .mk (.unop op arg) _bt loc =>
    -- For unary ops, thread expected type to operand
    let arg' ← resolveAnnotTerm ctx arg expectedBt
    return .mk (.unop op arg') arg'.bt loc
  | .mk (.ite c t e) _bt loc =>
    -- Condition expects bool, branches expect the overall expected type
    let c' ← resolveAnnotTerm ctx c (some .bool)
    let t' ← resolveAnnotTerm ctx t expectedBt
    let e' ← resolveAnnotTerm ctx e expectedBt
    -- Result type comes from branches (should match)
    return .mk (.ite c' t' e') t'.bt loc
  | .mk (.cast targetBt value) _bt loc =>
    -- Cast: result type is the target base type
    let value' ← resolveAnnotTerm ctx value none
    return .mk (.cast targetBt value') targetBt loc
  | .mk (.apply fn args) _bt loc =>
    -- Check for builtin functions first (e.g. MINi32(), MAXu8())
    -- Corresponds to: CN's builtins.ml - zero-arg functions returning constants
    match fn.name, args with
    | some name, [] =>
      match resolveBuiltin name with
      | some (constVal, bt) => return .mk (.const constVal) bt loc
      | none =>
        match resolveSym ctx fn with
        | some resolved => return .mk (.apply resolved []) _bt loc
        | none => throw (.symbolNotFound name)
    | _, _ =>
      -- Non-builtin function call: resolve symbol and args normally
      match resolveSym ctx fn with
      | some resolved =>
        let args' ← args.mapM (resolveAnnotTerm ctx · none)
        return .mk (.apply resolved args') _bt loc
      | none => throw (.symbolNotFound (fn.name.getD "?"))
  | .mk (.structMember obj member) _bt loc =>
    -- CN wellTyped.ml:695-706: infer obj type, extract struct tag, look up field type
    let obj' ← resolveAnnotTerm ctx obj none
    let fieldBt ← match obj'.bt with
      | .struct_ tag =>
        match ctx.tagDefs.find? fun (t, _) => t.name == tag.name && t.id == tag.id with
        | some (_, (_, .struct_ fields _)) =>
          match fields.find? fun f => f.name == member with
          | some field => pure (ctypeToOutputBaseType field.ty)
          | none => throw (.other s!"struct {tag.name.getD "?"} has no field '{member.name}'")
        | some (_, (_, .union_ _)) =>
          throw (.other s!"structMember on union tag {tag.name.getD "?"}: unions not supported")
        | none => throw (.other s!"struct tag {tag.name.getD "?"} not found in tagDefs")
      | bt => throw (.other s!"structMember on non-struct type: {repr bt}")
    return .mk (.structMember obj' member) fieldBt loc
  | .mk t bt loc =>
    -- For other terms, resolve recursively with expected type, preserve original type
    let t' ← resolveTerm ctx t expectedBt
    return .mk t' (resolveBaseTypeTag ctx.tagDefs bt) loc

end

/-! ## Resource Resolution -/

/-- Resolve symbols in a Predicate.
    Also resolves struct/union tags in the resource name (Owned<struct T> → proper tag ID).
    Corresponds to: CN's Cabs_to_ail resolving struct names in resource types -/
def resolvePredicate (ctx : ResolveContext) (p : Predicate) : ResolveResult Predicate := do
  let pointer' ← resolveAnnotTerm ctx p.pointer
  let iargs' ← p.iargs.mapM (resolveAnnotTerm ctx)
  let name' := resolveResourceNameTag ctx.tagDefs p.name
  return { p with name := name', pointer := pointer', iargs := iargs' }

/-- Resolve symbols in a QPredicate.
    Also resolves struct/union tags in the resource name. -/
def resolveQPredicate (ctx : ResolveContext) (qp : QPredicate) : ResolveResult QPredicate := do
  let pointer' ← resolveAnnotTerm ctx qp.pointer
  let permission' ← resolveAnnotTerm ctx qp.permission
  let iargs' ← qp.iargs.mapM (resolveAnnotTerm ctx)
  let name' := resolveResourceNameTag ctx.tagDefs qp.name
  return { qp with name := name', pointer := pointer', permission := permission', iargs := iargs' }

/-- Resolve symbols in a Request -/
def resolveRequest (ctx : ResolveContext) (req : Request) : ResolveResult Request := do
  match req with
  | .p pred => return .p (← resolvePredicate ctx pred)
  | .q qpred => return .q (← resolveQPredicate ctx qpred)

/-- Resolve symbols in an Output -/
def resolveOutput (ctx : ResolveContext) (out : Output) : ResolveResult Output := do
  let value' ← resolveAnnotTerm ctx out.value
  return { out with value := value' }

/-- Resolve symbols in a resource -/
def resolveResource (ctx : ResolveContext) (r : Resource) : ResolveResult Resource := do
  let request' ← resolveRequest ctx r.request
  let output' ← resolveOutput ctx r.output
  return { r with request := request', output := output' }

/-! ## Clause Resolution

When resolving clauses, we also need to handle bindings.
`take v = Owned<int>(p)` introduces a new binding `v`.
-/

/-- Resolve a clause, returning updated context (for new bindings) and resolved clause -/
def resolveClause (ctx : ResolveContext) (c : Clause) : ResolveResult (ResolveContext × Clause) := do
  match c with
  | .resource name r =>
    -- Resource clause introduces a new binding
    -- First resolve the request to determine the output type
    let resolvedRequest ← resolveRequest ctx r.request

    -- Compute the proper output base type from the resource
    -- For Owned<T>, this gives the CN base type of T (using Bits for integers)
    -- This matches CN's Memory.bt_of_sct behavior
    let outputBt := requestOutputBaseType resolvedRequest r.output.value.bt

    -- Create fresh symbol WITH the correct type
    let (ctx', freshSym) := ctx.fresh (name.name.getD "anon") outputBt

    -- Create the resource with the fresh symbol as its output value
    -- This ensures the output.value matches the binding symbol
    let resolvedResource : Resource := {
      request := resolvedRequest
      output := { value := AnnotTerm.mk (.sym freshSym) outputBt r.output.value.loc }
    }
    return (ctx', .resource freshSym resolvedResource)
  | .constraint assertion =>
    -- Constraint uses current context, doesn't add bindings
    let assertion' ← resolveAnnotTerm ctx assertion
    return (ctx, .constraint assertion')
  | .letBinding name value =>
    -- Let binding resolves the expression, then adds a new binding to context
    let value' ← resolveAnnotTerm ctx value
    let (ctx', freshSym) := ctx.fresh (name.name.getD "anon") value'.bt
    return (ctx', .letBinding freshSym value')

/-- Resolve all clauses in order, threading context through -/
def resolveClauses (ctx : ResolveContext) (clauses : List Clause) : ResolveResult (ResolveContext × List Clause) := do
  let mut ctx' := ctx
  let mut resolved : List Clause := []
  for clause in clauses do
    let (newCtx, resolvedClause) ← resolveClause ctx' clause
    ctx' := newCtx
    resolved := resolved ++ [resolvedClause]
  return (ctx', resolved)

/-! ## Spec Resolution -/

/-- Resolve a precondition -/
def resolvePrecondition (ctx : ResolveContext) (pre : Precondition) : ResolveResult (ResolveContext × Precondition) := do
  let (ctx', clauses) ← resolveClauses ctx pre.clauses
  return (ctx', { clauses := clauses })

/-- Resolve a postcondition -/
def resolvePostcondition (ctx : ResolveContext) (post : Postcondition) : ResolveResult (ResolveContext × Postcondition) := do
  let (ctx', clauses) ← resolveClauses ctx post.clauses
  return (ctx', { clauses := clauses })

/-- Resolve a complete function specification.

    Takes:
    - The parsed spec (with placeholder symbols)
    - Parameter symbols from the function signature (with their CN types)
    - Return type for the function

    Creates a fresh return symbol and resolves all identifiers.

    Returns error if any symbol is not found or integer is too large.

    Corresponds to: CN's desugaring of function specs in core_to_mucore.ml -/
def resolveFunctionSpec
    (spec : FunctionSpec)
    (params : List (Sym × BaseType))
    (returnType : BaseType := .unit)
    (nextFreshId : Nat := 1000)
    (paramCTypes : List (String × Ctype) := [])
    (tagDefs : TagDefs := [])
    : ResolveResult FunctionSpec := do
  -- Build initial context with parameters INCLUDING TYPES
  let paramCtx : ResolveContext := {
    nameToSymType := params.filterMap fun (sym, bt) =>
      sym.name.map fun name => (name, sym, bt)
    nextFreshId := nextFreshId
    paramCTypes := paramCTypes
    tagDefs := tagDefs
  }

  -- Create fresh return symbol with return type and add to context
  let (ctxWithReturn, returnSym) := paramCtx.fresh "return" returnType

  -- Resolve precondition (bindings from requires are visible in ensures)
  let (ctxAfterPre, resolvedPre) ← resolvePrecondition ctxWithReturn spec.requires

  -- Resolve postcondition (can see precondition bindings + return)
  let (_, resolvedPost) ← resolvePostcondition ctxAfterPre spec.ensures

  return { returnSym := returnSym
           requires := resolvedPre
           ensures := resolvedPost
           trusted := spec.trusted
         }

end CerbLean.CN.TypeChecking.Resolve
