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

namespace CerbLean.CN.TypeChecking.Resolve

open CerbLean.Core (Sym Loc)
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
    | .char => .integer  -- char signedness is implementation-defined
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
    Returns the resolved symbol AND its type.
    If not found, returns the original symbol with unit type (error case).

    Note: Symbols created by `fresh()` have non-zero IDs but ARE in the context
    with their types. We must look them up to preserve type information. -/
def resolveSymWithType (ctx : ResolveContext) (s : Sym) : Sym × BaseType :=
  if needsResolution s then
    -- Placeholder symbol (ID = 0): resolve by name and get new ID + type
    match s.name with
    | some name =>
      match ctx.lookup name with
      | some (resolved, bt) => (resolved, bt)
      | none => (s, .unit)  -- Not found - keep original with unit type
    | none => (s, .unit)  -- No name - keep original
  else
    -- Already has ID: still look up by name to get type (fresh symbols need this)
    match s.name with
    | some name =>
      match ctx.lookup name with
      | some (_, bt) => (s, bt)  -- Keep symbol ID, use type from context
      | none => (s, .unit)  -- Not in context - use unit type
    | none => (s, .unit)  -- No name - use unit type

/-- Resolve a symbol using the context (symbol only, for backwards compat). -/
def resolveSym (ctx : ResolveContext) (s : Sym) : Sym :=
  (resolveSymWithType ctx s).1

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

mutual

/-- Resolve symbols in a term, threading expected type for literals.
    Uses CN's bidirectional type checking approach. -/
partial def resolveTerm (ctx : ResolveContext) (t : Term)
    (expectedBt : Option BaseType := none) : Term :=
  match t with
  | .const c =>
    -- Handle integer constants based on mode (CN's num_lit_ + pick_integer_encoding_type)
    match c, expectedBt with
    | .z n, some (.bits sign width) =>
      -- CHECK mode with Bits expected
      .const (.bits sign width n)
    | .z n, none =>
      -- INFER mode: pick smallest fitting Bits type
      match pickIntegerEncodingType n with
      | some (.bits sign width) => .const (.bits sign width n)
      | _ => .const c  -- Fallback for huge numbers (CN would fail here)
    | _, _ => .const c
  | .sym s => .sym (resolveSym ctx s)
  | .unop op arg => .unop op (resolveAnnotTerm ctx arg expectedBt)
  | .binop op l r =>
    -- CN's algorithm: INFER left, CHECK right against left's type
    let l' := resolveAnnotTerm ctx l none
    let r' := resolveAnnotTerm ctx r (some l'.bt)
    .binop op l' r'
  | .ite c t e =>
    -- Condition expects bool, branches expect the overall expected type
    .ite (resolveAnnotTerm ctx c (some .bool))
         (resolveAnnotTerm ctx t expectedBt)
         (resolveAnnotTerm ctx e expectedBt)
  | .eachI lo v hi body => .eachI lo v hi (resolveAnnotTerm ctx body expectedBt)
  | .tuple elems => .tuple (elems.map (resolveAnnotTerm ctx · none))
  | .nthTuple n tup => .nthTuple n (resolveAnnotTerm ctx tup none)
  | .struct_ tag members => .struct_ tag (members.map fun (id, t) => (id, resolveAnnotTerm ctx t none))
  | .structMember obj member => .structMember (resolveAnnotTerm ctx obj none) member
  | .structUpdate obj member value => .structUpdate (resolveAnnotTerm ctx obj none) member (resolveAnnotTerm ctx value none)
  | .record members => .record (members.map fun (id, t) => (id, resolveAnnotTerm ctx t none))
  | .recordMember obj member => .recordMember (resolveAnnotTerm ctx obj none) member
  | .recordUpdate obj member value => .recordUpdate (resolveAnnotTerm ctx obj none) member (resolveAnnotTerm ctx value none)
  | .constructor constr args => .constructor constr (args.map fun (id, t) => (id, resolveAnnotTerm ctx t none))
  | .memberShift ptr tag member => .memberShift (resolveAnnotTerm ctx ptr none) tag member
  | .arrayShift base ct idx => .arrayShift (resolveAnnotTerm ctx base none) ct (resolveAnnotTerm ctx idx none)
  | .copyAllocId addr loc => .copyAllocId (resolveAnnotTerm ctx addr none) (resolveAnnotTerm ctx loc none)
  | .hasAllocId ptr => .hasAllocId (resolveAnnotTerm ctx ptr none)
  | .sizeOf ct => .sizeOf ct
  | .offsetOf tag member => .offsetOf tag member
  | .nil bt => .nil bt
  | .cons head tail => .cons (resolveAnnotTerm ctx head none) (resolveAnnotTerm ctx tail none)
  | .head list => .head (resolveAnnotTerm ctx list none)
  | .tail list => .tail (resolveAnnotTerm ctx list none)
  | .representable ct value => .representable ct (resolveAnnotTerm ctx value none)
  | .good ct value => .good ct (resolveAnnotTerm ctx value none)
  | .aligned ptr align => .aligned (resolveAnnotTerm ctx ptr none) (resolveAnnotTerm ctx align none)
  | .wrapI intTy value => .wrapI intTy (resolveAnnotTerm ctx value none)
  | .mapConst keyTy value => .mapConst keyTy (resolveAnnotTerm ctx value none)
  | .mapSet m k v => .mapSet (resolveAnnotTerm ctx m none) (resolveAnnotTerm ctx k none) (resolveAnnotTerm ctx v none)
  | .mapGet m k => .mapGet (resolveAnnotTerm ctx m none) (resolveAnnotTerm ctx k none)
  | .mapDef var body => .mapDef var (resolveAnnotTerm ctx body none)
  | .apply fn args => .apply (resolveSym ctx fn) (args.map (resolveAnnotTerm ctx · none))
  | .let_ var binding body => .let_ var (resolveAnnotTerm ctx binding none) (resolveAnnotTerm ctx body expectedBt)
  | .match_ scrutinee cases => .match_ (resolveAnnotTerm ctx scrutinee none) (cases.map fun (p, t) => (p, resolveAnnotTerm ctx t expectedBt))
  | .cast targetTy value => .cast targetTy (resolveAnnotTerm ctx value none)
  | .cnNone bt => .cnNone bt
  | .cnSome value => .cnSome (resolveAnnotTerm ctx value none)
  | .isSome opt => .isSome (resolveAnnotTerm ctx opt none)
  | .getOpt opt => .getOpt (resolveAnnotTerm ctx opt none)

/-- Resolve symbols in an annotated term, threading expected type.
    For symbol terms, looks up the type from context.
    For binops, threads left operand type to right operand.
    For integer constants with expected Bits type, creates Bits literals.

    Corresponds to: CN's type threading via Pexpr.expect field. -/
partial def resolveAnnotTerm (ctx : ResolveContext) (at_ : AnnotTerm)
    (expectedBt : Option BaseType := none) : AnnotTerm :=
  match at_ with
  | .mk (.sym s) _bt loc =>
    -- For symbols, look up the type from context
    let (resolvedSym, resolvedBt) := resolveSymWithType ctx s
    .mk (.sym resolvedSym) resolvedBt loc
  | .mk (.const (.z n)) _bt loc =>
    -- For integer constants, handle based on mode:
    -- CHECK mode (expectedBt = some): use expected type if it's Bits
    -- INFER mode (expectedBt = none): use pickIntegerEncodingType to pick default Bits type
    -- Corresponds to: CN's num_lit_ (indexTerms.ml:478) and pick_integer_encoding_type (wellTyped.ml)
    match expectedBt with
    | some (.bits sign width) =>
      -- CHECK mode with Bits expected: use expected type
      .mk (.const (.bits sign width n)) (.bits sign width) loc
    | some _ =>
      -- CHECK mode with non-Bits expected: keep as unbounded Integer
      .mk (.const (.z n)) .integer loc
    | none =>
      -- INFER mode: pick smallest fitting Bits type (CN's default behavior)
      match pickIntegerEncodingType n with
      | some (.bits sign width) => .mk (.const (.bits sign width n)) (.bits sign width) loc
      | _ => .mk (.const (.z n)) .integer loc  -- Fallback for huge numbers (CN would fail)
  | .mk (.binop op l r) _bt loc =>
    -- For binops, use CN's exact algorithm (wellTyped.ml:1643-1650):
    -- 1. INFER left operand (no expected type)
    -- 2. CHECK right operand against left's inferred type
    -- This is asymmetric and matches CN exactly.
    let l' := resolveAnnotTerm ctx l none  -- INFER left
    let r' := resolveAnnotTerm ctx r (some l'.bt)  -- CHECK right against left's type
    -- Compute result type from operator
    let resultBt := match op with
      | .eq | .lt | .le | .and_ | .or_ | .implies => .bool
      | _ => l'.bt  -- Arithmetic ops: result type matches left operand
    .mk (.binop op l' r') resultBt loc
  | .mk (.unop op arg) _bt loc =>
    -- For unary ops, thread expected type to operand
    let arg' := resolveAnnotTerm ctx arg expectedBt
    .mk (.unop op arg') arg'.bt loc
  | .mk (.ite c t e) _bt loc =>
    -- Condition expects bool, branches expect the overall expected type
    let c' := resolveAnnotTerm ctx c (some .bool)
    let t' := resolveAnnotTerm ctx t expectedBt
    let e' := resolveAnnotTerm ctx e expectedBt
    -- Result type comes from branches (should match)
    .mk (.ite c' t' e') t'.bt loc
  | .mk t bt loc =>
    -- For other terms, resolve recursively with expected type, preserve original type
    .mk (resolveTerm ctx t expectedBt) bt loc

end

/-! ## Resource Resolution -/

/-- Resolve symbols in a Predicate -/
def resolvePredicate (ctx : ResolveContext) (p : Predicate) : Predicate :=
  { p with
    pointer := resolveAnnotTerm ctx p.pointer
    iargs := p.iargs.map (resolveAnnotTerm ctx)
  }

/-- Resolve symbols in a QPredicate -/
def resolveQPredicate (ctx : ResolveContext) (qp : QPredicate) : QPredicate :=
  { qp with
    pointer := resolveAnnotTerm ctx qp.pointer
    permission := resolveAnnotTerm ctx qp.permission
    iargs := qp.iargs.map (resolveAnnotTerm ctx)
  }

/-- Resolve symbols in a Request -/
def resolveRequest (ctx : ResolveContext) (req : Request) : Request :=
  match req with
  | .p pred => .p (resolvePredicate ctx pred)
  | .q qpred => .q (resolveQPredicate ctx qpred)

/-- Resolve symbols in an Output -/
def resolveOutput (ctx : ResolveContext) (out : Output) : Output :=
  { out with value := resolveAnnotTerm ctx out.value }

/-- Resolve symbols in a resource -/
def resolveResource (ctx : ResolveContext) (r : Resource) : Resource :=
  { r with
    request := resolveRequest ctx r.request
    output := resolveOutput ctx r.output
  }

/-! ## Clause Resolution

When resolving clauses, we also need to handle bindings.
`take v = Owned<int>(p)` introduces a new binding `v`.
-/

/-- Resolve a clause, returning updated context (for new bindings) and resolved clause -/
def resolveClause (ctx : ResolveContext) (c : Clause) : ResolveContext × Clause :=
  match c with
  | .resource name r =>
    -- Resource clause introduces a new binding
    -- First resolve the request to determine the output type
    let resolvedRequest := resolveRequest ctx r.request

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
    (ctx', .resource freshSym resolvedResource)
  | .constraint assertion =>
    -- Constraint uses current context, doesn't add bindings
    (ctx, .constraint (resolveAnnotTerm ctx assertion))

/-- Resolve all clauses in order, threading context through -/
def resolveClauses (ctx : ResolveContext) (clauses : List Clause) : ResolveContext × List Clause :=
  clauses.foldl (fun (ctx, resolved) clause =>
    let (ctx', resolvedClause) := resolveClause ctx clause
    (ctx', resolved ++ [resolvedClause])
  ) (ctx, [])

/-! ## Spec Resolution -/

/-- Resolve a precondition -/
def resolvePrecondition (ctx : ResolveContext) (pre : Precondition) : ResolveContext × Precondition :=
  let (ctx', clauses) := resolveClauses ctx pre.clauses
  (ctx', { clauses := clauses })

/-- Resolve a postcondition -/
def resolvePostcondition (ctx : ResolveContext) (post : Postcondition) : ResolveContext × Postcondition :=
  let (ctx', clauses) := resolveClauses ctx post.clauses
  (ctx', { clauses := clauses })

/-- Resolve a complete function specification.

    Takes:
    - The parsed spec (with placeholder symbols)
    - Parameter symbols from the function signature (with their CN types)
    - Return type for the function

    Creates a fresh return symbol and resolves all identifiers.

    Corresponds to: CN's desugaring of function specs in core_to_mucore.ml -/
def resolveFunctionSpec
    (spec : FunctionSpec)
    (params : List (Sym × BaseType))
    (returnType : BaseType := .unit)
    (nextFreshId : Nat := 1000)
    : FunctionSpec :=
  -- Build initial context with parameters INCLUDING TYPES
  let paramCtx : ResolveContext := {
    nameToSymType := params.filterMap fun (sym, bt) =>
      sym.name.map fun name => (name, sym, bt)
    nextFreshId := nextFreshId
  }

  -- Create fresh return symbol with return type and add to context
  let (ctxWithReturn, returnSym) := paramCtx.fresh "return" returnType

  -- Resolve precondition (bindings from requires are visible in ensures)
  let (ctxAfterPre, resolvedPre) := resolvePrecondition ctxWithReturn spec.requires

  -- Resolve postcondition (can see precondition bindings + return)
  let (_, resolvedPost) := resolvePostcondition ctxAfterPre spec.ensures

  { returnSym := returnSym
    requires := resolvedPre
    ensures := resolvedPost
    trusted := spec.trusted
  }

end CerbLean.CN.TypeChecking.Resolve
