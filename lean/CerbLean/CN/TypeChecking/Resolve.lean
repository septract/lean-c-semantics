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

/-- Context for name resolution -/
structure ResolveContext where
  /-- Map from identifier name to resolved symbol -/
  nameToSym : List (String × Sym)
  /-- Counter for generating fresh symbol IDs -/
  nextFreshId : Nat
  deriving Inhabited

namespace ResolveContext

/-- Create an empty context -/
def empty : ResolveContext :=
  { nameToSym := [], nextFreshId := 1000 }  -- Start high to avoid conflicts

/-- Look up a name in the context -/
def lookup (ctx : ResolveContext) (name : String) : Option Sym :=
  ctx.nameToSym.find? (fun (n, _) => n == name) |>.map (·.2)

/-- Add a binding to the context -/
def add (ctx : ResolveContext) (name : String) (sym : Sym) : ResolveContext :=
  { ctx with nameToSym := (name, sym) :: ctx.nameToSym }

/-- Generate a fresh symbol and add it to the context -/
def fresh (ctx : ResolveContext) (name : String) : ResolveContext × Sym :=
  let sym : Sym := { id := ctx.nextFreshId, name := some name }
  let ctx' := { ctx with
    nameToSym := (name, sym) :: ctx.nameToSym
    nextFreshId := ctx.nextFreshId + 1
  }
  (ctx', sym)

end ResolveContext

/-! ## Symbol Resolution

Resolve symbols in terms by looking them up in the context.
Unresolved symbols (ID = 0) are looked up by name.
Already-resolved symbols (ID ≠ 0) are left unchanged.
-/

/-- Check if a symbol needs resolution (has placeholder ID 0) -/
def needsResolution (s : Sym) : Bool :=
  s.id == 0

/-- Resolve a symbol using the context.
    Returns the resolved symbol, or the original if not found (error case). -/
def resolveSym (ctx : ResolveContext) (s : Sym) : Sym :=
  if needsResolution s then
    match s.name with
    | some name =>
      match ctx.lookup name with
      | some resolved => resolved
      | none => s  -- Not found - keep original (will be caught by type checker)
    | none => s  -- No name - keep original
  else
    s  -- Already resolved

/-! ## Term Resolution

Walk the term structure and resolve all symbols.
-/

mutual

/-- Resolve symbols in a term -/
partial def resolveTerm (ctx : ResolveContext) (t : Term) : Term :=
  match t with
  | .const c => .const c
  | .sym s => .sym (resolveSym ctx s)
  | .unop op arg => .unop op (resolveAnnotTerm ctx arg)
  | .binop op l r => .binop op (resolveAnnotTerm ctx l) (resolveAnnotTerm ctx r)
  | .ite c t e => .ite (resolveAnnotTerm ctx c) (resolveAnnotTerm ctx t) (resolveAnnotTerm ctx e)
  | .eachI lo v hi body => .eachI lo v hi (resolveAnnotTerm ctx body)
  | .tuple elems => .tuple (elems.map (resolveAnnotTerm ctx))
  | .nthTuple n tup => .nthTuple n (resolveAnnotTerm ctx tup)
  | .struct_ tag members => .struct_ tag (members.map fun (id, t) => (id, resolveAnnotTerm ctx t))
  | .structMember obj member => .structMember (resolveAnnotTerm ctx obj) member
  | .structUpdate obj member value => .structUpdate (resolveAnnotTerm ctx obj) member (resolveAnnotTerm ctx value)
  | .record members => .record (members.map fun (id, t) => (id, resolveAnnotTerm ctx t))
  | .recordMember obj member => .recordMember (resolveAnnotTerm ctx obj) member
  | .recordUpdate obj member value => .recordUpdate (resolveAnnotTerm ctx obj) member (resolveAnnotTerm ctx value)
  | .constructor constr args => .constructor constr (args.map fun (id, t) => (id, resolveAnnotTerm ctx t))
  | .memberShift ptr tag member => .memberShift (resolveAnnotTerm ctx ptr) tag member
  | .arrayShift base ct idx => .arrayShift (resolveAnnotTerm ctx base) ct (resolveAnnotTerm ctx idx)
  | .copyAllocId addr loc => .copyAllocId (resolveAnnotTerm ctx addr) (resolveAnnotTerm ctx loc)
  | .hasAllocId ptr => .hasAllocId (resolveAnnotTerm ctx ptr)
  | .sizeOf ct => .sizeOf ct
  | .offsetOf tag member => .offsetOf tag member
  | .nil bt => .nil bt
  | .cons head tail => .cons (resolveAnnotTerm ctx head) (resolveAnnotTerm ctx tail)
  | .head list => .head (resolveAnnotTerm ctx list)
  | .tail list => .tail (resolveAnnotTerm ctx list)
  | .representable ct value => .representable ct (resolveAnnotTerm ctx value)
  | .good ct value => .good ct (resolveAnnotTerm ctx value)
  | .aligned ptr align => .aligned (resolveAnnotTerm ctx ptr) (resolveAnnotTerm ctx align)
  | .wrapI intTy value => .wrapI intTy (resolveAnnotTerm ctx value)
  | .mapConst keyTy value => .mapConst keyTy (resolveAnnotTerm ctx value)
  | .mapSet m k v => .mapSet (resolveAnnotTerm ctx m) (resolveAnnotTerm ctx k) (resolveAnnotTerm ctx v)
  | .mapGet m k => .mapGet (resolveAnnotTerm ctx m) (resolveAnnotTerm ctx k)
  | .mapDef var body => .mapDef var (resolveAnnotTerm ctx body)
  | .apply fn args => .apply (resolveSym ctx fn) (args.map (resolveAnnotTerm ctx))
  | .let_ var binding body => .let_ var (resolveAnnotTerm ctx binding) (resolveAnnotTerm ctx body)
  | .match_ scrutinee cases => .match_ (resolveAnnotTerm ctx scrutinee) (cases.map fun (p, t) => (p, resolveAnnotTerm ctx t))
  | .cast targetTy value => .cast targetTy (resolveAnnotTerm ctx value)
  | .cnNone bt => .cnNone bt
  | .cnSome value => .cnSome (resolveAnnotTerm ctx value)
  | .isSome opt => .isSome (resolveAnnotTerm ctx opt)
  | .getOpt opt => .getOpt (resolveAnnotTerm ctx opt)

/-- Resolve symbols in an annotated term -/
partial def resolveAnnotTerm (ctx : ResolveContext) (at_ : AnnotTerm) : AnnotTerm :=
  match at_ with
  | .mk t bt loc => .mk (resolveTerm ctx t) bt loc

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
    -- IMPORTANT: We must create the fresh symbol FIRST, then use it for the output
    -- Otherwise the resource's output.value won't match the binding symbol
    let (ctx', freshSym) := ctx.fresh (name.name.getD "anon")

    -- Now resolve the resource's request with the ORIGINAL context
    -- (the request can reference symbols defined earlier, but not this binding)
    let resolvedRequest := resolveRequest ctx r.request

    -- Create the resource with the fresh symbol as its output value
    -- This ensures the output.value matches the binding symbol
    let resolvedResource : Resource := {
      request := resolvedRequest
      output := { value := AnnotTerm.mk (.sym freshSym) r.output.value.bt r.output.value.loc }
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
    - Parameter symbols from the function signature

    Creates a fresh return symbol and resolves all identifiers.

    Corresponds to: CN's desugaring of function specs in core_to_mucore.ml -/
def resolveFunctionSpec
    (spec : FunctionSpec)
    (params : List (Sym × BaseType))
    (nextFreshId : Nat := 1000)
    : FunctionSpec :=
  -- Build initial context with parameters
  let paramCtx : ResolveContext := {
    nameToSym := params.filterMap fun (sym, _) =>
      sym.name.map fun name => (name, sym)
    nextFreshId := nextFreshId
  }

  -- Create fresh return symbol and add to context
  let (ctxWithReturn, returnSym) := paramCtx.fresh "return"

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
