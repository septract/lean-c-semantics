/-
  Symbol environment for the interpreter
  Based on cerberus/frontend/model/core_run.lem (thread_state.env)
-/

import CToLean.Semantics.Monad
import Std.Data.HashMap

namespace CToLean.Semantics

open CToLean.Core
open Std (HashMap)

/-! ## Symbol Environment

The symbol environment is a scoped map from symbols to values.
New scopes are pushed when entering functions or let bindings,
and popped when exiting.
-/

/-- Symbol environment with scoped bindings -/
structure SymEnv where
  /-- Stack of scope maps (head is innermost scope) -/
  scopes : List (HashMap Sym Value) := [{}]
  deriving Inhabited

namespace SymEnv

/-- Create an empty environment with one scope -/
def empty : SymEnv := { scopes := [{}] }

/-- Look up a symbol in the environment (searches from innermost scope) -/
def lookup (env : SymEnv) (sym : Sym) : Option Value :=
  env.scopes.findSome? fun scope => scope[sym]?

/-- Bind a symbol to a value in the current (innermost) scope -/
def bind (env : SymEnv) (sym : Sym) (val : Value) : SymEnv :=
  match env.scopes with
  | [] =>
    let emptyMap : HashMap Sym Value := {}
    { scopes := [emptyMap.insert sym val] }  -- Shouldn't happen
  | scope :: rest => { scopes := (scope.insert sym val) :: rest }

/-- Bind multiple symbols in the current scope -/
def bindAll (env : SymEnv) (bindings : List (Sym × Value)) : SymEnv :=
  bindings.foldl (fun e (s, v) => e.bind s v) env

/-- Push a new empty scope -/
def pushScope (env : SymEnv) : SymEnv :=
  { scopes := {} :: env.scopes }

/-- Pop the innermost scope -/
def popScope (env : SymEnv) : SymEnv :=
  match env.scopes with
  | [] => env  -- Already empty
  | _ :: rest => { scopes := if rest.isEmpty then [{}] else rest }

/-- Push a new scope with initial bindings -/
def pushScopeWith (env : SymEnv) (bindings : List (Sym × Value)) : SymEnv :=
  let emptyMap : HashMap Sym Value := {}
  let newScope := bindings.foldl (fun m (s, v) => m.insert s v) emptyMap
  { scopes := newScope :: env.scopes }

end SymEnv

/-! ## Continuation Environment

For save/run continuation handling.
-/

/-- Saved continuation (for save/run mechanism) -/
structure SavedCont where
  /-- Return type -/
  retTy : BaseType
  /-- Parameter symbols with their types and default values -/
  params : List (Sym × BaseType × APexpr)
  /-- Continuation body to execute (includes trailing code from sequences) -/
  body : Expr
  deriving Inhabited

/-- Continuation map: label symbol -> saved continuation -/
abbrev ContEnv := HashMap Sym SavedCont

/-! ## Pre-collecting Labeled Continuations

When entering a procedure, we pre-collect all `save` blocks and their continuation
bodies. This is necessary because `run label(args)` can jump to any `save` in the
procedure, not just those lexically enclosing it.

Key insight: when a save is inside a sequence, its continuation body includes
the rest of the sequence. E.g., `save X in body ; rest` means running X executes
`body ; rest`.
-/

/-- Collect all labeled continuations from an expression.
    Returns a map from label symbols to (params, body with continuation). -/
partial def collectLabeledConts (expr : Expr) : ContEnv :=
  go expr id
where
  /-- Helper that tracks the continuation wrapper -/
  go (e : Expr) (wrap : Expr → Expr) : ContEnv :=
    match e with
    | .pure _ => {}
    | .memop _ _ => {}
    | .action _ => {}
    | .ccall _ _ _ => {}
    | .proc _ _ => {}
    | .run _ _ => {}
    | .par _ => {}
    | .wait _ => {}
    | .bound inner => go inner wrap
    | .nd es => es.foldl (fun acc e' => acc.union (go e' wrap)) {}
    | .unseq es => es.foldl (fun acc e' => acc.union (go e' wrap)) {}
    | .case_ _ branches =>
      branches.foldl (fun acc (_, body) => acc.union (go body wrap)) {}
    | .let_ pat e1 e2 =>
      -- Continue collecting in e2 (let bindings don't affect continuation)
      go e2 wrap
    | .if_ _ then_ else_ =>
      (go then_ wrap).union (go else_ wrap)
    | .wseq pat e1 e2 =>
      -- For saves in e1, wrap with the continuation (wseq pat _ e2)
      let wrapE1 body := wrap (.wseq pat body e2)
      let fromE1 := go e1 wrapE1
      let fromE2 := go e2 wrap
      fromE1.union fromE2
    | .sseq pat e1 e2 =>
      -- For saves in e1, wrap with the continuation (sseq pat _ e2)
      let wrapE1 body := wrap (.sseq pat body e2)
      let fromE1 := go e1 wrapE1
      let fromE2 := go e2 wrap
      fromE1.union fromE2
    | .save retSym retTy params body =>
      -- Record this save with wrapped body
      let wrappedBody := wrap body
      let cont : SavedCont := { retTy, params, body := wrappedBody }
      -- Also collect from inside the save body
      let inner := go body wrap
      inner.insert retSym cont

/-! ## Extended Evaluation Environment

Includes both symbol bindings and continuations.
-/

/-- Full evaluation environment -/
structure EvalEnv where
  /-- Symbol bindings -/
  symEnv : SymEnv := {}
  /-- Saved continuations for save/run -/
  contEnv : ContEnv := {}
  deriving Inhabited

namespace EvalEnv

/-- Create empty evaluation environment -/
def empty : EvalEnv := {}

/-- Look up a symbol -/
def lookup (env : EvalEnv) (sym : Sym) : Option Value :=
  env.symEnv.lookup sym

/-- Bind a symbol -/
def bind (env : EvalEnv) (sym : Sym) (val : Value) : EvalEnv :=
  { env with symEnv := env.symEnv.bind sym val }

/-- Bind multiple symbols -/
def bindAll (env : EvalEnv) (bindings : List (Sym × Value)) : EvalEnv :=
  { env with symEnv := env.symEnv.bindAll bindings }

/-- Push new scope -/
def pushScope (env : EvalEnv) : EvalEnv :=
  { env with symEnv := env.symEnv.pushScope }

/-- Pop scope -/
def popScope (env : EvalEnv) : EvalEnv :=
  { env with symEnv := env.symEnv.popScope }

/-- Initialize continuations from a procedure body -/
def withConts (env : EvalEnv) (body : AExpr) : EvalEnv :=
  { env with contEnv := collectLabeledConts body.expr }

/-- Look up a saved continuation -/
def lookupCont (env : EvalEnv) (label : Sym) : Option SavedCont :=
  env.contEnv[label]?

end EvalEnv

end CToLean.Semantics
