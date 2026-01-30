/-
  Evaluation contexts for contextual decomposition
  Corresponds to: cerberus/frontend/model/core_run_aux.lem (context type)
                  cerberus/frontend/model/core_reduction.lem (get_ctx, apply_ctx)

  This module implements the contextual decomposition approach used in core_reduction.lem
  to find all possible reduction points in an expression.
-/

import CerbLean.Core

namespace CerbLean.Semantics

open CerbLean.Core
open CerbLean.Memory

/-! ## Evaluation Context Type

Corresponds to: core_run_aux.lem:28-34
```lem
type context =
  | CTX
  | Cunseq of list Annot.annot * list (Core.expr core_run_annotation) * context * list (Core.expr core_run_annotation)
  | Cwseq of list Annot.annot * Core.pattern * context * Core.expr core_run_annotation
  | Csseq of list Annot.annot * Core.pattern * context * Core.expr core_run_annotation
  | Cannot of list Annot.annot * list Core.dyn_annotation * context
  | Cbound of list Annot.annot * context
```
-/

/-- Evaluation context representing a "hole" in an expression where reduction can occur -/
inductive Context where
  | ctx                                                                            -- CTX (the hole)
  | unseq (annots : Annots) (before : List AExpr) (inner : Context) (after : List AExpr)  -- Cunseq
  | wseq (annots : Annots) (pat : APattern) (inner : Context) (e2 : AExpr)         -- Cwseq
  | sseq (annots : Annots) (pat : APattern) (inner : Context) (e2 : AExpr)         -- Csseq
  | annot_ (annots : Annots) (dynAnnots : DynAnnotations) (inner : Context)        -- Cannot
  | bound (annots : Annots) (inner : Context)                                      -- Cbound
  deriving Inhabited

/-! ## Irreducibility Check

Corresponds to: core_reduction.lem:181-194
```lem
let is_irreducible = function
    (* v *)
  | Expr _ (Epure (Pexpr _ _ (PEval _))) -> true
    (* annot(..., v) *)
  | Expr _ (Eannot _ (Expr _ (Epure (Pexpr _ _ (PEval _))))) -> true
    (* annot(..., annot(..., _)) ==> has a one step reduction, so NOT irreducible *)
  | Expr _ (Eannot _ (Expr _ (Eannot _ _))) -> false
  | _ -> false
```
-/

/-- Check if an expression is irreducible (a value or annotated value).
    Irreducible expressions cannot be reduced further within an unseq context.
    Corresponds to: core_reduction.lem:181-194
    Audited: 2026-01-30
    Deviations: CerbLean catches {A}{A}_ (any nested annotations) while Cerberus
    specifically checks {A}{A}v (nested around value). This is functionally equivalent
    because Cerberus's `_ -> false` fallthrough catches all other nested cases anyway.
    Both return false for all nested annotation patterns. -/
def isIrreducible : AExpr → Bool
  -- v (pure value)
  | ⟨_, .pure ⟨_, _, .val _⟩⟩ => true
  -- {A}v (annotated value)
  | ⟨_, .annot _ ⟨_, .pure ⟨_, _, .val _⟩⟩⟩ => true
  -- {A}{A}_ (nested annotations) - NOT irreducible, needs reduction via ANNOTS rule
  -- Note: Cerberus checks {A}{A}v specifically, but falls through to `_ -> false` for others
  | ⟨_, .annot _ ⟨_, .annot _ _⟩⟩ => false
  -- Everything else is reducible
  | _ => false

/-! ## Context Application

Corresponds to: core_reduction.lem:591-606
```lem
let rec apply_ctx ctx expr =
  match ctx with
    | CTX -> expr
    | Cunseq annot es1 ctx' es2 ->
        Expr annot (Eunseq (es1 ++ (apply_ctx ctx' expr :: es2)))
    | Cwseq annot pat ctx' e2 ->
        Expr annot (Ewseq pat (apply_ctx ctx' expr) e2)
    | Csseq annot pat ctx' e2 ->
        Expr annot (Esseq pat (apply_ctx ctx' expr) e2)
    | Cannot annot xs ctx' ->
        Expr annot (Eannot xs (apply_ctx ctx' expr))
    | Cbound annot ctx' ->
        Expr annot (Ebound (apply_ctx ctx' expr))
  end
```
-/

/-- Apply a context to an expression (plug the expression into the hole).
    Corresponds to: core_reduction.lem:591-606 -/
def applyCtx : Context → AExpr → AExpr
  | .ctx, e => e
  | .unseq annots before inner after, e =>
      ⟨annots, .unseq (before ++ [applyCtx inner e] ++ after)⟩
  | .wseq annots pat inner e2, e =>
      ⟨annots, .wseq pat (applyCtx inner e) e2⟩
  | .sseq annots pat inner e2, e =>
      ⟨annots, .sseq pat (applyCtx inner e) e2⟩
  | .annot_ annots dynAnnots inner, e =>
      ⟨annots, .annot dynAnnots (applyCtx inner e)⟩
  | .bound annots inner, e =>
      ⟨annots, .bound (applyCtx inner e)⟩

/-! ## Contextual Decomposition

Corresponds to: core_reduction.lem:509-588
```lem
let rec get_ctx (Expr annot expr_ as expr) =
  if is_irreducible expr then
    [(CTX, expr)]
  else match expr_ with
    | Epure _ -> [(CTX, expr)]
    | Ememop _ _ -> [(CTX, expr)]
    | Eaction _ -> [(CTX, expr)]
    ...
    | Eunseq es ->
        if List.all is_irreducible es then
          [(CTX, expr)]
        else
          get_ctx_unseq_aux annot [] [] es
    ...
  end
```
-/

mutual
/-- Get all (context, reducible-expr) pairs for an expression.
    Returns a list of all possible reduction points.
    Corresponds to: core_reduction.lem:509-574 -/
partial def getCtx (e : AExpr) : List (Context × AExpr) :=
  if isIrreducible e then
    [(.ctx, e)]
  else
    match e with
    | ⟨annots, expr⟩ =>
      match expr with
      -- Base cases: these expressions are reducible at the top level
      | .pure _ => [(.ctx, e)]
      | .memop _ _ => [(.ctx, e)]
      | .action _ => [(.ctx, e)]
      | .case_ _ _ => [(.ctx, e)]
      | .let_ _ _ _ => [(.ctx, e)]
      | .if_ _ _ _ => [(.ctx, e)]
      | .ccall _ _ _ => [(.ctx, e)]
      | .proc _ _ => [(.ctx, e)]
      | .nd _ => [(.ctx, e)]
      | .save _ _ _ _ => [(.ctx, e)]
      | .run _ _ => [(.ctx, e)]
      | .par _ => [(.ctx, e)]
      | .wait _ => [(.ctx, e)]

      -- Eunseq: find all reducible sub-expressions
      | .unseq es =>
          if es.all isIrreducible then
            [(.ctx, e)]
          else
            getCtxUnseqAux annots [] [] es

      -- Ewseq: decompose into first operand if reducible
      | .wseq pat e1 e2 =>
          if isIrreducible e1 then
            [(.ctx, e)]
          else
            (getCtx e1).map fun (innerCtx, inner) =>
              (.wseq annots pat innerCtx e2, inner)

      -- Esseq: decompose into first operand if reducible
      | .sseq pat e1 e2 =>
          if isIrreducible e1 then
            [(.ctx, e)]
          else
            (getCtx e1).map fun (innerCtx, inner) =>
              (.sseq annots pat innerCtx e2, inner)

      -- Ebound: decompose into body if reducible
      | .bound body =>
          if isIrreducible body then
            [(.ctx, e)]
          else
            (getCtx body).map fun (innerCtx, inner) =>
              (.bound annots innerCtx, inner)

      -- Eannot: special cases
      | .annot xs innerE =>
          -- Check for nested annotations: {A}{A}e -> needs flattening, not decomposition
          match innerE with
          | ⟨_, .annot _ _⟩ => [(.ctx, e)]
          | _ =>
              (getCtx innerE).map fun (innerCtx, inner) =>
                (.annot_ annots xs innerCtx, inner)

      -- Eexcluded: reducible at top level (executes the wrapped action)
      | .excluded _ _ => [(.ctx, e)]

/-- Get contexts for unseq operands.
    Accumulates all (context, expr) pairs for reducible expressions in the unseq.
    Corresponds to: core_reduction.lem:576-588
    ```lem
    and get_ctx_unseq_aux annot acc es1 = function
      | [] -> acc
      | e :: es2 ->
          if is_irreducible e then
            get_ctx_unseq_aux annot acc (es1 ++ [e]) es2
          else
            let zs = List.map (fun (ctx, e) ->
                (Cunseq annot es1 ctx es2, e)
              ) (get_ctx e) in
            get_ctx_unseq_aux annot (zs ++ acc) (es1 ++ [e]) es2
    ```
-/
partial def getCtxUnseqAux (annots : Annots) (acc : List (Context × AExpr))
    (before : List AExpr) : List AExpr → List (Context × AExpr)
  | [] => acc
  | e :: after =>
      if isIrreducible e then
        -- Skip irreducible expressions, add to "before"
        getCtxUnseqAux annots acc (before ++ [e]) after
      else
        -- Found reducible expression: add all its decompositions
        -- Corresponds to: core_reduction.lem:583-587
        -- Audited: 2026-01-30
        -- Deviations: None
        let zs := (getCtx e).map fun (innerCtx, inner) =>
          (Context.unseq annots before innerCtx after, inner)
        -- Continue with remaining expressions (e added to "before")
        getCtxUnseqAux annots (zs ++ acc) (before ++ [e]) after

end

/-! ## Helper Functions -/

/-- String representation of a context (for debugging) -/
partial def Context.toString : Context → String
  | .ctx => "CTX"
  | .unseq _ _ inner _ => s!"Cunseq[{inner.toString}]"
  | .wseq _ _ inner _ => s!"Cwseq[{inner.toString}]"
  | .sseq _ _ inner _ => s!"Csseq[{inner.toString}]"
  | .annot_ _ _ inner => s!"Cannot[{inner.toString}]"
  | .bound _ inner => s!"Cbound[{inner.toString}]"

instance : ToString Context := ⟨Context.toString⟩

end CerbLean.Semantics
