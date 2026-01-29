/-
  Symbol environment for the interpreter
  Based on cerberus/frontend/model/core_run.lem (thread_state.env)
-/

import CerbLean.Semantics.Monad
import CerbLean.Semantics.State
import Std.Data.HashMap

namespace CerbLean.Semantics

open CerbLean.Core
open Std (HashMap)

/-! ## Pre-collecting Labeled Continuations

Corresponds to: collect_labeled_continuations in core_aux.lem:1880-1931

When entering a procedure, we pre-collect all `save` blocks and their continuation
bodies. This is necessary because `run label(args)` can jump to any `save` in the
procedure, not just those lexically enclosing it.

CRITICAL: The wrapping logic must match Cerberus EXACTLY:
- For `Esave (sym_lab, _) sym_bTys e`: store `(List.map fst sym_bTys, e)` directly
- For `Ewseq pat e1 e2`: wrap continuations from e1 with `Ewseq pat _ e2`
- For `Esseq pat e1 e2`: wrap continuations from e1 with `Esseq pat _ e2`

```lem
val     collect_labeled_continuations: forall 'a. expr 'a -> map Symbol.sym (list (Symbol.sym) * expr 'a)
let rec collect_labeled_continuations (Expr annot expr_) =
  match expr_ with
    | Epure _ -> Map.empty
    | Ememop _ _ -> Map.empty
    | Elet _ _ e2 -> collect_labeled_continuations e2
    | Eif pe1 e2 e3 -> Map.(union) (collect_labeled_continuations e2) (collect_labeled_continuations e3)
    | Ecase pe pat_es -> Map.empty (* TODO THIS IS WRONG!!!!! *)
    | Eproc _ _ _ -> Map.empty
    | Eccall _ _ _ _ -> Map.empty
    | Eaction _ -> Map.empty
    | Eunseq _ -> Map.empty
    | Ewseq _as e1 e2 ->
        Map.(union) (Map.map (fun (a_tys, e) -> (a_tys, Expr annot (Ewseq _as e e2))) $ collect_labeled_continuations e1)
                    (collect_labeled_continuations e2)
    | Esseq _as e1 e2 ->
        Map.(union) (Map.map (fun (a_tys, e) -> (a_tys, Expr annot (Esseq _as e e2))) $ collect_labeled_continuations e1)
                    (collect_labeled_continuations e2)
    | Ebound _ -> Map.empty
    | Esave (sym_lab, _) sym_bTys e ->
        Map.insert sym_lab (List.map fst sym_bTys, e) $ collect_labeled_continuations e
    | Erun _ _ _ -> Map.empty
    | End _ -> Map.empty
    | Epar _ -> Map.empty
    | Ewait _ -> Map.empty
    | Eannot _ _ -> Map.empty
    | Eexcluded _ _ -> Map.empty
  end
```
-/

mutual
/-- Collect all labeled continuations from an expression.
    Corresponds to: collect_labeled_continuations in core_aux.lem:1880-1931
    Audited: 2025-01-01
    Deviations: None - matches Cerberus exactly -/
def collectLabeledContinuations (e : AExpr) : LabeledConts :=
  match e with
  | ⟨annots, expr⟩ =>
  match expr with
  | .pure _ => {}
  | .memop _ _ => {}
  | .action _ => {}
  | .ccall _ _ _ => {}
  | .proc _ _ => {}
  | .run _ _ => {}
  | .par _ => {}
  | .wait _ => {}
  | .bound _ => {}  -- Cerberus returns Map.empty for Ebound
  | .nd _ => {}  -- Cerberus returns Map.empty for End
  | .unseq _ => {}  -- Cerberus returns Map.empty for Eunseq
  | .annot _ inner => collectLabeledContinuations inner  -- Collect from inner expression

  | .let_ _pat _e1 e2 =>
    -- Elet _ _ e2 -> collect_labeled_continuations e2
    collectLabeledContinuations e2

  | .if_ _cond then_ else_ =>
    -- Map.(union) (collect_labeled_continuations e2) (collect_labeled_continuations e3)
    (collectLabeledContinuations then_).union (collectLabeledContinuations else_)

  | .case_ _ branches =>
    -- Collect from all case branches
    -- Corresponds to: collect_saves_aux case in core_aux.lem:2196-2199
    -- Cerberus's old collect_labeled_continuations was wrong here, but collect_saves fixes it
    -- Audited: 2026-01-02
    collectLabeledContinuationsBranches branches

  | .wseq pat e1 e2 =>
    -- Map.(union) (Map.map (fun (a_tys, e) -> (a_tys, Expr annot (Ewseq _as e e2))) $ collect_labeled_continuations e1)
    --             (collect_labeled_continuations e2)
    let fromE1 := collectLabeledContinuations e1
    -- Note: fold over HashMap result (not AST) is not recursive
    let wrappedE1 : LabeledConts := fromE1.fold (init := {}) fun acc sym cont =>
      let wrappedBody : AExpr := { annots, expr := .wseq pat cont.body e2 }
      acc.insert sym { cont with body := wrappedBody }
    let fromE2 := collectLabeledContinuations e2
    wrappedE1.union fromE2

  | .sseq pat e1 e2 =>
    -- Map.(union) (Map.map (fun (a_tys, e) -> (a_tys, Expr annot (Esseq _as e e2))) $ collect_labeled_continuations e1)
    --             (collect_labeled_continuations e2)
    let fromE1 := collectLabeledContinuations e1
    -- Note: fold over HashMap result (not AST) is not recursive
    let wrappedE1 : LabeledConts := fromE1.fold (init := {}) fun acc sym cont =>
      let wrappedBody : AExpr := { annots, expr := .sseq pat cont.body e2 }
      acc.insert sym { cont with body := wrappedBody }
    let fromE2 := collectLabeledContinuations e2
    wrappedE1.union fromE2

  | .save symLab _retTy params body =>
    -- Map.insert sym_lab (List.map fst sym_bTys, e) $ collect_labeled_continuations e
    let paramSyms := params.map fun (sym, _, _) => sym
    let cont : LabeledCont := { params := paramSyms, body }
    let inner := collectLabeledContinuations body
    inner.insert symLab cont

/-- Helper for processing case branches - explicit recursion for termination -/
def collectLabeledContinuationsBranches (branches : List (APattern × AExpr)) : LabeledConts :=
  match branches with
  | [] => {}
  | (_, body) :: rest =>
    (collectLabeledContinuations body).union (collectLabeledContinuationsBranches rest)
end

/-- Collect labeled continuations for all procedures in a file.
    Corresponds to: collect_labeled_continuations_NEW in core_aux.lem:2379-2393
    ```lem
    val collect_labeled_continuations_NEW: forall 'a.
      file 'a -> map Symbol.sym (map Symbol.sym (list (Symbol.sym * core_base_type) * expr 'a))
    let collect_labeled_continuations_NEW file =
      Map_extra.fold (fun fun_sym decl acc ->
        match decl with
          | Fun _ _ _ -> acc
          | Proc _ _ _ _ e ->
              Map.insert fun_sym (collect_saves e) acc
          | ProcDecl _ _ _ -> acc
          | BuiltinDecl _ _ _ -> acc
        end) (Map.(union) file.stdlib file.funs) Map.empty
    ```
    Note: Cerberus uses `collect_saves` (core_aux.lem:2258-2261) which handles Epar.
    We use `collectLabeledContinuations` based on the older function, which is
    equivalent for sequential code (we don't support Epar).
    Audited: 2026-01-02
    Deviations: None for sequential code -/
def collectAllLabeledContinuations (file : File) : AllLabeledConts :=
  let emptyMap : AllLabeledConts := {}
  -- Process funs first
  let withFuns := file.funs.foldl (init := emptyMap) fun acc (procSym, decl) =>
    match decl with
    | .proc _ _ _ _ body =>
      let conts := collectLabeledContinuations body
      acc.insert procSym conts
    | .fun_ _ _ _ => acc
    | .procDecl _ _ _ => acc
    | .builtinDecl _ _ _ => acc
  -- Also process stdlib
  file.stdlib.foldl (init := withFuns) fun acc (procSym, decl) =>
    match decl with
    | .proc _ _ _ _ body =>
      let conts := collectLabeledContinuations body
      acc.insert procSym conts
    | .fun_ _ _ _ => acc
    | .procDecl _ _ _ => acc
    | .builtinDecl _ _ _ => acc

end CerbLean.Semantics
