/-
  muCore Transformation Types and Functions

  This module provides the Core → muCore transformation that CN requires.
  The transformation:
  1. Collects all `Esave` nodes into a LabelDefs map
  2. Replaces `Esave` with `Erun` in the body
  3. Marks return labels as terminal

  Corresponds to: cerberus/ocaml_frontend/milicore.ml
  Audited: 2026-01-28

  Design Decision: We keep a single Core AST and use predicates to
  characterize well-formedness (isRawCore vs isMuCore) rather than
  creating two separate AST types. This simplifies the transformation
  theorem and allows sharing infrastructure.
-/

import CerbLean.Core.Expr
import CerbLean.Core.Ctype
import Std.Data.HashMap

namespace CerbLean.Core.MuCore

open CerbLean.Core

/-! ## Label Definitions

Corresponds to: mi_label_def in milicore.ml lines 13-15
```ocaml
type 'TY mi_label_def =
  | Mi_Return of loc
  | Mi_Label of loc * lt * ((symbol * bt) list) * 'TY Core.expr * annot list
```
-/

/-- C-level parameter type information.
    Corresponds to: lt in milicore.ml line 11:
    `type lt = (Symbol.sym option * (Ctype.ctype * Core.pass_by_value_or_pointer)) list`

    We simplify by not tracking pass_by_value_or_pointer since CN doesn't use it heavily. -/
structure CParam where
  sym : Option Sym
  ctype : Ctype
  deriving Inhabited

/-- Information about a non-return label.
    Corresponds to: Mi_Label fields in milicore.ml line 15 -/
structure LabelInfo where
  /-- Source location of the label -/
  loc : Loc
  /-- C-level parameter types (for CN's logical typing) -/
  cParams : List CParam
  /-- Core-level parameters (symbol, base type) -/
  params : List (Sym × BaseType)
  /-- Continuation body -/
  body : AExpr
  /-- Original annotations -/
  annots : Annots
  deriving Inhabited

/-- A label definition: either a return point or a regular label.
    Corresponds to: mi_label_def in milicore.ml lines 13-15 -/
inductive LabelDef where
  /-- Return continuation - just stores location, no body needed.
      When `Erun` calls this, the argument is the return value and
      execution terminates for this path.
      Corresponds to: Mi_Return of loc -/
  | return_ (loc : Loc)
  /-- Regular labeled continuation with parameters and body.
      Corresponds to: Mi_Label of loc * lt * params * body * annots -/
  | label (info : LabelInfo)
  deriving Inhabited

/-- Map from label symbol ID to its definition.
    Corresponds to: mi_label_defs in milicore.ml line 17:
    `type 'TY mi_label_defs = (symbol, ('TY mi_label_def)) Pmap.map`

    We use a List with ID-based lookup instead of HashMap because symbols
    parsed from different parts of the JSON may have the same ID but different
    object identity (affecting hash-based equality). -/
abbrev LabelDefs := List (Nat × LabelDef)

/-! ## Well-Formedness Predicates

These predicates characterize whether an expression is in "raw Core" form
(as exported from Cerberus) or "muCore" form (after transformation).
-/

/-- Check if an expression contains any Esave nodes -/
partial def containsSave (e : Expr) : Bool :=
  match e with
  | .pure _ => false
  | .memop _ _ => false
  | .action _ => false
  | .case_ _ branches => branches.any fun (_, body) => containsSave body.expr
  | .let_ _ _ body => containsSave body.expr
  | .if_ _ then_ else_ => containsSave then_.expr || containsSave else_.expr
  | .ccall _ _ _ => false
  | .proc _ _ => false
  | .unseq es => es.any fun e => containsSave e.expr
  | .wseq _ e1 e2 => containsSave e1.expr || containsSave e2.expr
  | .sseq _ e1 e2 => containsSave e1.expr || containsSave e2.expr
  | .bound e => containsSave e.expr
  | .nd es => es.any fun e => containsSave e.expr
  | .save _ _ _ _ => true  -- Found a save!
  | .run _ _ => false
  | .par es => es.any fun e => containsSave e.expr
  | .wait _ => false
  | .annot _ e => containsSave e.expr
  | .excluded _ _ => false

/-- An expression is "muCore" if it contains no Esave nodes.
    In muCore, all saves have been extracted to a separate LabelDefs map
    and replaced with Erun. -/
def isMuCore (e : AExpr) : Bool := !containsSave e.expr

/-- An expression is "raw Core" (well-formed for interpretation).
    For now we don't enforce structural constraints on where Erun can appear. -/
def isRawCore (_e : AExpr) : Bool := true

/-! ## Transformation: Collect Saves

Corresponds to: Core_aux.m_collect_saves in core_aux.lem lines 2323-2512
This walks the expression tree and extracts all Esave nodes into a map.
-/

/-- Collect all Esave nodes from an expression into a LabelDefs list.
    Recursively processes save bodies to find nested saves.

    Corresponds to: m_collect_saves in core_aux.lem

    Note: We extract parameters from the Esave structure. The body's
    annotations tell us if this is a return label (via LAreturn). -/
partial def collectSaves (e : AExpr) : LabelDefs :=
  go [] e
where
  go (acc : LabelDefs) (e : AExpr) : LabelDefs :=
    match (e.expr : Expr) with
    | .pure _ => acc
    | .memop _ _ => acc
    | .action _ => acc
    | .case_ _ branches =>
      branches.foldl (fun acc' (_, body) => go acc' body) acc
    | .let_ _ _ body => go acc body
    | .if_ _ then_ else_ =>
      let acc' := go acc then_
      go acc' else_
    | .ccall _ _ _ => acc
    | .proc _ _ => acc
    | .unseq es => es.foldl go acc
    | .wseq _ e1 e2 =>
      let acc' := go acc e1
      go acc' e2
    | .sseq _ e1 e2 =>
      let acc' := go acc e1
      go acc' e2
    | .bound e => go acc e
    | .nd es => es.foldl go acc
    | .save retSym _retTy args body =>
      -- First, recursively collect saves from the body
      let acc' := go acc body
      -- Check if this is a return label
      -- Ideally we'd use e.annots.isReturn, but the JSON export doesn't include
      -- label annotations. Instead, we use a naming convention: labels starting
      -- with "ret_" are return labels (this is how Cerberus names them).
      -- TODO: Modify Cerberus JSON export to include label annotations
      let loc := e.annots.getLoc.getD .unknown
      let hasReturnName := retSym.name.map (·.startsWith "ret_") |>.getD false
      let isReturnLabel := hasReturnName || e.annots.isReturn
      let labelDef : LabelDef :=
        if isReturnLabel then
          .return_ loc
        else
          -- Extract parameters: (sym, bt, defaultPe) -> (sym, bt)
          let params := args.map fun (sym, bt, _) => (sym, bt)
          -- For now, we don't have C-level type info in the save itself
          -- This would need to come from annotations; leave empty for now
          let cParams : List CParam := []
          .label {
            loc := loc
            cParams := cParams
            params := params
            body := body
            annots := e.annots
          }
      -- Add to the list (using symbol ID as key)
      (retSym.id, labelDef) :: acc'
    | .run _ _ => acc
    | .par es => es.foldl go acc
    | .wait _ => acc
    | .annot _ e => go acc e
    | .excluded _ _ => acc

/-! ## Transformation: Remove Saves

Corresponds to: remove_save in milicore.ml lines 49-88
This replaces all Esave nodes with Erun nodes.
-/

/-- Replace all Esave nodes with Erun nodes.
    Esave(sym, ty, [(s₁,bt₁,pe₁), ...], body) → Erun(sym, [pe₁, ...])

    Note: This discards the body - it's already captured in LabelDefs.

    Corresponds to: remove_save in milicore.ml lines 49-88 -/
partial def removeSave (e : AExpr) : AExpr :=
  let annots := e.annots
  let expr' : Expr := match e.expr with
    | .pure pe => .pure pe
    | .memop op args => .memop op args
    | .action a => .action a
    | .case_ scrut branches =>
      .case_ scrut (branches.map fun (pat, body) => (pat, removeSave body))
    | .let_ pat pe body => .let_ pat pe (removeSave body)
    | .if_ cond then_ else_ => .if_ cond (removeSave then_) (removeSave else_)
    | .ccall funPtr funTy args => .ccall funPtr funTy args
    | .proc name args => .proc name args
    | .unseq es => .unseq (es.map removeSave)
    | .wseq pat e1 e2 => .wseq pat (removeSave e1) (removeSave e2)
    | .sseq pat e1 e2 => .sseq pat (removeSave e1) (removeSave e2)
    | .bound e => .bound (removeSave e)
    | .nd es => .nd (es.map removeSave)
    | .save retSym _retTy args _body =>
      -- Transform: Esave(sym, ty, [(s,bt,pe), ...], body) → Erun(sym, [pe, ...])
      -- Extract just the default expressions from the args
      let runArgs := args.map fun (_, _, pe) => pe
      .run retSym runArgs
    | .run label args => .run label args
    | .par es => .par (es.map removeSave)
    | .wait tid => .wait tid
    | .annot dynAnnots e => .annot dynAnnots (removeSave e)
    | .excluded exclId act => .excluded exclId act
  { annots := annots, expr := expr' }

/-! ## muCore Procedure

A transformed procedure ready for CN type checking.
-/

/-- A muCore procedure: transformed body + extracted labels.
    Corresponds to: Mi_Proc in milicore.ml line 21 -/
structure MuProc where
  /-- Transformed body (no Esave nodes) -/
  body : AExpr
  /-- Extracted label definitions -/
  labels : LabelDefs

/-- Transform a raw Core procedure to muCore form.
    Returns the transformed body and extracted label definitions.

    Corresponds to: core_to_micore__funmap_decl in milicore.ml lines 91-128 -/
def transformProc (body : AExpr) : MuProc :=
  let labels := collectSaves body
  let body' := removeSave body
  { body := body', labels := labels }

/-! ## Label Lookup Helpers -/

/-- Look up a label by symbol ID -/
def LabelDefs.get? (labels : LabelDefs) (sym : Sym) : Option LabelDef :=
  labels.lookup sym.id

/-- Check if a label is a return continuation -/
def LabelDefs.isReturn (labels : LabelDefs) (sym : Sym) : Bool :=
  match labels.get? sym with
  | some (.return_ _) => true
  | _ => false

/-- Get label info (for non-return labels) -/
def LabelDefs.getInfo (labels : LabelDefs) (sym : Sym) : Option LabelInfo :=
  match labels.get? sym with
  | some (.label info) => some info
  | _ => none

/-- Get the number of labels -/
def LabelDefs.size (labels : LabelDefs) : Nat := labels.length

end CerbLean.Core.MuCore
