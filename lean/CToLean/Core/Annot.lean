/-
  Annotations and source locations
  Based on cerberus/frontend/model/annot.lem and loc.lem
-/

namespace CToLean.Core

/-- Source location -/
structure Loc where
  file : String
  startLine : Nat
  startCol : Nat
  endLine : Nat
  endCol : Nat
  deriving Repr, BEq, Inhabited

def Loc.unknown : Loc := ⟨"<unknown>", 0, 0, 0, 0⟩

/-- Annotation kinds -/
inductive Annot where
  | loc (l : Loc)
  | uid (id : Nat)
  | other (key : String) (value : String)
  deriving Repr, BEq, Inhabited

/-- List of annotations -/
abbrev Annots := List Annot

/-- Get location from annotations if present -/
def Annots.getLoc (annots : Annots) : Option Loc :=
  annots.findSome? fun
    | .loc l => some l
    | _ => none

end CToLean.Core
