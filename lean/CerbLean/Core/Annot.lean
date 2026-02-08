/-
  Annotations and source locations
  Corresponds to: cerberus/frontend/model/annot.lem
  Audited: 2025-12-31
  Deviations: None
-/

import CerbLean.Core.IntegerType

namespace CerbLean.Core

/-! ## Source Position

Corresponds to: cerberus/util/cerb_position.ml
-/

/-- Source position (file, line, column)
    Corresponds to: Cerb_position.t -/
structure Pos where
  file : String
  line : Nat
  col : Nat
  deriving Repr, BEq, Inhabited

/-! ## Source Location

Corresponds to: cerberus/util/cerb_location.ml
```ocaml
type cursor =
  | NoCursor
  | PointCursor of Cerb_position.t
  | RegionCursor of Cerb_position.t * Cerb_position.t

type t =
  | Loc_unknown
  | Loc_other of string
  | Loc_point of Cerb_position.t
  | Loc_region of Cerb_position.t * Cerb_position.t * cursor
  | Loc_regions of (Cerb_position.t * Cerb_position.t) list * cursor
```
-/

/-- Cursor within a location
    Corresponds to: cursor in cerb_location.ml -/
inductive Cursor where
  | noCursor
  | pointCursor (pos : Pos)
  | regionCursor (start : Pos) (end_ : Pos)
  deriving Repr, BEq, Inhabited

/-- Source location
    Corresponds to: t in cerb_location.ml
    Audited: 2025-01-07
    Deviations: None -/
inductive Loc.t where
  | unknown
  | other (desc : String)
  | point (pos : Pos)
  | region (start : Pos) (end_ : Pos) (cursor : Cursor)
  | regions (regions : List (Pos × Pos)) (cursor : Cursor)
  deriving Repr, BEq, Inhabited

/-- Abbreviation for backwards compatibility -/
abbrev Loc := Loc.t

/-! ## BMC Annotation

Corresponds to: annot.lem:7-8
```lem
type bmc_annot =
  | Abmc_id of nat
```
-/

/-- BMC annotation
    Corresponds to: bmc_annot in annot.lem:7-8
    Audited: 2025-12-31
    Deviations: None -/
inductive BmcAnnot where
  | id (n : Nat)
  deriving Repr, BEq, Inhabited

/-! ## Attributes (C2X)

Corresponds to: annot.lem:10-17
```lem
type attribute = <|
  attr_ns: maybe Symbol.identifier;
  attr_id: Symbol.identifier;
  attr_args: list (Loc.t * string * list (Loc.t * string));
|>
type attributes = | Attrs of list attribute
```
-/

/-- C2X attribute argument (internal helper)
    Represents one element of attr_args in annot.lem:13: (Loc.t * string * list (Loc.t * string)) -/
structure AttrArg where
  loc : Loc
  arg : String
  tokens : List (Loc × String) := []
  deriving Repr, BEq, Inhabited

/-- C2X attribute
    Corresponds to: attribute in annot.lem:10-14
    Audited: 2025-12-31
    Deviations: Uses String for identifier names -/
structure Attribute where
  /-- Namespace (e.g., "cerb" in [[cerb::magic]]) -/
  ns : Option String := none
  /-- Attribute identifier -/
  id : String
  /-- Attribute arguments -/
  args : List AttrArg := []
  deriving Repr, BEq, Inhabited

/-- C2X attributes list
    Corresponds to: attributes in annot.lem:16-17
    Audited: 2025-12-31
    Deviations: None -/
structure Attributes where
  attrs : List Attribute := []
  deriving Repr, BEq, Inhabited

/-- Empty attributes (internal helper)
    Corresponds to: no_attributes in annot.lem:23-25 -/
def Attributes.empty : Attributes := ⟨[]⟩

/-! ## Loop ID

Corresponds to: annot.lem:31
```lem
type loop_id = nat
```
-/

/-- Loop identifier
    Corresponds to: loop_id in annot.lem:31
    Audited: 2025-12-31
    Deviations: None -/
abbrev LoopId := Nat

/-! ## Label Annotation

Corresponds to: annot.lem:33-44
```lem
type label_annot =
  | LAloop of loop_id
  | LAloop_continue of loop_id
  | LAloop_break of loop_id
  | LAreturn
  | LAswitch
  | LAcase
  | LAdefault
  | LAactual_label
```
-/

/-- Label annotation - records where a label comes from
    Corresponds to: label_annot in annot.lem:33-44
    Audited: 2025-12-31
    Deviations: None -/
inductive LabelAnnot where
  | loop (id : LoopId)
  | loopContinue (id : LoopId)
  | loopBreak (id : LoopId)
  | return_  -- when an Esave is annotated with this it indicates it is the return label
  | switch
  | case
  | default
  | actualLabel
  deriving Repr, BEq, Inhabited

/-! ## Cerberus Attribute

Corresponds to: annot.lem:59-61
```lem
type cerb_attribute =
  | ACerb_with_address of integer
  | ACerb_hidden
```
-/

/-- Cerberus-specific attribute
    Corresponds to: cerb_attribute in annot.lem:59-61
    Audited: 2025-12-31
    Deviations: None -/
inductive CerbAttribute where
  | withAddress (addr : Int)
  | hidden
  deriving Repr, BEq, Inhabited

/-! ## Value Annotation

Corresponds to: annot.lem:63-64
```lem
type value_annot =
  | Ainteger of IntegerType.integerType
```
-/

/-- Value annotation
    Corresponds to: value_annot in annot.lem:63-64
    Audited: 2025-12-31
    Deviations: None -/
inductive ValueAnnot where
  | integer (ity : IntegerType)
  deriving Repr, BEq, Inhabited

/-! ## Annotation

Corresponds to: annot.lem:66-81
```lem
type annot =
  | Astd of string
  | Aloc of Loc.t
  | Auid of string
  | Amarker of nat
  | Amarker_object_types of nat
  | Abmc of bmc_annot
  | Aattrs of attributes
  | Atypedef of Symbol.sym
  | Alabel of label_annot
  | Acerb of cerb_attribute
  | Avalue of value_annot
  | Ainlined_label of (Loc.t * Symbol.sym * label_annot)
  | Astmt
  | Aexpr
```
-/

-- Forward declaration for Sym (to avoid circular import)
-- In practice, we store the symbol ID as a Nat
/-- Annotation kinds
    Corresponds to: annot in annot.lem:66-81
    Audited: 2025-12-31
    Deviations: Atypedef uses Nat (symbol ID) instead of Symbol.sym -/
inductive Annot where
  | std (s : String)                    -- ISO C11 Standard Annotation
  | loc (l : Loc)                       -- C source location
  | uid (id : String)                   -- Unique ID (string in Cerberus)
  | marker (n : Nat)                    -- Marker
  | markerObjectTypes (n : Nat)         -- Marker for object types
  | bmc (a : BmcAnnot)                  -- BMC annotation
  | attrs (a : Attributes)              -- C2X attributes
  | typedef (symId : Nat)               -- Typedef symbol ID
  | label (a : LabelAnnot)              -- Label annotation
  | cerb (a : CerbAttribute)            -- Cerberus attribute
  | value (a : ValueAnnot)              -- Value annotation
  | inlinedLabel (loc : Loc) (symId : Nat) (label : LabelAnnot)  -- Inlined label
  | stmt                                -- CN: marks Ail statement boundary
  | expr                                -- CN: marks Ail expression boundary
  deriving Repr, BEq, Inhabited

/-- List of annotations (internal helper)
    Used throughout Core AST; Cerberus uses `list annot` directly -/
abbrev Annots := List Annot

/-! ## Identifier Item Kind

Corresponds to: annot.lem:84-86
```lem
type identifier_item_kind =
  | Marker_Local
  | Marker_Global
```
-/

/-- Identifier item kind for marker environment
    Corresponds to: identifier_item_kind in annot.lem:84-86
    Audited: 2025-12-31
    Deviations: None -/
inductive IdentifierItemKind where
  | local
  | global
  deriving Repr, BEq, Inhabited

/-! ## Loop Attribute

Corresponds to: annot.lem:91-95
```lem
type loop_attribute =
  <| marker_id : nat;
     attributes : attributes;
     loc_condition : Loc.t;
     loc_loop : Loc.t; |>
```
-/

/-- Loop attribute information
    Corresponds to: loop_attribute in annot.lem:91-95
    Audited: 2025-12-31
    Deviations: None -/
structure LoopAttribute where
  markerId : Nat
  attributes : Attributes
  locCondition : Loc
  locLoop : Loc
  deriving Repr, BEq, Inhabited

/-! ## Loop Attributes Map

Corresponds to: annot.lem:97
```lem
type loop_attributes = map loop_id loop_attribute
```
-/

/-- Map from loop ID to loop attributes
    Corresponds to: loop_attributes in annot.lem:97
    Audited: 2025-12-31
    Deviations: Uses List instead of map -/
abbrev LoopAttributes := List (LoopId × LoopAttribute)

/-! ## Helper Functions -/

/-- Get location from annotations if present
    Corresponds to: get_loc in annot.lem:100-133
    Audited: 2025-12-31
    Deviations: None -/
def Annots.getLoc (annots : Annots) : Option Loc :=
  annots.findSome? fun
    | .loc l => some l
    | _ => none

/-- Get UID from annotations if present
    Corresponds to: get_uid in annot.lem:267-300
    Audited: 2025-12-31
    Deviations: None -/
def Annots.getUid (annots : Annots) : Option String :=
  annots.findSome? fun
    | .uid id => some id
    | _ => none

/-- Get marker from annotations if present
    Corresponds to: get_marker in annot.lem:229-241
    Audited: 2025-12-31
    Deviations: None -/
def Annots.getMarker (annots : Annots) : Option Nat :=
  annots.findSome? fun
    | .marker n => some n
    | _ => none

/-- Get label annotation if present
    Corresponds to: get_label_annot in annot.lem:258-264
    Audited: 2025-12-31
    Deviations: None -/
def Annots.getLabelAnnot (annots : Annots) : Option LabelAnnot :=
  annots.findSome? fun
    | .label a => some a
    | _ => none

/-- Check if annotations indicate a return label
    Corresponds to: is_return in annot.lem:303-305
    Audited: 2025-12-31
    Deviations: None -/
def Annots.isReturn (annots : Annots) : Bool :=
  annots.getLabelAnnot == some .return_

/-- Check if annotations indicate a loop break
    Corresponds to: is_loop_break in annot.lem:307-312
    Audited: 2025-12-31
    Deviations: None -/
def Annots.isLoopBreak (annots : Annots) : Bool :=
  match annots.getLabelAnnot with
  | some (.loopBreak _) => true
  | _ => false

/-- Get integer type annotation if present.
    Corresponds to: integer_annot in cn/lib/wellTyped.ml lines 1592-1600

    CN's implementation:
      let integer_annot annots =
        match List.filter_map is_integer_annot annots with
        | [] -> None
        | [ ity ] -> Some ity
        | _ -> assert false
    -/
def Annots.getIntegerAnnot (annots : Annots) : Option IntegerType :=
  annots.findSome? fun
    | .value (.integer ity) => some ity
    | _ => none

end CerbLean.Core
