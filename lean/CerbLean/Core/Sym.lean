/-
  Symbols and identifiers for Core IR
  Corresponds to: cerberus/frontend/model/symbol.lem
  Audited: 2025-12-31
  Deviations: None
-/

import CerbLean.Core.Annot

namespace CerbLean.Core

/-! ## Identifier

Corresponds to: identifier in symbol.lem lines 4-5
```lem
type identifier =
  | Identifier of Loc.t * string
```
-/

/-- C identifier (struct/union member names, etc.)
    Corresponds to: identifier in symbol.lem lines 4-5
    Audited: 2025-12-31
    Deviations: None -/
structure Identifier where
  /-- Source location of the identifier -/
  loc : Loc
  /-- The identifier string -/
  name : String
  deriving Repr, Inhabited

/-- Equality for identifiers is based on name only (matching Cerberus idEqual) -/
instance : BEq Identifier where
  beq a b := a.name == b.name

instance : Hashable Identifier where
  hash a := hash a.name

/-! ## Digest

Corresponds to: digest in symbol.lem lines 40-51
A digest is a translation unit identifier (MD5 hash in Cerberus).
We represent it as a String for simplicity.
-/

/-- Translation unit digest
    Corresponds to: digest in symbol.lem lines 40-51
    Audited: 2025-12-31
    Deviations: Represented as String instead of Digest.t -/
abbrev Digest := String

/-! ## Symbol Description

Corresponds to: symbol_description in symbol.lem lines 77-88
```lem
type symbol_description =
  | SD_None
  | SD_unnamed_tag of Loc.t
  | SD_Id of string
  | SD_CN_Id of string
  | SD_ObjectAddress of string
  | SD_Return
  | SD_FunArgValue of string
  | SD_FunArg of Loc.t * nat
```
-/

/-- Symbol description for debugging/naming purposes
    Corresponds to: symbol_description in symbol.lem lines 77-88
    Audited: 2025-12-31
    Deviations: None -/
inductive SymbolDescription where
  | none_
  | unnamedTag (loc : Loc)
  | id (name : String)
  | cnId (name : String)
  | objectAddress (name : String)
  | return_
  | funArgValue (name : String)
  | funArg (loc : Loc) (index : Nat)
  deriving Repr, BEq, Inhabited

/-! ## Symbol

Corresponds to: sym in symbol.lem lines 126-127
```lem
type sym =
  Symbol of digest * nat * symbol_description
```
-/

/-- Symbol identifier (unique ID for variables, functions, etc.)
    Corresponds to: sym in symbol.lem lines 126-127
    Audited: 2025-12-31
    Deviations: Added `name` field for convenience (derived from description) -/
structure Sym where
  /-- Translation unit digest -/
  digest : Digest := ""
  /-- Unique numeric identifier within the translation unit -/
  id : Nat
  /-- Symbol description -/
  description : SymbolDescription := .none_
  /-- Cached name for display (derived from description or generated) -/
  name : Option String := none
  deriving Repr, Inhabited

/-- Symbols are equal if they have the same digest and id -/
instance : BEq Sym where
  beq a b := a.digest == b.digest && a.id == b.id

instance : Hashable Sym where
  hash s := mixHash (hash s.digest) (hash s.id)

/-! ## Symbol Prefix

Corresponds to: prefix in symbol.lem (commented out in Cerberus)
Used for allocation naming.
-/

/-- Symbol prefix for allocation naming
    Corresponds to: prefix in symbol.lem (commented out)
    Audited: 2025-12-31
    Deviations: Simplified to just a string -/
structure SymPrefix where
  val : String
  deriving Repr, BEq, Inhabited

end CerbLean.Core
