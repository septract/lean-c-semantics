/-
  Type layout computation: sizeof, alignof, offsetsof
  Based on cerberus/memory/concrete/impl_mem.ml layout calculations
-/

import CToLean.Core.Ctype
import CToLean.Core.File
import Std.Data.HashMap

namespace CToLean.Memory

open CToLean.Core

/-! ## Target Configuration

These values match typical LP64 (Linux/macOS 64-bit) ABI.
Cerberus gets these from the implementation file.
-/

/-- Target pointer size in bytes -/
def targetPtrSize : Nat := 8

/-- Target maximum alignment -/
def targetMaxAlign : Nat := 16

/-! ## Integer Type Sizes -/

/-- Size of integer base kind in bytes -/
def intBaseKindSize : IntBaseKind → Nat
  | .ichar => 1
  | .short => 2
  | .int_ => 4
  | .long => 8      -- LP64
  | .longLong => 8
  | .intN n => (n + 7) / 8
  | .intLeastN n =>
    if n ≤ 8 then 1
    else if n ≤ 16 then 2
    else if n ≤ 32 then 4
    else 8
  | .intFastN n =>
    if n ≤ 8 then 1
    else if n ≤ 16 then 2
    else if n ≤ 32 then 4
    else 8
  | .intmax => 8
  | .intptr => targetPtrSize

/-- Size of integer type in bytes -/
def integerTypeSize : IntegerType → Nat
  | .char => 1
  | .bool => 1
  | .signed k => intBaseKindSize k
  | .unsigned k => intBaseKindSize k
  | .enum _ => 4  -- Enums are int-sized
  | .size_t => targetPtrSize
  | .wchar_t => 4
  | .wint_t => 4
  | .ptrdiff_t => targetPtrSize
  | .ptraddr_t => targetPtrSize

/-- Size of real floating type in bytes -/
def realFloatingTypeSize : RealFloatingType → Nat
  | .float => 4
  | .double => 8
  | .longDouble => 16  -- x86-64 long double

/-- Size of floating type in bytes -/
def floatingTypeSize : FloatingType → Nat
  | .realFloating ty => realFloatingTypeSize ty

/-- Size of basic type in bytes -/
def basicTypeSize : BasicType → Nat
  | .integer ity => integerTypeSize ity
  | .floating fty => floatingTypeSize fty

/-! ## Alignment -/

/-- Alignment of integer base kind -/
def intBaseKindAlign : IntBaseKind → Nat
  | .ichar => 1
  | .short => 2
  | .int_ => 4
  | .long => 8
  | .longLong => 8
  | .intN n => min ((n + 7) / 8) targetMaxAlign
  | .intLeastN n =>
    if n ≤ 8 then 1
    else if n ≤ 16 then 2
    else if n ≤ 32 then 4
    else 8
  | .intFastN n =>
    if n ≤ 8 then 1
    else if n ≤ 16 then 2
    else if n ≤ 32 then 4
    else 8
  | .intmax => 8
  | .intptr => targetPtrSize

/-- Alignment of integer type -/
def integerTypeAlign : IntegerType → Nat
  | .char => 1
  | .bool => 1
  | .signed k => intBaseKindAlign k
  | .unsigned k => intBaseKindAlign k
  | .enum _ => 4
  | .size_t => targetPtrSize
  | .wchar_t => 4
  | .wint_t => 4
  | .ptrdiff_t => targetPtrSize
  | .ptraddr_t => targetPtrSize

/-- Alignment of real floating type -/
def realFloatingTypeAlign : RealFloatingType → Nat
  | .float => 4
  | .double => 8
  | .longDouble => 16

/-- Alignment of floating type -/
def floatingTypeAlign : FloatingType → Nat
  | .realFloating ty => realFloatingTypeAlign ty

/-- Alignment of basic type -/
def basicTypeAlign : BasicType → Nat
  | .integer ity => integerTypeAlign ity
  | .floating fty => floatingTypeAlign fty

/-! ## Type Environment

We need access to struct/union definitions for layout.
-/

/-- Type environment containing struct/union definitions -/
structure TypeEnv where
  /-- Tag definitions: tag symbol -> (loc, def) -/
  tagDefs : TagDefs
  deriving Inhabited

/-- Look up a tag definition -/
def TypeEnv.lookupTag (env : TypeEnv) (tag : Sym) : Option TagDef :=
  env.tagDefs.find? (·.1 == tag) |>.map (·.2.2)

/-- Create type environment from a Core file -/
def TypeEnv.fromFile (file : File) : TypeEnv :=
  { tagDefs := file.tagDefs }

/-! ## Sizeof and Alignof

These require type environment for struct/union types.
-/

/-- Round up to alignment -/
def alignUp (n : Nat) (align : Nat) : Nat :=
  if align == 0 then n
  else ((n + align - 1) / align) * align

mutual
  /-- Compute sizeof for inner ctype -/
  partial def sizeof_ (env : TypeEnv) : Ctype_ → Nat
    | .void => 0  -- void has size 0
    | .basic bty => basicTypeSize bty
    | .array elemTy (some n) => n * sizeof_ env elemTy
    | .array _ none => 0  -- Flexible array member
    | .function .. => 0  -- Functions don't have size
    | .functionNoParams .. => 0
    | .pointer .. => targetPtrSize
    | .atomic ty => sizeof_ env ty
    | .struct_ tag =>
      match env.lookupTag tag with
      | some (.struct_ members _) => structSize env members
      | _ => 0
    | .union_ tag =>
      match env.lookupTag tag with
      | some (.union_ members) => unionSize env members
      | _ => 0
    | .byte => 1

  /-- Compute sizeof for a type -/
  partial def sizeof (env : TypeEnv) (ct : Ctype) : Nat :=
    sizeof_ env ct.ty

  /-- Compute alignof for inner ctype -/
  partial def alignof_ (env : TypeEnv) : Ctype_ → Nat
    | .void => 1
    | .basic bty => basicTypeAlign bty
    | .array elemTy _ => alignof_ env elemTy
    | .function .. => 1
    | .functionNoParams .. => 1
    | .pointer .. => targetPtrSize
    | .atomic ty => alignof_ env ty
    | .struct_ tag =>
      match env.lookupTag tag with
      | some (.struct_ members _) => structAlign env members
      | _ => 1
    | .union_ tag =>
      match env.lookupTag tag with
      | some (.union_ members) => unionAlign env members
      | _ => 1
    | .byte => 1

  /-- Compute alignof for a type -/
  partial def alignof (env : TypeEnv) (ct : Ctype) : Nat :=
    alignof_ env ct.ty

  /-- Compute struct size including padding and tail padding -/
  partial def structSize (env : TypeEnv) (members : List FieldDef) : Nat :=
    let (endOffset, maxAlign) := members.foldl (init := (0, 1)) fun (offset, maxA) m =>
      let memberAlign := alignof env m.ty
      let alignedOffset := alignUp offset memberAlign
      let newOffset := alignedOffset + sizeof env m.ty
      (newOffset, max maxA memberAlign)
    alignUp endOffset maxAlign

  /-- Compute struct alignment (max of member alignments) -/
  partial def structAlign (env : TypeEnv) (members : List FieldDef) : Nat :=
    members.foldl (init := 1) fun acc m => max acc (alignof env m.ty)

  /-- Compute union size (max of member sizes, aligned to max alignment) -/
  partial def unionSize (env : TypeEnv) (members : List FieldDef) : Nat :=
    let maxSize := members.foldl (init := 0) fun acc m => max acc (sizeof env m.ty)
    let maxA := unionAlign env members
    alignUp maxSize maxA

  /-- Compute union alignment (max of member alignments) -/
  partial def unionAlign (env : TypeEnv) (members : List FieldDef) : Nat :=
    members.foldl (init := 1) fun acc m => max acc (alignof env m.ty)
end

/-! ## Member Offsets -/

/-- Compute member offsets for a struct -/
def structOffsets (env : TypeEnv) (members : List FieldDef) : List (Identifier × Nat) :=
  let (_, offsets) := members.foldl (init := (0, [])) fun (offset, acc) m =>
    let memberAlign := alignof env m.ty
    let alignedOffset := alignUp offset memberAlign
    let newOffset := alignedOffset + sizeof env m.ty
    (newOffset, acc ++ [(m.name, alignedOffset)])
  offsets

/-- Get member offset from tag definition -/
def memberOffset (env : TypeEnv) (tag : Sym) (member : Identifier) : Option Nat :=
  match env.lookupTag tag with
  | some (.struct_ members _) =>
    let offsets := structOffsets env members
    offsets.find? (·.1 == member) |>.map (·.2)
  | some (.union_ _) =>
    -- All union members start at offset 0
    some 0
  | none => none

/-- Get member type from tag definition -/
def memberType (env : TypeEnv) (tag : Sym) (member : Identifier) : Option Ctype :=
  match env.lookupTag tag with
  | some (.struct_ members _) =>
    members.find? (·.name == member) |>.map (·.ty)
  | some (.union_ members) =>
    members.find? (·.name == member) |>.map (·.ty)
  | none => none

end CToLean.Memory
