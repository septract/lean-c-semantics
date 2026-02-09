/-
  Type layout computation: sizeof, alignof, offsetsof
  Corresponds to: cerberus/ocaml_frontend/ocaml_implementation.ml and impl_mem.ml

  This implements the LP64 (x86_64-apple-darwin) ABI for:
  - Type sizes (sizeof)
  - Type alignments (alignof)
  - Struct member offsets (offsetsof)

  The layout rules match Cerberus's DefaultImpl in ocaml_implementation.ml.
  CRITICAL: These must match Cerberus exactly for differential testing.
-/

import CerbLean.Core.Ctype
import CerbLean.Core.File
import Std.Data.HashMap

namespace CerbLean.Memory

open CerbLean.Core

/-! ## Target Configuration

Corresponds to: DefaultImpl in ocaml_implementation.ml:114-274
These values match the x86_64-apple-darwin LP64 ABI that Cerberus uses.
Audited: 2026-01-01
-/

/-- Target pointer size in bytes.
    Corresponds to: sizeof_pointer in ocaml_implementation.ml:118-119
    Audited: 2026-01-01
    Deviations: None -/
def targetPtrSize : Nat := 8

/-- Target maximum alignment.
    Corresponds to: max_alignment in ocaml_implementation.ml:151-152
    Audited: 2026-02-09
    Deviations: None -/
def targetMaxAlign : Nat := 8

/-! ## Integer Type Sizes

Corresponds to: sizeof_ity in ocaml_implementation.ml:173-204
-/

/-- Size of integer base kind in bytes.
    Corresponds to: sizeof_ity in ocaml_implementation.ml:173-204
    Audited: 2026-01-01
    Deviations: None (LP64 ABI) -/
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

/-- Size of integer type in bytes.
    Corresponds to: sizeof_ity in ocaml_implementation.ml:173-204
    Audited: 2026-01-01
    Deviations: None -/
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

/-- Check if integer type is signed.
    Corresponds to: checking signedness in impl_mem.ml:2379-2398
    Audited: 2026-01-06 -/
def isSignedIntegerType : IntegerType → Bool
  | .char => true  -- Assuming signed char (implementation-defined)
  | .bool => false
  | .signed _ => true
  | .unsigned _ => false
  | .enum _ => true  -- Enums are signed int
  | .size_t => false
  | .wchar_t => false  -- Implementation-defined, assuming unsigned
  | .wint_t => true
  | .ptrdiff_t => true
  | .ptraddr_t => false

/-- Maximum value for an integer type.
    Corresponds to: max_ival in impl_mem.ml:2367-2403
    Audited: 2026-01-06 -/
def integerTypeMax (ity : IntegerType) : Nat :=
  let n := integerTypeSize ity
  if isSignedIntegerType ity then
    2 ^ (8 * n - 1) - 1  -- 2^(bits-1) - 1
  else
    2 ^ (8 * n) - 1      -- 2^bits - 1

/-- Minimum value for an integer type.
    Corresponds to: min_ival in impl_mem.ml:2405-2437
    Audited: 2026-01-06 -/
def integerTypeMin (ity : IntegerType) : Int :=
  let n := integerTypeSize ity
  if isSignedIntegerType ity then
    -(2 ^ (8 * n - 1) : Int)  -- -2^(bits-1)
  else
    0

/-- Size of real floating type in bytes.
    Corresponds to: sizeof_fty in ocaml_implementation.ml:206-212
    Audited: 2026-01-01
    Deviations: None (Cerberus uses 8 for all floating types) -/
def realFloatingTypeSize : RealFloatingType → Nat
  | .float => 8       -- Cerberus uses 8 (stores float as double)
  | .double => 8
  | .longDouble => 8  -- Cerberus uses 8 (same as double)

/-- Size of floating type in bytes.
    Audited: 2026-01-01
    Deviations: None -/
def floatingTypeSize : FloatingType → Nat
  | .realFloating ty => realFloatingTypeSize ty

/-- Size of basic type in bytes.
    Audited: 2026-01-01
    Deviations: None -/
def basicTypeSize : BasicType → Nat
  | .integer ity => integerTypeSize ity
  | .floating fty => floatingTypeSize fty

/-! ## Alignment

Corresponds to: alignof_ity, alignof_fty in ocaml_implementation.ml:214-253
-/

/-- Alignment of integer base kind.
    Corresponds to: alignof_ity in ocaml_implementation.ml:214-245
    Audited: 2026-01-01
    Deviations: None (LP64 ABI) -/
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

/-- Alignment of integer type.
    Corresponds to: alignof_ity in ocaml_implementation.ml:214-245
    Audited: 2026-01-01
    Deviations: None -/
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

/-- Alignment of real floating type.
    Corresponds to: alignof_fty in ocaml_implementation.ml:247-253
    Audited: 2026-01-01
    Deviations: None (Cerberus uses 8 for all floating types) -/
def realFloatingTypeAlign : RealFloatingType → Nat
  | .float => 8       -- Cerberus uses 8 (stores float as double)
  | .double => 8
  | .longDouble => 8  -- Cerberus uses 8 (same as double)

/-- Alignment of floating type.
    Audited: 2026-01-01
    Deviations: None -/
def floatingTypeAlign : FloatingType → Nat
  | .realFloating ty => realFloatingTypeAlign ty

/-- Alignment of basic type.
    Audited: 2026-01-01
    Deviations: None -/
def basicTypeAlign : BasicType → Nat
  | .integer ity => integerTypeAlign ity
  | .floating fty => floatingTypeAlign fty

/-! ## Type Environment

We need access to struct/union definitions for layout.
Corresponds to: Tags.tagDefs() in Cerberus (global mutable state)
-/

/-- Type environment containing struct/union definitions.
    Corresponds to: Tags.tagDefs() in Cerberus
    Audited: 2026-01-01
    Deviations: Explicit parameter instead of global state -/
structure TypeEnv where
  /-- Tag definitions: tag symbol -> (loc, def) -/
  tagDefs : TagDefs
  deriving Inhabited

/-- Look up a tag definition.
    Audited: 2026-01-01
    Deviations: None -/
def TypeEnv.lookupTag (env : TypeEnv) (tag : Sym) : Option TagDef :=
  env.tagDefs.find? (·.1 == tag) |>.map (·.2.2)

/-- Create type environment from a Core file.
    Audited: 2026-01-01
    Deviations: None -/
def TypeEnv.fromFile (file : File) : TypeEnv :=
  { tagDefs := file.tagDefs }

/-! ## Sizeof and Alignof

Corresponds to: sizeof, alignof in impl_mem.ml (which calls the implementation module)
and offsetsof for struct layout computation.
-/

/-- Round up to alignment.
    Audited: 2026-01-01
    Deviations: None -/
def alignUp (n : Nat) (align : Nat) : Nat :=
  if align == 0 then n
  else ((n + align - 1) / align) * align

mutual
  /-- Compute sizeof for inner ctype.
      Corresponds to: sizeof in impl_mem.ml:2492
      Audited: 2026-01-01
      Deviations: None -/
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
      | some (.union_ _) => panic! s!"sizeof: expected struct but found union for tag {tag.name}"
      | none => panic! s!"sizeof: undefined struct tag {tag.name}"
    | .union_ tag =>
      match env.lookupTag tag with
      | some (.union_ members) => unionSize env members
      | some (.struct_ _ _) => panic! s!"sizeof: expected union but found struct for tag {tag.name}"
      | none => panic! s!"sizeof: undefined union tag {tag.name}"
    | .byte => 1

  /-- Compute sizeof for a type.
      Corresponds to: sizeof in impl_mem.ml:2492
      Audited: 2026-01-01
      Deviations: None -/
  partial def sizeof (env : TypeEnv) (ct : Ctype) : Nat :=
    sizeof_ env ct.ty

  /-- Compute alignof for inner ctype.
      Corresponds to: alignof in impl_mem.ml:2494
      Audited: 2026-01-01
      Deviations: None -/
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
      | some (.union_ _) => panic! s!"alignof: expected struct but found union for tag {tag.name}"
      | none => panic! s!"alignof: undefined struct tag {tag.name}"
    | .union_ tag =>
      match env.lookupTag tag with
      | some (.union_ members) => unionAlign env members
      | some (.struct_ _ _) => panic! s!"alignof: expected union but found struct for tag {tag.name}"
      | none => panic! s!"alignof: undefined union tag {tag.name}"
    | .byte => 1

  /-- Compute alignof for a type.
      Corresponds to: alignof in impl_mem.ml:2494
      Audited: 2026-01-01
      Deviations: None -/
  partial def alignof (env : TypeEnv) (ct : Ctype) : Nat :=
    alignof_ env ct.ty

  /-- Compute struct size including padding and tail padding.
      Corresponds to: sizeof for Struct case, using offsetsof
      Audited: 2026-01-01
      Deviations: None -/
  partial def structSize (env : TypeEnv) (members : List FieldDef) : Nat :=
    let (endOffset, maxAlign) := members.foldl (init := (0, 1)) fun (offset, maxA) m =>
      let memberAlign := alignof env m.ty
      let alignedOffset := alignUp offset memberAlign
      let newOffset := alignedOffset + sizeof env m.ty
      (newOffset, max maxA memberAlign)
    alignUp endOffset maxAlign

  /-- Compute struct alignment (max of member alignments).
      Audited: 2026-01-01
      Deviations: None -/
  partial def structAlign (env : TypeEnv) (members : List FieldDef) : Nat :=
    members.foldl (init := 1) fun acc m => max acc (alignof env m.ty)

  /-- Compute union size (max of member sizes, aligned to max alignment).
      Audited: 2026-01-01
      Deviations: None -/
  partial def unionSize (env : TypeEnv) (members : List FieldDef) : Nat :=
    let maxSize := members.foldl (init := 0) fun acc m => max acc (sizeof env m.ty)
    let maxA := unionAlign env members
    alignUp maxSize maxA

  /-- Compute union alignment (max of member alignments).
      Audited: 2026-01-01
      Deviations: None -/
  partial def unionAlign (env : TypeEnv) (members : List FieldDef) : Nat :=
    members.foldl (init := 1) fun acc m => max acc (alignof env m.ty)
end

/-! ## Member Offsets

Corresponds to: offsetsof in impl_mem.ml
-/

/-- Compute member offsets for a struct.
    Corresponds to: offsetsof in impl_mem.ml:98-127
    Audited: 2026-01-06
    Deviations: Returns list instead of (list, last_offset) -/
def structOffsets (env : TypeEnv) (members : List FieldDef) : List (Identifier × Nat) :=
  let (_, offsets) := members.foldl (init := (0, [])) fun (offset, acc) m =>
    let memberAlign := alignof env m.ty
    let alignedOffset := alignUp offset memberAlign
    let newOffset := alignedOffset + sizeof env m.ty
    (newOffset, acc ++ [(m.name, alignedOffset)])
  offsets

/-- Compute member info (name, type, offset) for a struct.
    Corresponds to: offsetsof in impl_mem.ml:98-127
    Returns: [(memb_ident, memb_ty, memb_offset)] matching Cerberus exactly.
    Audited: 2026-01-06
    Deviations: None -/
def structMemberInfo (env : TypeEnv) (members : List FieldDef) : List (Identifier × Ctype × Nat) :=
  let (_, info) := members.foldl (init := (0, [])) fun (offset, acc) m =>
    let memberAlign := alignof env m.ty
    let alignedOffset := alignUp offset memberAlign
    let newOffset := alignedOffset + sizeof env m.ty
    (newOffset, acc ++ [(m.name, m.ty, alignedOffset)])
  info

/-- Get member offset from tag definition.
    Corresponds to: offsetof_ival in impl_mem.ml
    Audited: 2026-01-01
    Deviations: None -/
def memberOffset (env : TypeEnv) (tag : Sym) (member : Identifier) : Nat :=
  match env.lookupTag tag with
  | some (.struct_ members _) =>
    let offsets := structOffsets env members
    match offsets.find? (·.1 == member) with
    | some (_, offset) => offset
    | none => panic! s!"memberOffset: member {member.name} not found in struct {tag.name}"
  | some (.union_ _) =>
    -- All union members start at offset 0
    0
  | none => panic! s!"memberOffset: undefined tag {tag.name}"

/-- Get member type from tag definition.
    Audited: 2026-01-01
    Deviations: None -/
def memberType (env : TypeEnv) (tag : Sym) (member : Identifier) : Ctype :=
  match env.lookupTag tag with
  | some (.struct_ members _) =>
    match members.find? (·.name == member) with
    | some field => field.ty
    | none => panic! s!"memberType: member {member.name} not found in struct {tag.name}"
  | some (.union_ members) =>
    match members.find? (·.name == member) with
    | some field => field.ty
    | none => panic! s!"memberType: member {member.name} not found in union {tag.name}"
  | none => panic! s!"memberType: undefined tag {tag.name}"

end CerbLean.Memory
