/-
  Memory model interface
  Corresponds to: cerberus/ocaml_frontend/memory_model.ml:22-257

  This defines the abstract interface for memory operations.
  The Memory module type in Cerberus (memory_model.ml) defines
  the signature that all memory models must implement.

  CRITICAL: This interface must match Cerberus exactly for differential testing.
-/

import CToLean.Memory.Types
import CToLean.Memory.Layout

namespace CToLean.Memory

open CToLean.Core

/-! ## Pointer Value Constructors

Corresponds to: memory_model.ml:70-78
```ocaml
val null_ptrval: Ctype.ctype -> pointer_value
val fun_ptrval: Symbol.sym -> pointer_value
val concrete_ptrval: Nat_big_num.num -> Nat_big_num.num -> pointer_value
```
-/

/-- Create null pointer of given type.
    Corresponds to: null_ptrval in memory_model.ml:70
    Audited: 2026-01-01
    Deviations: None -/
def nullPtrval (ty : Ctype) : PointerValue :=
  { prov := .none, base := .null ty }

/-- Create function pointer.
    Corresponds to: fun_ptrval in memory_model.ml:71
    Audited: 2026-01-01
    Deviations: None -/
def funPtrval (sym : Sym) : PointerValue :=
  { prov := .none, base := .function sym }

/-- Create concrete pointer with allocation ID and address.
    Corresponds to: concrete_ptrval in memory_model.ml:74
    Audited: 2026-01-01
    Deviations: Takes allocId separately (Cerberus encodes in first num) -/
def concretePtrval (allocId : Nat) (addr : Nat) : PointerValue :=
  { prov := .some allocId, base := .concrete none addr }

/-! ## Integer Value Constructors

Corresponds to: memory_model.ml:132-141
```ocaml
val integer_ival: Nat_big_num.num -> integer_value
val max_ival: Ctype.integerType -> integer_value
val min_ival: Ctype.integerType -> integer_value
val sizeof_ival: Ctype.ctype -> integer_value
val alignof_ival: Ctype.ctype -> integer_value
```
-/

/-- Create integer value from literal.
    Corresponds to: integer_ival in memory_model.ml:134
    Audited: 2026-01-01
    Deviations: Takes Int instead of Nat_big_num (equivalent) -/
def integerIval (n : Int) : IntegerValue :=
  { val := n, prov := .none }

/-- Create integer value with provenance.
    Not in Cerberus interface - used internally for pointer-to-int casts.
    Audited: 2026-01-01
    Deviations: Extension for provenance tracking -/
def integerIvalWithProv (n : Int) (prov : Provenance) : IntegerValue :=
  { val := n, prov := prov }

/-! ## Integer Type Bounds

Corresponds to: memory_model.ml:135-136
```ocaml
val max_ival: Ctype.integerType -> integer_value
val min_ival: Ctype.integerType -> integer_value
```
-/

/-- Maximum value for an integer type.
    Corresponds to: max_ival in memory_model.ml:135
    Audited: 2026-01-01
    Deviations: None (LP64 assumptions match Cerberus) -/
def maxIval (_env : TypeEnv) (ity : IntegerType) : IntegerValue :=
  let size := integerTypeSize ity
  let bits := size * 8
  let maxVal : Int :=
    match ity with
    | .char => 127  -- Assuming signed char
    | .bool => 1
    | .signed _ => (2 ^ (bits - 1)) - 1
    | .unsigned _ => (2 ^ bits) - 1
    | .enum _ => (2 ^ 31) - 1  -- int range
    | .size_t => (2 ^ bits) - 1
    | .wchar_t => (2 ^ 31) - 1
    | .wint_t => (2 ^ 31) - 1
    | .ptrdiff_t => (2 ^ (bits - 1)) - 1
    | .ptraddr_t => (2 ^ bits) - 1
  integerIval maxVal

/-- Minimum value for an integer type.
    Corresponds to: min_ival in memory_model.ml:136
    Audited: 2026-01-01
    Deviations: None (LP64 assumptions match Cerberus) -/
def minIval (_env : TypeEnv) (ity : IntegerType) : IntegerValue :=
  let size := integerTypeSize ity
  let bits := size * 8
  let minVal : Int :=
    match ity with
    | .char => -128  -- Assuming signed char
    | .bool => 0
    | .signed _ => -(2 ^ (bits - 1))
    | .unsigned _ => 0
    | .enum _ => -(2 ^ 31)  -- int range
    | .size_t => 0
    | .wchar_t => -(2 ^ 31)
    | .wint_t => -(2 ^ 31)
    | .ptrdiff_t => -(2 ^ (bits - 1))
    | .ptraddr_t => 0
  integerIval minVal

/-- sizeof(ty) as integer value.
    Corresponds to: sizeof_ival in memory_model.ml:140
    Audited: 2026-01-01
    Deviations: None -/
def sizeofIval (env : TypeEnv) (ty : Ctype) : IntegerValue :=
  integerIval (sizeof env ty)

/-- alignof(ty) as integer value.
    Corresponds to: alignof_ival in memory_model.ml:141
    Audited: 2026-01-01
    Deviations: None -/
def alignofIval (env : TypeEnv) (ty : Ctype) : IntegerValue :=
  integerIval (alignof env ty)

/-! ## Memory Value Constructors

Corresponds to: memory_model.ml:181-189
```ocaml
val unspecified_mval: Ctype.ctype -> mem_value
val integer_value_mval: Ctype.integerType -> integer_value -> mem_value
val floating_value_mval: Ctype.floatingType -> floating_value -> mem_value
val pointer_mval: Ctype.ctype -> pointer_value -> mem_value
val array_mval: mem_value list -> mem_value
val struct_mval: Symbol.sym -> (Symbol.identifier * Ctype.ctype * mem_value) list -> mem_value
val union_mval: Symbol.sym -> Symbol.identifier -> mem_value -> mem_value
```
-/

/-- Create unspecified (uninitialized) memory value.
    Corresponds to: unspecified_mval in memory_model.ml:183
    Audited: 2026-01-01
    Deviations: None -/
def unspecifiedMval (ty : Ctype) : MemValue :=
  .unspecified ty

/-- Create integer memory value.
    Corresponds to: integer_value_mval in memory_model.ml:184
    Audited: 2026-01-01
    Deviations: None -/
def integerValueMval (ity : IntegerType) (v : IntegerValue) : MemValue :=
  .integer ity v

/-- Create floating memory value.
    Corresponds to: floating_value_mval in memory_model.ml:185
    Audited: 2026-01-01
    Deviations: None -/
def floatingValueMval (fty : FloatingType) (v : FloatingValue) : MemValue :=
  .floating fty v

/-- Create pointer memory value.
    Corresponds to: pointer_mval in memory_model.ml:186
    Audited: 2026-01-01
    Deviations: None -/
def pointerMval (ty : Ctype) (v : PointerValue) : MemValue :=
  .pointer ty v

/-- Create array memory value.
    Corresponds to: array_mval in memory_model.ml:187
    Audited: 2026-01-01
    Deviations: None -/
def arrayMval (elems : List MemValue) : MemValue :=
  .array elems

/-- Create struct memory value.
    Corresponds to: struct_mval in memory_model.ml:188
    Audited: 2026-01-01
    Deviations: None -/
def structMval (tag : Sym) (members : List (Identifier × Ctype × MemValue)) : MemValue :=
  .struct_ tag members

/-- Create union memory value.
    Corresponds to: union_mval in memory_model.ml:189
    Audited: 2026-01-01
    Deviations: None -/
def unionMval (tag : Sym) (member : Identifier) (val : MemValue) : MemValue :=
  .union_ tag member val

/-! ## Memory Interface

Corresponds to: Memory module type in memory_model.ml:22-257

This defines the core memory operations as a typeclass. The concrete
implementation is in Memory/Concrete.lean.

The Memory module signature in Cerberus defines:
- Types: pointer_value, integer_value, floating_value, mem_value, mem_state
- Memory actions: allocate_object, allocate_region, kill, load, store
- Pointer operations: eq/ne/lt/gt/le/ge_ptrval, diff_ptrval, array_shift, member_shift
- Casting: ptrfromint, intfromptr
- Memory operations: memcpy, memcmp, realloc

Audited: 2026-01-01
Deviations:
- No thread_id parameter (sequential only)
- No location parameter (tracked elsewhere)
- No Cerb_location (source tracking deferred)
-/

/-- Memory interface operations.
    Corresponds to: Memory module type in memory_model.ml:22-257 -/
class MemoryOps (m : Type → Type) where
  /-- Get the type environment -/
  getTypeEnv : m TypeEnv

  /-- Allocate memory for a typed object.
      Corresponds to: allocate_object in memory_model.ml:47-55
      - name: debug name for allocation (Symbol.prefix in Cerberus)
      - align: alignment constraint as integer value
      - ty: C type of allocation
      - requestedAddr: optional address (cerb::with_address attribute)
      - init: optional initial value (makes allocation read-only) -/
  allocateObject : String → IntegerValue → Ctype → Option Nat → Option MemValue → m PointerValue

  /-- Allocate raw memory region (malloc-style).
      Corresponds to: allocate_region in memory_model.ml:57-62
      - name: debug name
      - align: alignment constraint
      - size: size in bytes -/
  allocateRegion : String → IntegerValue → IntegerValue → m PointerValue

  /-- Load value from memory.
      Corresponds to: load in memory_model.ml:66
      Returns footprint (for race detection) and loaded value. -/
  load : Ctype → PointerValue → m (Footprint × MemValue)

  /-- Store value to memory.
      Corresponds to: store in memory_model.ml:67
      - ty: type being stored
      - isLocking: if true, locks as read-only after store (for string literals)
      - ptr: destination pointer
      - val: value to store
      Returns footprint of written bytes. -/
  store : Ctype → Bool → PointerValue → MemValue → m Footprint

  /-- Deallocate memory.
      Corresponds to: kill in memory_model.ml:64
      - isDynamic: true for free(), false for end of scope -/
  kill : Bool → PointerValue → m Unit

  /-- Pointer equality.
      Corresponds to: eq_ptrval in memory_model.ml:82 -/
  eqPtrval : PointerValue → PointerValue → m Bool

  /-- Pointer inequality.
      Corresponds to: ne_ptrval in memory_model.ml:83 -/
  nePtrval : PointerValue → PointerValue → m Bool

  /-- Pointer less than.
      Corresponds to: lt_ptrval in memory_model.ml:84 -/
  ltPtrval : PointerValue → PointerValue → m Bool

  /-- Pointer greater than.
      Corresponds to: gt_ptrval in memory_model.ml:85 -/
  gtPtrval : PointerValue → PointerValue → m Bool

  /-- Pointer less than or equal.
      Corresponds to: le_ptrval in memory_model.ml:86 -/
  lePtrval : PointerValue → PointerValue → m Bool

  /-- Pointer greater than or equal.
      Corresponds to: ge_ptrval in memory_model.ml:87 -/
  gePtrval : PointerValue → PointerValue → m Bool

  /-- Pointer difference (p1 - p2) / sizeof(elemTy).
      Corresponds to: diff_ptrval in memory_model.ml:88 -/
  diffPtrval : Ctype → PointerValue → PointerValue → m IntegerValue

  /-- Effectful pointer arithmetic with bounds checking.
      Corresponds to: eff_array_shift_ptrval in memory_model.ml:112 -/
  effArrayShiftPtrval : PointerValue → Ctype → IntegerValue → m PointerValue

  /-- Effectful struct member shift.
      Corresponds to: eff_member_shift_ptrval in memory_model.ml:113 -/
  effMemberShiftPtrval : PointerValue → Sym → Identifier → m PointerValue

  /-- Convert integer to pointer.
      Corresponds to: ptrfromint in memory_model.ml:98 -/
  ptrfromint : IntegerType → Ctype → IntegerValue → m PointerValue

  /-- Convert pointer to integer.
      Corresponds to: intfromptr in memory_model.ml:100 -/
  intfromptr : Ctype → IntegerType → PointerValue → m IntegerValue

  /-- Check if pointer is valid for dereferencing.
      Corresponds to: validForDeref_ptrval in memory_model.ml:93 -/
  validForDeref : Ctype → PointerValue → m Bool

  /-- Check if pointer is well-aligned.
      Corresponds to: isWellAligned_ptrval in memory_model.ml:94 -/
  isWellAligned : Ctype → PointerValue → m Bool

  /-- Memory copy.
      Corresponds to: memcpy in memory_model.ml:115 -/
  memcpy : PointerValue → PointerValue → IntegerValue → m PointerValue

  /-- Memory compare.
      Corresponds to: memcmp in memory_model.ml:116 -/
  memcmp : PointerValue → PointerValue → IntegerValue → m IntegerValue

  /-- Reallocate.
      Corresponds to: realloc in memory_model.ml:117 -/
  realloc : IntegerValue → PointerValue → IntegerValue → m PointerValue

/-! ## Pure Pointer Operations

Corresponds to: memory_model.ml:109-110
```ocaml
val array_shift_ptrval:  pointer_value -> Ctype.ctype -> integer_value -> pointer_value
val member_shift_ptrval: pointer_value -> Symbol.sym -> Symbol.identifier -> pointer_value
```

These are pure (non-effectful) versions that don't check bounds.
The effectful versions (eff_array_shift_ptrval, eff_member_shift_ptrval)
are in the MemoryOps typeclass and perform bounds checking.
-/

/-- Pure pointer arithmetic (no bounds check).
    Corresponds to: array_shift_ptrval in memory_model.ml:109
    Computes: ptr + (n * sizeof(elemTy))
    Audited: 2026-01-01
    Deviations: None -/
def arrayShiftPtrval (env : TypeEnv) (ptr : PointerValue) (elemTy : Ctype) (n : IntegerValue) : PointerValue :=
  match ptr.base with
  | .null ty => { ptr with base := .null ty }  -- NULL + n = NULL
  | .function sym => { ptr with base := .function sym }  -- Keep function ptr
  | .concrete unionMem addr =>
    let elemSize := sizeof env elemTy
    -- Handle negative offsets properly (n.val is Int, not Nat)
    let offset := n.val * elemSize
    let newAddr := (addr : Int) + offset
    -- Convert back to Nat (should be non-negative after bounds check)
    { ptr with base := .concrete unionMem newAddr.toNat }

/-- Pure struct member shift.
    Corresponds to: member_shift_ptrval in memory_model.ml:110
    Audited: 2026-01-01
    Deviations: None -/
def memberShiftPtrval (env : TypeEnv) (ptr : PointerValue) (tag : Sym) (member : Identifier) : PointerValue :=
  match ptr.base with
  | .null ty => { ptr with base := .null ty }
  | .function sym => { ptr with base := .function sym }
  | .concrete _ addr =>
    let offset := memberOffset env tag member
    -- For union members, track which member we're accessing
    let unionMem := match env.lookupTag tag with
      | some (.union_ _) => some member
      | _ => none
    { ptr with base := .concrete unionMem (addr + offset) }

end CToLean.Memory
