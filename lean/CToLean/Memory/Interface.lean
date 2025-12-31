/-
  Memory model interface
  Defines the abstract interface for memory operations.
  Based on cerberus/ocaml_frontend/memory_model.ml
-/

import CToLean.Memory.Types
import CToLean.Memory.Layout

namespace CToLean.Memory

open CToLean.Core

/-! ## Value Constructors -/

/-- Create null pointer of given type -/
def nullPtrval (ty : Ctype) : PointerValue :=
  { prov := .none, base := .null ty }

/-- Create function pointer -/
def funPtrval (sym : Sym) : PointerValue :=
  { prov := .none, base := .function sym }

/-- Create concrete pointer with allocation ID and address -/
def concretePtrval (allocId : Nat) (addr : Nat) : PointerValue :=
  { prov := .some allocId, base := .concrete none addr }

/-- Create integer value from literal -/
def integerIval (n : Int) : IntegerValue :=
  { val := n, prov := .none }

/-- Create integer value with provenance -/
def integerIvalWithProv (n : Int) (prov : Provenance) : IntegerValue :=
  { val := n, prov := prov }

/-! ## Integer Type Bounds -/

/-- Maximum value for an integer type -/
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

/-- Minimum value for an integer type -/
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

/-- sizeof(ty) as integer value -/
def sizeofIval (env : TypeEnv) (ty : Ctype) : IntegerValue :=
  integerIval (sizeof env ty)

/-- alignof(ty) as integer value -/
def alignofIval (env : TypeEnv) (ty : Ctype) : IntegerValue :=
  integerIval (alignof env ty)

/-! ## Memory Value Constructors -/

/-- Create unspecified (uninitialized) memory value -/
def unspecifiedMval (ty : Ctype) : MemValue :=
  .unspecified ty

/-- Create integer memory value -/
def integerValueMval (ity : IntegerType) (v : IntegerValue) : MemValue :=
  .integer ity v

/-- Create floating memory value -/
def floatingValueMval (fty : FloatingType) (v : FloatingValue) : MemValue :=
  .floating fty v

/-- Create pointer memory value -/
def pointerMval (ty : Ctype) (v : PointerValue) : MemValue :=
  .pointer ty v

/-- Create array memory value -/
def arrayMval (elems : List MemValue) : MemValue :=
  .array elems

/-- Create struct memory value -/
def structMval (tag : Sym) (members : List (Identifier × Ctype × MemValue)) : MemValue :=
  .struct_ tag members

/-- Create union memory value -/
def unionMval (tag : Sym) (member : Identifier) (val : MemValue) : MemValue :=
  .union_ tag member val

/-! ## Memory Interface

This defines the core memory operations. The concrete implementation
is in Memory/Concrete.lean.
-/

/-- Memory interface operations -/
class MemoryOps (m : Type → Type) where
  /-- Get the type environment -/
  getTypeEnv : m TypeEnv

  /-- Allocate memory for a typed object
      - name: debug name for allocation
      - size: size in bytes
      - ty: C type
      - align: optional alignment override
      - init: optional initial value -/
  allocateObject : String → IntegerValue → Ctype → Option Nat → Option MemValue → m PointerValue

  /-- Allocate raw memory region (malloc-style)
      - name: debug name
      - size: size in bytes
      - align: alignment -/
  allocateRegion : String → IntegerValue → IntegerValue → m PointerValue

  /-- Load value from memory -/
  load : Ctype → PointerValue → m (Footprint × MemValue)

  /-- Store value to memory
      - ty: type being stored
      - isLocking: if true, locks as read-only after store
      - ptr: destination pointer
      - val: value to store -/
  store : Ctype → Bool → PointerValue → MemValue → m Footprint

  /-- Deallocate memory
      - isDynamic: true for free(), false for end of scope
      - ptr: pointer to deallocate -/
  kill : Bool → PointerValue → m Unit

  /-- Pointer equality -/
  eqPtrval : PointerValue → PointerValue → m Bool

  /-- Pointer inequality -/
  nePtrval : PointerValue → PointerValue → m Bool

  /-- Pointer less than -/
  ltPtrval : PointerValue → PointerValue → m Bool

  /-- Pointer greater than -/
  gtPtrval : PointerValue → PointerValue → m Bool

  /-- Pointer less than or equal -/
  lePtrval : PointerValue → PointerValue → m Bool

  /-- Pointer greater than or equal -/
  gePtrval : PointerValue → PointerValue → m Bool

  /-- Pointer difference (p1 - p2) / sizeof(elemTy) -/
  diffPtrval : Ctype → PointerValue → PointerValue → m IntegerValue

  /-- Effectful pointer arithmetic with bounds checking -/
  effArrayShiftPtrval : PointerValue → Ctype → IntegerValue → m PointerValue

  /-- Effectful struct member shift -/
  effMemberShiftPtrval : PointerValue → Sym → Identifier → m PointerValue

  /-- Convert integer to pointer -/
  ptrfromint : IntegerType → Ctype → IntegerValue → m PointerValue

  /-- Convert pointer to integer -/
  intfromptr : Ctype → IntegerType → PointerValue → m IntegerValue

  /-- Check if pointer is valid for dereferencing -/
  validForDeref : Ctype → PointerValue → m Bool

  /-- Check if pointer is well-aligned -/
  isWellAligned : Ctype → PointerValue → m Bool

  /-- Memory copy -/
  memcpy : PointerValue → PointerValue → IntegerValue → m PointerValue

  /-- Memory compare -/
  memcmp : PointerValue → PointerValue → IntegerValue → m IntegerValue

  /-- Reallocate -/
  realloc : IntegerValue → PointerValue → IntegerValue → m PointerValue

/-! ## Pure Pointer Operations

These operations don't require memory state access.
-/

/-- Pure pointer arithmetic (no bounds check)
    ptr + (n * sizeof(elemTy)) -/
def arrayShiftPtrval (env : TypeEnv) (ptr : PointerValue) (elemTy : Ctype) (n : IntegerValue) : PointerValue :=
  match ptr.base with
  | .null ty => { ptr with base := .null ty }  -- NULL + n = NULL
  | .function sym => { ptr with base := .function sym }  -- Keep function ptr
  | .concrete unionMem addr =>
    let elemSize := sizeof env elemTy
    let newAddr := addr + n.val.toNat * elemSize
    { ptr with base := .concrete unionMem newAddr }

/-- Pure struct member shift -/
def memberShiftPtrval (env : TypeEnv) (ptr : PointerValue) (tag : Sym) (member : Identifier) : PointerValue :=
  match ptr.base with
  | .null ty => { ptr with base := .null ty }
  | .function sym => { ptr with base := .function sym }
  | .concrete _ addr =>
    match memberOffset env tag member with
    | some offset =>
      -- For union members, track which member we're accessing
      let unionMem := match env.lookupTag tag with
        | some (.union_ _) => some member
        | _ => none
      { ptr with base := .concrete unionMem (addr + offset) }
    | none => ptr  -- Member not found, return unchanged

end CToLean.Memory
