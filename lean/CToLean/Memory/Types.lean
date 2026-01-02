/-
  Memory model types
  Corresponds to: cerberus/memory/concrete/impl_mem.ml
  Additional types from: cerberus/frontend/model/mem_common.lem

  CRITICAL: These types must match Cerberus exactly for differential testing.
-/

import CToLean.Core.Value
import Std.Data.HashMap

namespace CToLean.Memory

open CToLean.Core

/-! ## Read-only Status

Corresponds to: readonly_kind in mem_common.lem:124-127
```lem
type readonly_kind =
  | ReadonlyStringLiteral
  | ReadonlyTemporaryLifetime
  | ReadonlyConstQualified
```

And readonly_status in impl_mem.ml:400-402
```ocaml
type readonly_status =
  | IsWritable
  | IsReadOnly of Mem_common.readonly_kind
```
-/

/-- Kind of read-only memory.
    Corresponds to: readonly_kind in mem_common.lem:124-127
    Audited: 2026-01-01
    Deviations: None -/
inductive ReadonlyKind where
  | stringLiteral       -- ReadonlyStringLiteral
  | temporaryLifetime   -- ReadonlyTemporaryLifetime
  | constQualified      -- ReadonlyConstQualified
  deriving Repr, BEq, Inhabited

/-- Read-only status for allocations.
    Corresponds to: readonly_status in impl_mem.ml:400-402
    Audited: 2026-01-01
    Deviations: None -/
inductive ReadonlyStatus where
  | writable                      -- IsWritable
  | readonly (kind : ReadonlyKind) -- IsReadOnly of readonly_kind
  deriving Repr, BEq, Inhabited

/-! ## Taint (PNVI-ae exposure tracking)

Corresponds to: taint field in allocation type, impl_mem.ml:409
```ocaml
taint: [ `Unexposed | `Exposed ]; (* NOTE: PNVI-ae, PNVI-ae-udi *)
```
-/

/-- Taint status for PNVI-ae exposure tracking.
    Corresponds to: taint field in impl_mem.ml:409
    Audited: 2026-01-01
    Deviations: None -/
inductive Taint where
  | unexposed  -- `Unexposed - allocation not exposed to integer world
  | exposed    -- `Exposed - allocation has been exposed
  deriving Repr, BEq, Inhabited

/-! ## Allocation Metadata

Corresponds to: allocation type in impl_mem.ml:404-412
```ocaml
type allocation = {
  base: address;
  size: N.num;
  ty: ctype option;
  is_readonly: readonly_status;
  taint: [ `Unexposed | `Exposed ];
  prefix: Symbol.prefix;
}
```
-/

/-- Metadata for a single memory allocation.
    Corresponds to: allocation in impl_mem.ml:404-412
    Audited: 2026-01-01
    Deviations: prefix field simplified to String (Cerberus uses Symbol.prefix) -/
structure Allocation where
  /-- Base address of this allocation.
      Corresponds to: base field -/
  base : Nat
  /-- Size in bytes.
      Corresponds to: size field -/
  size : Nat
  /-- C type (None for malloc/dynamic allocation).
      Corresponds to: ty field -/
  ty : Option Ctype
  /-- Write protection status.
      Corresponds to: is_readonly field -/
  isReadonly : ReadonlyStatus
  /-- PNVI-ae exposure tracking.
      Corresponds to: taint field -/
  taint : Taint := .unexposed
  /-- Debug name (variable name, source info).
      Corresponds to: prefix field (simplified) -/
  name : String
  deriving Repr, Inhabited

/-! ## Abstract Bytes

Corresponds to: AbsByte.t in impl_mem.ml:415-420
```ocaml
module AbsByte = struct
  type t = {
    prov: provenance;
    copy_offset: int option;
    value: char option;
  }
```
-/

/-- Abstract byte in memory.
    Corresponds to: AbsByte.t in impl_mem.ml:415-420
    Audited: 2026-01-01
    Deviations: copy_offset uses Nat instead of int (always non-negative) -/
structure AbsByte where
  /-- Provenance of this byte (which allocation it came from).
      Corresponds to: prov field -/
  prov : Provenance
  /-- Copy offset for pointer decomposition tracking.
      When a pointer is stored, each byte records its offset in the pointer
      representation so we can reconstruct the pointer on load.
      Corresponds to: copy_offset field -/
  copyOffset : Option Nat
  /-- Actual byte value (None = uninitialized).
      Corresponds to: value field -/
  value : Option UInt8
  deriving Repr, BEq, Inhabited

instance : Inhabited AbsByte where
  default := { prov := .none, copyOffset := none, value := none }

/-! ## Memory State

Corresponds to: mem_state in impl_mem.ml:482-501
```ocaml
type mem_state = {
  next_alloc_id: storage_instance_id;
  next_iota: symbolic_storage_instance_id;
  last_address: address;
  allocations: allocation IntMap.t;
  iota_map: [...] IntMap.t;  (* PNVI-ae-udi only *)
  funptrmap: (Digest.t * string) IntMap.t;
  varargs: (int * (ctype * pointer_value) list) IntMap.t;
  next_varargs_id: N.num;
  bytemap: AbsByte.t IntMap.t;
  last_used_union_members: Symbol.identifier IntMap.t;
  dead_allocations: storage_instance_id list;
  dynamic_addrs: address list;
  last_used: storage_instance_id option;
  requested: (address * N.num) list;
}
```
-/

/-- Global memory state.
    Corresponds to: mem_state in impl_mem.ml:482-501
    Audited: 2026-01-01
    Deviations:
    - next_iota, iota_map: Deferred (PNVI-ae-udi only)
    - varargs, next_varargs_id: Deferred (variadic functions)
    - last_used: Deferred (PNVI-ae only)
    - requested: Deferred (cerb::with_address extension)
    - Address allocation grows upward from 0x1000 instead of downward from 0xFFFFFFFFFFFF -/
structure MemState where
  /-- Next allocation ID to assign.
      Corresponds to: next_alloc_id field -/
  nextAllocId : Nat := 1
  /-- Active allocations: allocId -> Allocation.
      Corresponds to: allocations field -/
  allocations : Std.HashMap Nat Allocation := {}
  /-- Byte-level memory: address -> AbstractByte.
      Corresponds to: bytemap field -/
  bytemap : Std.HashMap Nat AbsByte := {}
  /-- Freed allocation IDs (for dangling pointer detection).
      Corresponds to: dead_allocations field -/
  deadAllocations : List Nat := []
  /-- Dynamically allocated addresses (for free validation).
      Corresponds to: dynamic_addrs field -/
  dynamicAddrs : List Nat := []
  /-- Function pointer mapping: address -> function symbol.
      Corresponds to: funptrmap field (simplified - no digest) -/
  funptrmap : Std.HashMap Nat Sym := {}
  /-- Last used union members for union semantics.
      Corresponds to: last_used_union_members field -/
  lastUsedUnionMembers : Std.HashMap Nat Identifier := {}
  /-- Next address to use for allocations.
      Corresponds to: last_address field (but grows upward) -/
  nextAddr : Nat := 0x1000
  deriving Inhabited

/-! ## Footprint Tracking

Corresponds to: access_kind in mem_common.lem:17-19
```lem
type access_kind =
  | LoadAccess
  | StoreAccess
```

And footprint in impl_mem.ml:523-524
-/

/-- Access kind for footprint tracking.
    Corresponds to: access_kind in mem_common.lem:17-19
    Audited: 2026-01-01
    Deviations: None -/
inductive AccessKind where
  | read   -- LoadAccess
  | write  -- StoreAccess
  deriving Repr, BEq, Inhabited

/-- Memory access footprint.
    Corresponds to: footprint in impl_mem.ml:523-524
    Audited: 2026-01-01
    Deviations: None -/
structure Footprint where
  /-- Read or write -/
  kind : AccessKind
  /-- Base address of access -/
  base : Nat
  /-- Size of access in bytes -/
  size : Nat
  deriving Repr, BEq, Inhabited

/-! ## Memory Errors

Corresponds to: error types in mem_common.lem:21-76 and mem_error in mem_common.lem:129-162
-/

/-- Access-related memory errors.
    Corresponds to: access_error in mem_common.lem:21-27
    Audited: 2026-01-01
    Deviations: None -/
inductive AccessError where
  | nullPtr        -- NullPtr: dereferencing null pointer
  | functionPtr    -- FunctionPtr: dereferencing function pointer
  | deadPtr        -- DeadPtr: use after free
  | outOfBoundPtr  -- OutOfBoundPtr: out of bounds access
  | noProvPtr      -- NoProvPtr: no provenance information
  | atomicMemberof -- AtomicMemberof: accessing atomic struct/union member
  deriving Repr, BEq, Inhabited

/-- Free/deallocation errors.
    Corresponds to: free_error in mem_common.lem:46-49
    Audited: 2026-01-01
    Deviations: None -/
inductive FreeError where
  | nonMatching    -- Free_non_matching: address doesn't match any allocation
  | deadAllocation -- Free_dead_allocation: double free
  | outOfBound     -- Free_out_of_bound: address doesn't match allocation start
  deriving Repr, BEq, Inhabited

/-- Memory copy errors.
    Corresponds to: memcpy_error in mem_common.lem:61-65
    Audited: 2026-01-01
    Deviations: None -/
inductive MemcpyError where
  | overlap    -- Memcpy_overlap: overlapping regions
  | nonObject  -- Memcpy_non_object: copying to/from non-objects
  | deadObject -- Memcpy_dead_object: copying from dead object
  | outOfBound -- Memcpy_out_of_bound: copy region exceeds bounds
  deriving Repr, BEq, Inhabited

/-- Combined memory error type.
    Corresponds to: mem_error in mem_common.lem:129-162
    Audited: 2026-01-01
    Deviations:
    - MerrInternal, MerrOther: Combined into typeError
    - MerrPtrComparison, MerrArrayShift, etc.: Using specific error variants
    - VIP errors: Deferred (VIP memory model)
    - CHERI errors: Deferred (CHERI memory model) -/
inductive MemError where
  /-- Access error (load/store).
      Corresponds to: MerrAccess of access_kind * access_error -/
  | access (err : AccessError) (addr : Option Nat := none)
  /-- Free error.
      Corresponds to: MerrUndefinedFree of free_error -/
  | free (err : FreeError)
  /-- Memcpy error.
      Corresponds to: MerrUndefinedMemcpy of memcpy_error -/
  | memcpy (err : MemcpyError)
  /-- Writing to read-only memory.
      Corresponds to: MerrWriteOnReadOnly of readonly_kind -/
  | readonlyWrite (kind : ReadonlyKind := .constQualified)
  /-- Reading uninitialized memory.
      Corresponds to: MerrReadUninit -/
  | uninitRead (ty : Ctype)
  /-- Trap representation (e.g., _Bool not 0/1).
      Corresponds to: MerrTrapRepresentation of access_kind -/
  | trapRepresentation (kind : AccessKind)
  /-- Use outside lifetime.
      Corresponds to: MerrOutsideLifetime of string -/
  | outsideLifetime (msg : String)
  /-- Type incompatibility error.
      Corresponds to: MerrInternal, MerrOther -/
  | typeError (msg : String)
  /-- Pointer arithmetic overflow -/
  | ptrArithOverflow
  /-- Invalid alignment -/
  | alignmentError (required : Nat) (actual : Nat)
  /-- Pointer difference error.
      Corresponds to: MerrPtrdiff -/
  | ptrdiff
  deriving Repr, Inhabited

instance : ToString MemError where
  toString
    | .access .nullPtr _ => "null pointer dereference"
    | .access .functionPtr _ => "dereferencing function pointer"
    | .access .deadPtr addr => s!"use after free{addr.map (s!" at address {·}") |>.getD ""}"
    | .access .outOfBoundPtr addr => s!"out of bounds access{addr.map (s!" at address {·}") |>.getD ""}"
    | .access .noProvPtr _ => "pointer has no provenance"
    | .access .atomicMemberof _ => "accessing atomic struct/union member"
    | .free .nonMatching => "free of non-allocated address"
    | .free .deadAllocation => "double free"
    | .free .outOfBound => "free address doesn't match allocation"
    | .memcpy .overlap => "memcpy with overlapping regions"
    | .memcpy .nonObject => "memcpy to/from non-object"
    | .memcpy .deadObject => "memcpy from dead object"
    | .memcpy .outOfBound => "memcpy region exceeds allocation"
    | .readonlyWrite .stringLiteral => "write to string literal"
    | .readonlyWrite .temporaryLifetime => "write to temporary lifetime object"
    | .readonlyWrite .constQualified => "write to const-qualified object"
    | .uninitRead ty => s!"reading uninitialized memory of type {repr ty}"
    | .trapRepresentation .read => "read trap representation"
    | .trapRepresentation .write => "write trap representation"
    | .outsideLifetime msg => s!"use outside lifetime: {msg}"
    | .typeError msg => s!"type error: {msg}"
    | .ptrArithOverflow => "pointer arithmetic overflow"
    | .alignmentError req actual => s!"alignment error: required {req}, got {actual}"
    | .ptrdiff => "pointer difference error"

/-! ## Memory Monad -/

/-- Memory effect monad -/
abbrev MemM := StateT MemState (Except MemError)

/-- Run a memory computation with initial state -/
def MemM.run (m : MemM α) (s : MemState := {}) : Except MemError (α × MemState) :=
  StateT.run m s

/-- Run a memory computation, discarding final state -/
def MemM.run' (m : MemM α) (s : MemState := {}) : Except MemError α :=
  (·.1) <$> m.run s

end CToLean.Memory
