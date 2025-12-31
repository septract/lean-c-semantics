/-
  Memory model types
  Based on cerberus/memory/concrete/impl_mem.ml and
  cerberus/frontend/model/mem_common.lem
-/

import CToLean.Core.Value
import Std.Data.HashMap

namespace CToLean.Memory

open CToLean.Core

/-! ## Read-only Status -/

/-- Kind of read-only memory -/
inductive ReadonlyKind where
  | ordinary      -- Normal const qualifier
  | stringLiteral -- String literal (special UB for modification)
  deriving Repr, BEq, Inhabited

/-- Read-only status for allocations -/
inductive ReadonlyStatus where
  | writable
  | readonly (kind : ReadonlyKind)
  deriving Repr, BEq, Inhabited

/-! ## Allocation Metadata -/

/-- Metadata for a single memory allocation -/
structure Allocation where
  /-- Base address of this allocation -/
  base : Nat
  /-- Size in bytes -/
  size : Nat
  /-- C type (None for malloc/dynamic allocation) -/
  ty : Option Ctype
  /-- Write protection status -/
  isReadonly : ReadonlyStatus
  /-- Debug name (variable name, source info) -/
  name : String
  deriving Repr, Inhabited

/-! ## Abstract Bytes -/

/-- Abstract byte in memory
    Tracks provenance for pointer reconstruction -/
structure AbsByte where
  /-- Provenance of this byte (which allocation it came from) -/
  prov : Provenance
  /-- Copy offset for pointer decomposition tracking
      When a pointer is stored, each byte records its offset in the pointer
      representation so we can reconstruct the pointer on load -/
  copyOffset : Option Nat
  /-- Actual byte value (None = uninitialized) -/
  value : Option UInt8
  deriving Repr, BEq, Inhabited

instance : Inhabited AbsByte where
  default := { prov := .none, copyOffset := none, value := none }

/-! ## Memory State -/

/-- Global memory state -/
structure MemState where
  /-- Next allocation ID to assign -/
  nextAllocId : Nat := 1
  /-- Active allocations: allocId -> Allocation -/
  allocations : Std.HashMap Nat Allocation := {}
  /-- Byte-level memory: address -> AbstractByte -/
  bytemap : Std.HashMap Nat AbsByte := {}
  /-- Freed allocation IDs (for dangling pointer detection) -/
  deadAllocations : List Nat := []
  /-- Function pointer mapping: address -> function symbol -/
  funptrmap : Std.HashMap Nat Sym := {}
  /-- Next address to use for allocations -/
  nextAddr : Nat := 0x1000  -- Start at reasonable offset
  deriving Inhabited

/-! ## Footprint Tracking -/

/-- Access kind for footprint tracking -/
inductive AccessKind where
  | read
  | write
  deriving Repr, BEq, Inhabited

/-- Memory access footprint -/
structure Footprint where
  /-- Read or write -/
  kind : AccessKind
  /-- Base address of access -/
  base : Nat
  /-- Size of access in bytes -/
  size : Nat
  deriving Repr, BEq, Inhabited

/-! ## Memory Errors -/

/-- Access-related memory errors -/
inductive AccessError where
  /-- Dereferencing null pointer -/
  | nullPtr
  /-- Dereferencing function pointer -/
  | functionPtr
  /-- Use after free -/
  | deadPtr
  /-- Out of bounds access -/
  | outOfBoundPtr
  /-- No provenance information on pointer -/
  | noProvPtr
  /-- Accessing atomic struct/union member -/
  | atomicMemberof
  deriving Repr, BEq, Inhabited

/-- Free/deallocation errors -/
inductive FreeError where
  /-- Free address doesn't match any allocation -/
  | nonMatching
  /-- Double free -/
  | deadAllocation
  /-- Address doesn't match allocation start -/
  | outOfBound
  deriving Repr, BEq, Inhabited

/-- Memory copy errors -/
inductive MemcpyError where
  /-- Overlapping regions in memcpy -/
  | overlap
  /-- Copying to/from non-objects -/
  | nonObject
  /-- Copying from dead object -/
  | deadObject
  /-- Copy region exceeds allocation bounds -/
  | outOfBound
  deriving Repr, BEq, Inhabited

/-- Combined memory error type -/
inductive MemError where
  /-- Access error (load/store) -/
  | access (err : AccessError) (addr : Option Nat := none)
  /-- Free error -/
  | free (err : FreeError)
  /-- Memcpy error -/
  | memcpy (err : MemcpyError)
  /-- Writing to read-only memory -/
  | readonlyWrite
  /-- Reading uninitialized memory (trap representation) -/
  | uninitRead (ty : Ctype)
  /-- Type incompatibility error -/
  | typeError (msg : String)
  /-- Pointer arithmetic overflow -/
  | ptrArithOverflow
  /-- Invalid alignment -/
  | alignmentError (required : Nat) (actual : Nat)
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
    | .readonlyWrite => "write to read-only memory"
    | .uninitRead ty => s!"reading uninitialized memory of type {repr ty}"
    | .typeError msg => s!"type error: {msg}"
    | .ptrArithOverflow => "pointer arithmetic overflow"
    | .alignmentError req actual => s!"alignment error: required {req}, got {actual}"

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
