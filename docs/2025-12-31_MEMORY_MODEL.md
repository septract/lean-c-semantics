# Memory Model Interface Design

This document describes the Lean memory model interface for the Lean C Semantics project. The design mirrors Cerberus's concrete memory model with allocation-ID provenance tracking (excluding symbolic PNVI-ae-udi and CHERI extensions).

## Overview

### Purpose
Define an abstract interface for memory operations that:
1. Matches Cerberus semantics for differential testing
2. Enables UB detection (null dereference, out-of-bounds, use-after-free)
3. Supports future theorem proving about memory safety

### Scope
- **Included**: Allocation-ID provenance, bounds checking, dangling pointer detection
- **Excluded**: Symbolic provenance (PNVI-ae-udi), CHERI capabilities, concurrency

### Reference Files
| File | Description |
|------|-------------|
| `cerberus/frontend/model/mem_common.lem` | Error types, memop definitions (~705 lines) |
| `cerberus/ocaml_frontend/memory_model.ml` | Interface signature (~257 lines) |
| `cerberus/memory/concrete/impl_mem.ml` | Concrete implementation (~3015 lines) |

---

## Core Types

### Already Defined (lean/CToLean/Core/Value.lean)

These types are already implemented and match Cerberus:

```lean
-- Provenance tracking
inductive Provenance where
  | none                    -- No provenance (integer constants)
  | some (allocId : Nat)    -- Allocation ID
  | symbolic (iota : Nat)   -- PNVI-ae-udi (not used)
  | device                  -- Device memory (not used)

-- Integer value with provenance
structure IntegerValue where
  val : Int
  prov : Provenance := .none

-- Pointer value base
inductive PointerValueBase where
  | null (ty : Ctype)
  | function (sym : Sym)
  | concrete (unionMember : Option Identifier) (addr : Nat)

-- Pointer value with provenance
structure PointerValue where
  prov : Provenance
  base : PointerValueBase

-- Memory value (values stored in memory)
inductive MemValue where
  | unspecified (ty : Ctype)
  | integer (ity : IntegerType) (v : IntegerValue)
  | floating (fty : FloatingType) (v : FloatingValue)
  | pointer (ty : Ctype) (v : PointerValue)
  | array (elems : List MemValue)
  | struct_ (tag : Sym) (members : List (Identifier × Ctype × MemValue))
  | union_ (tag : Sym) (member : Identifier) (value : MemValue)
```

### New Types (to be defined in lean/CToLean/Memory/)

#### Allocation Metadata

```lean
/-- Read-only status for allocations -/
inductive ReadonlyKind where
  | ordinary      -- Normal read-only (const)
  | stringLiteral -- String literal (special semantics)

inductive ReadonlyStatus where
  | writable
  | readonly (kind : ReadonlyKind)

/-- Metadata for a single allocation -/
structure Allocation where
  base : Nat                    -- Base address
  size : Nat                    -- Size in bytes
  ty : Option Ctype             -- Type (None for malloc)
  isReadonly : ReadonlyStatus   -- Write protection
  prefix : String               -- Debug info (variable name, etc.)
```

#### Memory State

```lean
/-- Abstract byte in memory -/
structure AbsByte where
  prov : Provenance             -- Where this byte came from
  copyOffset : Option Nat       -- For pointer decomposition tracking
  value : Option UInt8          -- Actual byte value (None = uninitialized)

/-- Global memory state -/
structure MemState where
  nextAllocId : Nat                           -- Next allocation ID to use
  allocations : Std.HashMap Nat Allocation    -- allocId -> Allocation
  bytemap : Std.HashMap Nat AbsByte           -- address -> byte
  deadAllocations : List Nat                  -- Freed allocation IDs
  funptrmap : Std.HashMap Nat Sym             -- address -> function symbol
```

#### Footprint Tracking

```lean
/-- Access kind for footprint tracking -/
inductive AccessKind where
  | read
  | write

/-- Memory access footprint -/
structure Footprint where
  kind : AccessKind
  base : Nat          -- Base address accessed
  size : Nat          -- Size in bytes
```

---

## Error Types

Memory errors map to undefined behaviors. From `cerberus/frontend/model/mem_common.lem`:

```lean
/-- Access errors -/
inductive AccessError where
  | nullPtr           -- Dereferencing null pointer
  | functionPtr       -- Dereferencing function pointer
  | deadPtr           -- Use after free
  | outOfBoundPtr     -- Out of bounds access
  | noProvPtr         -- No provenance information
  | atomicMemberof    -- Atomic struct/union member access

/-- Free/deallocation errors -/
inductive FreeError where
  | nonMatching       -- Free address doesn't match any allocation
  | deadAllocation    -- Double free
  | outOfBound        -- Address doesn't match allocation bounds

/-- Memory copy errors -/
inductive MemcpyError where
  | overlap           -- Overlapping regions in memcpy
  | nonObject         -- Copying to/from non-objects
  | deadObject        -- Copying from dead object
  | outOfBound        -- Copy region exceeds allocation bounds

/-- Combined memory error type -/
inductive MemError where
  | access (err : AccessError)
  | free (err : FreeError)
  | memcpy (err : MemcpyError)
  | readonlyWrite     -- Writing to read-only memory
  | uninitRead        -- Reading uninitialized memory (for trap representations)
  | typeError         -- Type compatibility error
```

---

## Memory Operations

### Monadic Interface

```lean
/-- Memory effect monad -/
abbrev MemM := StateT MemState (Except MemError)

-- With footprint tracking (for concurrency analysis, optional):
-- abbrev MemM α := StateT MemState (ExceptT MemError (WriterT (List Footprint) Id)) α
```

### Allocation Operations

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `allocateObject` | `String → IntegerValue → Ctype → Option Nat → Option MemValue → MemM PointerValue` | Static allocation with optional initialization |
| `allocateRegion` | `String → IntegerValue → IntegerValue → MemM PointerValue` | Dynamic allocation (malloc-style) |

```lean
/-- Allocate memory for a typed object
    - prefix: debug name
    - size: size in bytes
    - ty: C type
    - align: optional alignment override
    - init: optional initial value -/
def allocateObject (prefix : String) (size : IntegerValue) (ty : Ctype)
    (align : Option Nat) (init : Option MemValue) : MemM PointerValue

/-- Allocate raw memory region (malloc)
    - prefix: debug name
    - size: size in bytes
    - align: alignment -/
def allocateRegion (prefix : String) (size : IntegerValue)
    (align : IntegerValue) : MemM PointerValue
```

### Access Operations

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `load` | `Ctype → PointerValue → MemM (Footprint × MemValue)` | Read from memory |
| `store` | `Ctype → Bool → PointerValue → MemValue → MemM Footprint` | Write to memory |
| `kill` | `Bool → PointerValue → MemM Unit` | Deallocate memory |

```lean
/-- Load value from memory
    Checks: null, dead, out-of-bounds, function pointer
    Returns: footprint and loaded value -/
def load (ty : Ctype) (ptr : PointerValue) : MemM (Footprint × MemValue)

/-- Store value to memory
    - ty: type being stored
    - isLocking: if true, locks memory as read-only after store
    - ptr: destination pointer
    - val: value to store
    Checks: null, dead, out-of-bounds, read-only -/
def store (ty : Ctype) (isLocking : Bool) (ptr : PointerValue)
    (val : MemValue) : MemM Footprint

/-- Deallocate memory
    - isDynamic: true for free(), false for end of scope
    - ptr: pointer to deallocate
    Checks: null (optional), non-matching, double-free -/
def kill (isDynamic : Bool) (ptr : PointerValue) : MemM Unit
```

### Pointer Comparison Operations

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `eqPtrval` | `PointerValue → PointerValue → MemM Bool` | Pointer equality |
| `nePtrval` | `PointerValue → PointerValue → MemM Bool` | Pointer inequality |
| `ltPtrval` | `PointerValue → PointerValue → MemM Bool` | Less than |
| `gtPtrval` | `PointerValue → PointerValue → MemM Bool` | Greater than |
| `lePtrval` | `PointerValue → PointerValue → MemM Bool` | Less than or equal |
| `gePtrval` | `PointerValue → PointerValue → MemM Bool` | Greater than or equal |
| `diffPtrval` | `Ctype → PointerValue → PointerValue → MemM IntegerValue` | Pointer difference |

```lean
/-- Pointer equality comparison
    Handles: null, function pointers, concrete addresses
    Note: Comparison of pointers from different allocations is implementation-defined -/
def eqPtrval (p1 p2 : PointerValue) : MemM Bool

/-- Pointer difference (p1 - p2) / sizeof(elemTy)
    Checks: same allocation, valid pointers -/
def diffPtrval (elemTy : Ctype) (p1 p2 : PointerValue) : MemM IntegerValue
```

### Pointer Arithmetic Operations

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `arrayShiftPtrval` | `PointerValue → Ctype → IntegerValue → PointerValue` | Pure pointer arithmetic |
| `effArrayShiftPtrval` | `PointerValue → Ctype → IntegerValue → MemM PointerValue` | Effectful with bounds check |
| `memberShiftPtrval` | `PointerValue → Sym → Identifier → PointerValue` | Struct member access |
| `effMemberShiftPtrval` | `PointerValue → Sym → Identifier → MemM PointerValue` | Effectful member access |

```lean
/-- Pure pointer arithmetic (no bounds check)
    ptr + (n * sizeof(elemTy)) -/
def arrayShiftPtrval (ptr : PointerValue) (elemTy : Ctype)
    (n : IntegerValue) : PointerValue

/-- Effectful pointer arithmetic with bounds checking
    Returns error if result is out of bounds -/
def effArrayShiftPtrval (ptr : PointerValue) (elemTy : Ctype)
    (n : IntegerValue) : MemM PointerValue

/-- Shift pointer to struct/union member (pure) -/
def memberShiftPtrval (ptr : PointerValue) (tag : Sym)
    (member : Identifier) : PointerValue
```

### Conversion Operations

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `ptrfromint` | `IntegerType → Ctype → IntegerValue → MemM PointerValue` | Integer to pointer |
| `intfromptr` | `Ctype → IntegerType → PointerValue → MemM IntegerValue` | Pointer to integer |
| `validForDeref` | `Ctype → PointerValue → MemM Bool` | Check dereference validity |
| `isWellAligned` | `Ctype → PointerValue → MemM Bool` | Check alignment |

```lean
/-- Convert integer to pointer
    Implementation-defined behavior -/
def ptrfromint (fromTy : IntegerType) (toTy : Ctype)
    (n : IntegerValue) : MemM PointerValue

/-- Convert pointer to integer
    Preserves provenance in result -/
def intfromptr (fromTy : Ctype) (toTy : IntegerType)
    (ptr : PointerValue) : MemM IntegerValue

/-- Check if pointer is valid for dereferencing type -/
def validForDeref (ty : Ctype) (ptr : PointerValue) : MemM Bool

/-- Check if pointer is well-aligned for type -/
def isWellAligned (ty : Ctype) (ptr : PointerValue) : MemM Bool
```

### Memory Functions

| Operation | Signature | Description |
|-----------|-----------|-------------|
| `memcpy` | `PointerValue → PointerValue → IntegerValue → MemM PointerValue` | Memory copy |
| `memcmp` | `PointerValue → PointerValue → IntegerValue → MemM IntegerValue` | Memory compare |
| `realloc` | `IntegerValue → PointerValue → IntegerValue → MemM PointerValue` | Reallocate |

```lean
/-- Copy n bytes from src to dst
    Checks: non-overlapping, valid regions -/
def memcpy (dst src : PointerValue) (n : IntegerValue) : MemM PointerValue

/-- Compare n bytes, return <0, 0, >0 -/
def memcmp (p1 p2 : PointerValue) (n : IntegerValue) : MemM IntegerValue

/-- Reallocate memory region
    - align: new alignment
    - ptr: old pointer (freed after copy)
    - newSize: new size in bytes -/
def realloc (align : IntegerValue) (ptr : PointerValue)
    (newSize : IntegerValue) : MemM PointerValue
```

---

## Value Constructors

### Pointer Value Constructors

```lean
/-- Create null pointer of given type -/
def nullPtrval (ty : Ctype) : PointerValue :=
  { prov := .none, base := .null ty }

/-- Create function pointer -/
def funPtrval (sym : Sym) : PointerValue :=
  { prov := .none, base := .function sym }

/-- Create concrete pointer with address and provenance -/
def concretePtrval (allocId : Nat) (addr : Nat) : PointerValue :=
  { prov := .some allocId, base := .concrete none addr }
```

### Integer Value Constructors

```lean
/-- Create integer value from literal -/
def integerIval (n : Int) : IntegerValue :=
  { val := n, prov := .none }

/-- Maximum value for integer type -/
def maxIval (ity : IntegerType) : IntegerValue

/-- Minimum value for integer type -/
def minIval (ity : IntegerType) : IntegerValue

/-- sizeof(ty) as integer value -/
def sizeofIval (ty : Ctype) : IntegerValue

/-- alignof(ty) as integer value -/
def alignofIval (ty : Ctype) : IntegerValue

/-- Integer arithmetic with overflow checking -/
def opIval (op : IntegerOperator) (v1 v2 : IntegerValue) : IntegerValue
```

### Memory Value Constructors

```lean
/-- Create unspecified (uninitialized) value -/
def unspecifiedMval (ty : Ctype) : MemValue :=
  .unspecified ty

/-- Create integer memory value -/
def integerValueMval (ity : IntegerType) (v : IntegerValue) : MemValue :=
  .integer ity v

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
```

---

## Type Layout

Layout computation is needed for pointer arithmetic and allocation:

```lean
/-- Compute sizeof for a type (in bytes) -/
def sizeof (ty : Ctype) : Nat

/-- Compute alignof for a type (in bytes) -/
def alignof (ty : Ctype) : Nat

/-- Compute member offsets for a struct type
    Returns list of (member, offset) pairs -/
def offsetsof (tag : Sym) : List (Identifier × Nat)

/-- Get offset of specific member -/
def memberOffset (tag : Sym) (member : Identifier) : Option Nat
```

These require access to the type environment (struct/union definitions).

---

## Validation Strategy

### Differential Testing

The primary validation method is comparing Lean execution results against Cerberus:

```
┌─────────────┐     ┌──────────────┐     ┌─────────────────┐
│  C source   │────▶│   Cerberus   │────▶│  JSON Core IR   │
└─────────────┘     └──────────────┘     └────────┬────────┘
                                                   │
      ┌────────────────────────────────────────────┤
      │                                            ▼
      │                                    ┌──────────────┐
      │                                    │ Lean Parser  │
      │                                    └──────┬───────┘
      │                                           │
      ▼                                           ▼
┌─────────────────┐                      ┌──────────────────┐
│ Cerberus --batch│                      │ Lean Interpreter │
└────────┬────────┘                      └────────┬─────────┘
         │                                        │
         ▼                                        ▼
┌─────────────────┐                      ┌──────────────────┐
│ Cerberus Result │◀────── compare ─────▶│   Lean Result    │
└─────────────────┘                      └──────────────────┘
```

### Result Format

Match Cerberus batch output format for comparison:

```
-- Successful execution
Defined {value: "Specified(42)", stdout: "", stderr: "", blocked: "false"}

-- Unspecified return value
Defined {value: "Unspecified(int)", stdout: "", stderr: "", blocked: "false"}

-- Undefined behavior
Undefined {ub: "UB043_indirection_invalid_value", stderr: "", loc: "<6:3--6:5>"}
```

### Test Categories

| Category | File Pattern | Expected Result |
|----------|--------------|-----------------|
| Normal | `*.c` | `Defined { value: Specified(N) }` |
| Unspecified | (varies) | `Defined { value: Unspecified(ty) }` |
| Undefined | `*.undef.c` | `Undefined { ub: ... }` |
| Error | `*.error.c` | Compilation error |
| Syntax only | `*.syntax-only.c` | Parse success (no execution) |

### Success Criteria

| Level | Target | Test Set |
|-------|--------|----------|
| MVP | 80% match | CI tests subset (50 files) |
| Phase 3 | 85% match | Full CI tests (121 files) |
| Phase 5 | 90% match | Extended tests (5500 files) |

### Incremental Validation (Before Interpreter)

1. **Type-check**: Memory interface compiles
2. **Unit tests**: Individual operations (allocate, load, store)
3. **Property tests**: Invariants hold (e.g., load after store returns stored value)
4. **Edge cases**: NULL handling, alignment, overflow

---

## Implementation Plan

### File Structure

```
lean/CToLean/Memory/
├── Interface.lean    -- Type class defining memory operations
├── Types.lean        -- MemState, Allocation, Footprint, errors
├── Concrete.lean     -- Concrete memory model implementation
└── Layout.lean       -- sizeof, alignof, offsetsof
```

### Dependencies

```
Memory/Types.lean     (imports Core/Value.lean)
    ↓
Memory/Layout.lean    (imports Types.lean, needs type environment)
    ↓
Memory/Interface.lean (imports Types.lean, Layout.lean)
    ↓
Memory/Concrete.lean  (implements Interface)
```

### Implementation Order

1. **Types.lean**: Define `MemState`, `Allocation`, `Footprint`, `MemError`
2. **Layout.lean**: Implement `sizeof`, `alignof`, `offsetsof`
3. **Interface.lean**: Define type class with all operations
4. **Concrete.lean**: Implement allocation-ID provenance model

---

## Mapping to Cerberus

### Key Simplifications

| Cerberus Feature | Lean Handling |
|------------------|---------------|
| PNVI-ae-udi symbolic provenance | Not implemented |
| CHERI capabilities | Not implemented |
| Thread IDs | Ignored (single-threaded) |
| Memory order (atomics) | Ignored (sequential) |
| Varargs state | Deferred |
| Iota map | Not needed (no symbolic provenance) |

### Preserved Features

| Cerberus Feature | Lean Implementation |
|------------------|---------------------|
| Allocation IDs | `Provenance.some allocId` |
| Bounds checking | Check against `Allocation.size` |
| Dangling pointer detection | Check `deadAllocations` |
| Read-only memory | `Allocation.isReadonly` |
| Uninitialized memory | `AbsByte.value = none` |
| Footprint tracking | `Footprint` type |

---

## Open Questions

1. **Floating point**: How to handle NaN, infinity in comparisons?
2. **Effective type**: Track effective type for strict aliasing?
3. **Union semantics**: Full union member tracking or simplified?
4. **Error messages**: Include source location in errors?

These can be resolved during implementation based on test case requirements.
