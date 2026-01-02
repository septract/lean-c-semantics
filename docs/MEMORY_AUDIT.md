# Memory Model Audit Plan

## Goal

Refactor the Lean memory model to match Cerberus's concrete memory model (`impl_mem.ml`) exactly, with:
1. Full Cerberus correspondence documentation (audited, line numbers)
2. Extensibility for future memory models (VIP, symbolic, CHERI)
3. Integration with the interpreter via `Eaction` handling

## Current State

**What we have (85-90% complete):**
- Core types: `Provenance`, `Allocation`, `AbsByte`, `MemState` - mostly correct
- Operations: `allocate`, `load`, `store`, `kill` - implemented but need audit
- Layout: `sizeof`, `alignof`, `structOffsets` - correct for LP64
- Integration: `liftMem` in interpreter monad - working

**Gaps identified:**
- Missing audit documentation linking to Cerberus
- Some Cerberus fields not present (e.g., `taint` for PNVI-ae)
- Float serialization is simplified (not IEEE 754)
- Trap representation checking not implemented
- `Eaction` not wired up in Step.lean

## Cerberus Reference Files

| File | Purpose |
|------|---------|
| `memory/concrete/impl_mem.ml:277-3015` | Concrete memory model implementation |
| `ocaml_frontend/memory_model.ml:22-257` | Memory module type signature |
| `frontend/model/mem_common.lem` | Error types, shared definitions |

## Phase 1: Types Audit and Alignment

### 1.1 Audit `Memory/Types.lean`

Add Cerberus correspondence documentation to all types:

**`Provenance`** → `provenance` in impl_mem.ml:287-291
```lean
/-- Pointer provenance for tracking allocation origin.
    Corresponds to: provenance in impl_mem.ml:287-291
    Audited: YYYY-MM-DD
    Deviations: None -/
inductive Provenance where
  | none      -- Prov_none
  | some (allocId : Nat)  -- Prov_some of storage_instance_id
  | symbolic (iota : Nat) -- Prov_symbolic (PNVI-ae-udi only)
  | device    -- Prov_device
```

**`Allocation`** → `allocation` in impl_mem.ml:404-412
- Add `taint : Taint` field for PNVI-ae (can default to `Unexposed`)
- Document each field's correspondence

**`AbsByte`** → `AbsByte.t` in impl_mem.ml:415-420
- Already has `prov`, `copyOffset`, `value` - verify match

**`MemState`** → `mem_state` in impl_mem.ml:482-501
- Add missing fields as stubs for future extensibility:
  - `iotaMap` (PNVI-ae-udi)
  - `lastUsedUnionMembers` (union semantics)
  - `dynamicAddrs` (malloc tracking)

### 1.2 Audit `Memory/Interface.lean`

Verify `MemoryOps` typeclass matches `Memory` module type.

Key operations to document:
- `allocateObject` → `allocate_object` (impl_mem.ml:1288-1347)
- `allocateRegion` → `allocate_region` (impl_mem.ml:1420-1435)
- `load` → `load` (impl_mem.ml:1552-1603)
- `store` → `store` (impl_mem.ml:1667-1789)
- `kill` → `kill` (impl_mem.ml:1464-1550)

## Phase 2: Concrete Implementation Audit

### 2.1 Audit `Memory/Concrete.lean`

For each function, add:
1. Cerberus correspondence (file:lines)
2. "Audited: YYYY-MM-DD" marker
3. "Deviations:" section listing any differences

**Key functions to audit:**

| Lean Function | Cerberus Function | Lines |
|---------------|-------------------|-------|
| `allocateImpl` | `allocator` + `allocate_object` | 1247-1347 |
| `loadImpl` | `load` | 1552-1603 |
| `storeImpl` | `store` | 1667-1789 |
| `killImpl` | `kill` | 1464-1550 |
| `memValueToBytes` | `repr` | 1139-1219 |
| `reconstructValue` | `abst` | 916-1093 |
| `intToBytes` | `bytes_of_int` | 723-737 |
| `bytesToInt` | `int_of_bytes` | 739-758 |

### 2.2 Fix Known Gaps

1. **Float serialization** (medium priority)
   - Current: `f.toUInt64.toNat` (wrong)
   - Cerberus: IEEE 754 bit pattern
   - Fix: Use proper float-to-bits conversion

2. **Address allocation direction** (verify)
   - Cerberus: grows downward from `0xFFFFFFFFFFFF`
   - Current: grows upward from `0x1000`
   - Decision: Keep current (functionally equivalent, just different addresses)

3. **Trap representation** (low priority, defer)
   - Cerberus: checks `_Bool` loads for 0/1
   - Add TODO comment for future

## Phase 3: Interpreter Integration

### 3.1 Implement `Eaction` in Step.lean

Currently: `| .action _paction, _ => throw (.notImplemented "Eaction")`

Implement each action case matching `core_action_step` in core_run.lem:275-650:

```lean
| .action paction, stack =>
  let act := paction.action.action
  match act with
  | .create align size prefix =>
    -- Corresponds to: core_run.lem:309-326 (Create case)
    let alignVal ← evalPexpr st.env align
    let sizeVal ← evalPexpr st.env size
    let ptr ← InterpM.liftMem (allocateObject ...)
    -- Return pointer value wrapped in Epure
    ...
  | .store locking ty ptr val order =>
    -- Corresponds to: core_run.lem:529-566 (Store case)
    ...
  | .load ty ptr order =>
    -- Corresponds to: core_run.lem:582-609 (Load case)
    ...
  | .kill kind ptr =>
    -- Corresponds to: core_run.lem:456-474 (Kill case)
    ...
```

### 3.2 Value Conversion Helpers

Add helpers to convert between Core `Value` and Memory types:

```lean
/-- Convert Core Value to MemValue for store -/
def valueToMemValue (v : Value) (ty : Ctype) : InterpM MemValue

/-- Convert MemValue to Core Value after load -/
def memValueToValue (mv : MemValue) : InterpM Value
```

## Phase 4: Testing

### 4.1 Update Memory Tests

Ensure `Test/Memory.lean` covers:
- All allocation scenarios
- Load/store for each type (int, float, pointer, struct, array)
- UB detection (null deref, use-after-free, double-free, OOB)
- Read-only memory enforcement

### 4.2 Interpreter Tests

With `Eaction` implemented, these tests should pass:
- `007-local-var.c` (create, store, load, kill)
- `008-local-var-arith.c`
- `012-compare-eq.c` through `030-negative.c`

Target: 22 additional tests (currently failing due to `Eaction`)

## File Changes Summary

| File | Changes |
|------|---------|
| `Memory/Types.lean` | Add audit docs, `Taint` type, stub fields |
| `Memory/Interface.lean` | Add audit docs |
| `Memory/Concrete.lean` | Add audit docs, fix float encoding |
| `Memory/Layout.lean` | Add audit docs (already correct) |
| `Semantics/Step.lean` | Implement `Eaction` cases |
| `Semantics/Eval.lean` | Add value conversion helpers |

## Extensibility Design

To support future memory models:

1. **Keep `MemoryOps` typeclass** - already abstract
2. **Add `MemoryModel` enum** for runtime selection:
   ```lean
   inductive MemoryModel where
     | concrete    -- Current implementation
     | vip         -- Future: VIP (PNVI-ae-udi)
     | symbolic    -- Future: For CN
   ```
3. **Stub fields in `MemState`** - add PNVI fields with defaults
4. **Document which operations are model-specific** vs shared

## Implementation Order

**Approach**: Full implementation with verified Cerberus references. For each correspondence comment, read the actual Cerberus source to confirm line numbers before adding.

### Step 1: Audit `Memory/Types.lean`
- Read `impl_mem.ml` to verify type definitions
- Add correspondence docs with verified line numbers
- Add `Taint` type for PNVI-ae compatibility
- Add stub fields to `MemState` for future extensibility

### Step 2: Audit `Memory/Interface.lean`
- Read `memory_model.ml` module signature
- Verify `MemoryOps` typeclass matches
- Add correspondence docs

### Step 3: Audit `Memory/Concrete.lean`
- Read each Cerberus function and verify our implementation
- Add correspondence docs to each function
- Fix float serialization (IEEE 754)
- Note any deviations

### Step 4: Audit `Memory/Layout.lean`
- Verify against `sizeof`/`alignof`/`offsetsof` in impl_mem.ml
- Add correspondence docs

### Step 5: Implement `Eaction` in `Step.lean`
- Read `core_action_step` in core_run.lem
- Implement create, store, load, kill actions
- Add value conversion helpers

### Step 6: Test and Validate
- Run memory unit tests
- Run interpreter tests (target: 30/30)
- Fix any issues found

## Success Criteria

- All memory types/functions have Cerberus correspondence docs
- `Eaction` fully implemented for: create, store, load, kill
- Interpreter tests: 30/30 passing (up from 8/30)
- Memory tests: all passing
- No regressions in parser or pretty-printer tests

## Out of Scope (Future Work)

- PNVI-ae-udi symbolic provenance resolution
- VIP memory model
- Atomic operations (fence, RMW, compare-exchange)
- CHERI capabilities
- Effective type tracking (strict aliasing)
