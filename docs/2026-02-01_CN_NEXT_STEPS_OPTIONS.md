# CN Implementation: Next Steps Options Analysis

**Date**: 2026-02-01
**Context**: After eliminating all silent default value anti-patterns (commit `7c95ac7`)
**Tests**: 11/28 passing, 17 failing

---

## Test Failure Categories

| Category | Count | Root Cause |
|----------|-------|------------|
| Memop | 5 | `ptrValidForDeref` not implemented |
| Type Annotation | 8 | Pure expressions lose type info |
| Case/Match | 2 | Conditionals lose type info |
| Constructor | 1 | `ivalignof` not handled |
| SMT | 1 | Cast not serialized |

---

## Option A: Type Inference (Unblocks 10 tests)

**Address Categories**: Type Annotation (8) + Case/Match (2)

Add type inference when Core annotations are missing:
- For binary ops: infer from operand types
- For case expressions: merge branch types
- For struct access: look up field types

**Pros**:
- Unblocks the most tests (10)
- Relatively contained changes (Pexpr.lean)
- No new CN concepts needed

**Cons**:
- Doesn't match CN exactly (CN has annotations from C frontend)
- May hide real type errors
- Doesn't advance resource verification

**Files**: `Pexpr.lean` (~100-150 lines)

---

## Option B: Memory Operations (Unblocks 5 tests)

**Address Category**: Memop (5)

Implement key memory operations in Expr.lean:
- `ptrValidForDeref` - validates pointer for dereferencing
- `ptrWellAligned` - checks alignment
- `arrayShift` / `memberShift` - pointer arithmetic

**Pros**:
- Advances core verification capability
- Required for any real memory verification
- Matches CN's approach exactly

**Cons**:
- Requires understanding CN's memop semantics
- May uncover other missing pieces
- Fewer tests unblocked

**Files**: `Expr.lean` (~100-200 lines)

### CN Implementation Reference

From `cn/lib/check.ml` lines 1700-1746:

**PtrValidForDeref** (lines 1700-1715):
```ocaml
| PtrValidForDeref, [ pe_ct; pe ] ->
  let@ ct = check_pexpr_good_ctype_const [] pe_ct in
  let@ () = WellTyped.ensure_base_type loc ~expect Bool in
  let@ () = WellTyped.ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe) in
  check_pexpr pe (fun arg ->
    let result = aligned_ (arg, ct) loc in
    k result)
```

**PtrWellAligned** (lines 1716-1725):
- Identical to PtrValidForDeref

**PtrArrayShift** (lines 1726-1746):
```ocaml
| PtrArrayShift, [ pe1; pe_ct; pe2 ] ->
  let@ () = WellTyped.ensure_base_type loc ~expect (Loc ()) in
  let@ ct = check_pexpr_good_ctype_const [] pe_ct in
  check_pexpr pe1 (fun vt1 ->
    check_pexpr pe2 (fun vt2 ->
      let result = arrayShift_ ~base:vt1 ct ~index:(cast_ Memory.uintptr_bt vt2 loc) loc in
      k result))
```

---

## Option C: Constructor Handling (Unblocks 1 test)

**Address Category**: Constructor (1)

Handle compiler builtins in Pexpr.lean:
- `ivalignof` - integer alignment constant
- `ivsize` - integer size constant

**Pros**:
- Quick win (small change)
- Simple semantics

**Cons**:
- Only unblocks 1 test
- Low impact overall

**Files**: `Pexpr.lean` (~20 lines)

---

## Option D: SMT Cast Serialization (Unblocks 1 test)

**Address Category**: SMT (1)

Add proper SMT serialization for cast operations.

**Pros**:
- Completes SMT backend for this case
- Quick fix

**Cons**:
- Only unblocks 1 test
- SMT layer is already fairly complete

**Files**: `SmtLib.lean` (~30 lines)

---

## Option E: Function Calls (Unblocks 0 tests currently, but foundational)

**Address**: ccall/proc in Expr.lean

Implement function call semantics:
- Look up function specification
- Check precondition resources
- Consume/produce resources
- Return properly typed result

**Pros**:
- Required for inter-procedural verification
- Foundational for real programs

**Cons**:
- No current tests exercise this
- Requires spec lookup infrastructure
- Larger scope

**Files**: `Expr.lean`, potentially new spec registry

---

## Recommended Prioritization

### Phase 1: Quick Wins
1. **Option C** (Constructors) - 1 test, ~20 lines, simple
2. **Option D** (SMT cast) - 1 test, ~30 lines, completes SMT layer

### Phase 2: Core Verification (Choose Based on Goals)

**Option A (Type Inference)** - Pragmatic approach:
- Unblocks 10 tests quickly
- Makes system more usable
- **BUT**: Deviates from CN's exact approach

**Option B (Memory Operations)** - CN-matching approach:
- Unblocks 5 tests
- Advances real verification
- **AND**: Matches CN exactly

### Phase 3: Inter-procedural
3. **Option E** (Function calls) - Required for real programs

---

## Files Summary

| File | Option | Lines | Impact |
|------|--------|-------|--------|
| `Pexpr.lean` | A, C | 100-170 | Type inference, constructors |
| `Expr.lean` | B, E | 100-300 | Memops, function calls |
| `SmtLib.lean` | D | 30 | Cast serialization |

---

## Verification

After any implementation:
```bash
make test-cn
```

Expected improvement per option:
- Option A: 10 more tests pass (21/28)
- Option B: 5 more tests pass (16/28)
- Option C: 1 more test passes (12/28)
- Option D: 1 more test passes (12/28)

---

## Decision Made (2026-02-01)

User selected:
1. **Match CN exactly** - investigate missing annotations rather than adding inference
2. **Option B: Memory Operations** - implement memops first
