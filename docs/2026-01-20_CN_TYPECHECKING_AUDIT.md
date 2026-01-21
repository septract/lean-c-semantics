# CN TypeChecking Audit Report

**Date**: 2026-01-20
**Scope**: `CerbLean/CN/TypeChecking/*.lean` vs `cn/lib/*.ml`

## Executive Summary

The CN TypeChecking implementation has **critical escape hatches** and **structural divergences** from the CN OCaml implementation that must be addressed. This audit identifies issues that would allow incorrect programs to pass verification or prevent proper error detection.

## Audit Methodology

Compared Lean implementation against CN OCaml source files:
- `cn/lib/context.ml` - Context data structure
- `cn/lib/typing.ml` - Typing monad
- `cn/lib/resourceInference.ml` - Resource inference algorithm
- `cn/lib/check.ml` - Main type checking (check_pexpr, check_expr, Eaction)
- `cn/lib/request.ml` - Request/resource types

---

## CRITICAL ISSUES (Must Fix)

### Issue 1: Default Values in Value Conversion (Pexpr.lean)

**Location**: `Pexpr.lean:56-61`
```lean
| .object (.pointer pv) =>
  match pv.base with
  | .null _ => return .null
  | .concrete _ addr =>
    match pv.prov with
    | .some allocId => return .pointer ⟨allocId, addr⟩
    | _ => return .pointer ⟨0, addr⟩  -- ESCAPE HATCH: Uses 0 for unknown provenance
```

**Problem**: Unknown provenance silently becomes allocation ID 0. This is **unsafe** - it could allow pointer operations to succeed when they should fail due to invalid provenance.

**CN OCaml**: Fails explicitly when provenance is required but missing.

**Fix**: Fail with a proper error:
```lean
| _ => throw (.other "Pointer with unknown provenance")
```

---

### Issue 2: Default Type in Ctype Conversion (Action.lean)

**Location**: `Action.lean:66-74`
```lean
def ctypeToBaseType (ct : Ctype) : BaseType :=
  match ct.ty with
  | .void => .unit
  | .basic (.integer _) => .integer
  | .basic (.floating _) => .real
  | .pointer _ _ => .loc
  | .struct_ tag => .struct_ tag
  | .array _ _ => .unit  -- ESCAPE HATCH
  | _ => .unit  -- ESCAPE HATCH: catch-all returns unit
```

**Problem**: Unknown types silently become `unit`. This could cause type mismatches to go undetected.

**Fix**: Make this function return `Except TypeError BaseType` and fail on unsupported types.

---

### Issue 3: Hardcoded C Type in Memory Actions (Action.lean)

**Location**: `Action.lean:99, 125, 157, 207`
```lean
-- In handleCreate:
let ct := Ctype.void  -- ESCAPE HATCH: hardcoded void*

-- In handleKill:
let ct := Ctype.void  -- ESCAPE HATCH: hardcoded void

-- In handleStore:
let ct := Ctype.integer (.signed .int_)  -- ESCAPE HATCH: hardcoded int

-- In handleLoad:
let ct := Ctype.integer (.signed .int_)  -- ESCAPE HATCH: hardcoded int
```

**Problem**: Memory operations use hardcoded types instead of extracting the actual type from the expression. This makes the verification meaningless - it's not checking the actual types being used.

**CN OCaml**: `action_.ct` provides the actual C type from the action annotation:
```ocaml
| Create (pe, act, prefix) ->
    let@ () = WellTyped.check_ct act.loc act.ct in
    ...
    (P { name = Owned (act.ct, Uninit); pointer = ret; iargs = [] }, ...)
```

**Fix**: Extract the actual type from the action's `Paction` structure.

---

### Issue 4: Silent Failure in Branch Resource Checking (Expr.lean)

**Location**: `Expr.lean:43-48`
```lean
def checkResourcesMatch (_ctx1 _ctx2 : Context) : TypingM Unit := do
  -- For now, we just trust that branches agree
  -- A full implementation would check resource equality
  pure ()
```

**Problem**: Branches are allowed to end with different resources, which violates separation logic soundness. Both branches of a conditional must produce the same resources.

**CN OCaml**: Checks that branch resources are compatible and merges them properly.

**Fix**: Implement actual resource comparison and fail if branches disagree.

---

### Issue 5: Non-Deterministic Expression Returns Arbitrary Result (Expr.lean)

**Location**: `Expr.lean:189-191`
```lean
| .nd es =>
  if es.isEmpty then
    return mkUnitTerm loc
  checkExpr es.head!  -- ESCAPE HATCH: just picks first
```

**Problem**: Non-deterministic choice just picks the first option, losing verification coverage. The other branches are never checked.

**Fix**: Check ALL branches and verify they produce compatible results.

---

### Issue 6: Missing Type Checking in Expression Conversion (Pexpr.lean)

**Location**: Throughout `checkPexpr`

**Problem**: CN uses `WellTyped.ensure_base_type` to verify types match expected types. Our implementation skips this entirely, relying on IndexTerm carrying `bt` fields.

**CN OCaml**:
```ocaml
| Epure pe ->
    let@ () = WellTyped.ensure_base_type loc ~expect (Mu.bt_of_pexpr pe) in
    check_pexpr pe (fun lvt -> k lvt)
```

**Our Lean**:
```lean
| .pure pe =>
    checkPexpr pe  -- No type checking!
```

**Fix**: Add explicit type checking calls that verify expected vs actual types.

---

### Issue 7: Pattern Conversion Loses Information (Pexpr.lean)

**Location**: `Pexpr.lean:350-362`
```lean
def convertPattern (pat : APattern) (bt : BaseType) (loc : Core.Loc) : CerbLean.CN.Types.Pattern :=
  match pat.pat with
  | .base (some s) _ => .mk (.sym s) bt loc
  | .base none _ => .mk .wild bt loc
  | .ctor c args =>
    let cnArgs := args.map fun p =>
      let subPat := convertPattern ⟨[], p⟩ bt loc  -- ESCAPE HATCH: reuses same bt
      let id : Identifier := { loc := Core.Loc.t.unknown, name := "" }  -- ESCAPE HATCH
      (id, subPat)
    .mk (.constructor (ctorToSym c) cnArgs) bt loc
```

**Problems**:
1. Constructor sub-patterns all get the same `bt` - should have per-field types
2. Identifier uses `unknown` location and empty name

**Fix**: Propagate proper types and locations through pattern conversion.

---

### Issue 8: Function Call Returns Placeholder (Expr.lean)

**Location**: `Expr.lean:144-158`
```lean
| .ccall funPtr _funTy args =>
  -- ...
  -- For now, just return a placeholder
  let resultBt := if argVals.isEmpty then .unit else argVals.head!.bt
  return AnnotTerm.mk (.const .unit) resultBt loc
```

**Problem**: Function calls completely skip specification checking. They just return a placeholder value instead of:
1. Looking up the function's specification
2. Consuming precondition resources
3. Producing postcondition resources
4. Returning the proper result

**Fix**: Implement proper function call checking using the callee's specification.

---

### Issue 9: Fresh Symbol Generation is Deterministic (Action.lean)

**Location**: `Action.lean:35-38`
```lean
def freshSym (prefix_ : SymPrefix) (_loc : Core.Loc) : TypingM Sym := do
  return { id := 0, name := some prefix_.val }  -- ESCAPE HATCH: always returns id=0
```

**Problem**: All "fresh" symbols have the same ID (0), which could cause incorrect symbol equality comparisons.

**CN OCaml**: Uses a global counter to generate truly unique symbols.

**Fix**: Add a counter to TypingState and increment it for each fresh symbol.

---

### Issue 10: Store Can Write to Init Memory Without Check (Action.lean)

**Location**: `Action.lean:176-191`
```lean
| none =>
  -- Try consuming Init instead (overwriting initialized memory)
  let initPred : Predicate := { ... }
  match ← predicateRequest initPred with
  | some _ =>
    -- Consumed Init, produce Init with new value
    ...
```

**Problem**: When store can't find Uninit, it silently falls back to consuming Init. This is actually correct for CN's semantics (you can write to initialized memory), BUT it should also check that the value being written is representable in the type.

**CN OCaml** (line 1863-1877):
```ocaml
let@ () =
  let in_range_lc = representable_ (act.ct, varg) here in
  let@ provable = provable loc in
  let holds = provable (LC.T in_range_lc) in
  match holds with
  | `True -> return ()
  | `False -> fail (...Write_value_unrepresentable...)
```

**Fix**: Add representability check before allowing the write.

---

## MEDIUM ISSUES (Should Fix)

### Issue 11: Missing Alloc Predicate (Action.lean)

**Location**: `handleCreate` and `handleKill`

**Problem**: CN creates an `Alloc` predicate alongside `Owned` to track allocation existence:
```ocaml
let@ () = add_r loc (P (Req.make_alloc ret), O lookup) in
```

Our implementation only creates `Owned`, missing the allocation tracking.

---

### Issue 12: Missing Alignment Constraints (Action.lean)

**CN OCaml** (line 1800):
```ocaml
let@ () = add_c loc (LC.T (alignedI_ ~align:align_v ~t:ret loc)) in
```

Our `handleCreate` doesn't add alignment constraints.

---

### Issue 13: Missing Allocation History (Action.lean)

**CN OCaml** tracks allocation history for VIP (virtual indirection proofs):
```ocaml
let lookup = Alloc.History.lookup_ptr ret here in
let value = Alloc.History.make_value ~base:(addr_ ret here) ~size here
```

Our implementation doesn't track this.

---

### Issue 14: Missing Action Recording (Action.lean)

**CN OCaml** records actions for debugging/proof logs:
```ocaml
let@ () = record_action (Create ret, loc) in
```

Our implementation doesn't record actions.

---

### Issue 15: sandbox Function Has Wrong Error Handling (Monad.lean)

**Location**: `Monad.lean:292-304`
```lean
def sandbox (m : TypingM α) : TypingM (Except TypeError α) := do
  let s ← getState
  let result : Except TypeError α ← (do
    let a ← m
    return Except.ok a) <|> (do
    return Except.error (TypeError.other "failed"))  -- ESCAPE HATCH: loses actual error
```

**Problem**: When the inner computation fails, the actual error is lost and replaced with a generic "failed" message.

**Fix**: Properly capture and return the actual error.

---

### Issue 16: Missing Solver Interaction (Monad.lean, Inference.lean)

**Problem**: CN's typing monad interacts with an SMT solver for constraint checking:
```ocaml
type s = { ...
  solver : solver option;
  ...
}
```

Our ProofOracle is a simplification that doesn't actually interact with a solver. The `trivial` oracle accepts everything, which is only valid for testing.

**Note**: This is acceptable for now if clearly documented as a testing mode.

---

## MINOR ISSUES (Nice to Have)

### Issue 17: Missing `remove_a` Operation (Context.lean)

**CN OCaml** has `remove_a` to move variables from computational to logical scope:
```ocaml
let remove_a s ctxt =
  let binding, info = Sym.Map.find s ctxt.computational in
  add_l_binding s binding info
    { ctxt with computational = Sym.Map.remove s ctxt.computational }
```

This is used when variables go out of scope but constraints on them should be preserved.

---

### Issue 18: Missing Global Context (Context.lean)

**CN OCaml Context** includes:
```ocaml
type t = { ...
  global : Global.t;
  where : Where.t
}
```

Our Context omits these fields. `global` is needed for looking up function specs, struct layouts, etc.

---

### Issue 19: Incomplete Audit Comments

Several functions lack proper line-number correspondence to CN OCaml. Good examples exist in Context.lean but are missing in Action.lean and Expr.lean.

---

## STRUCTURAL OBSERVATIONS

### CPS Style vs Direct Style

CN uses continuation-passing style (CPS):
```ocaml
let check_pexpr (pe : BT.t Mu.pexpr) (k : IT.t -> unit m) : unit m =
```

Our implementation uses direct style:
```lean
def checkPexpr (pe : APexpr) : TypingM IndexTerm := do
```

This is acceptable - the semantics are equivalent. Direct style is more idiomatic Lean.

### Two-Phase Resource Matching

Our `predicateRequestScan` correctly implements two-phase matching (syntactic fast path, then SMT slow path). This matches CN's approach.

### Subsumption

Our `nameSubsumed` correctly implements the rule that `Uninit` can be satisfied by `Init`:
```lean
| .owned ct1 .uninit, .owned ct2 _ => ct1 == ct2  -- uninit matches both
```

This matches CN's `subsumed` function in request.ml.

---

## RECOMMENDATIONS

### Priority 1 (Critical - Blocks Correctness)
1. Fix hardcoded types in Action.lean (Issue 3)
2. Implement branch resource checking (Issue 4)
3. Remove default value escape hatches (Issues 1, 2)
4. Implement function call specification checking (Issue 8)

### Priority 2 (Important - Improves Coverage)
5. Add type checking in Pexpr.lean (Issue 6)
6. Fix fresh symbol generation (Issue 9)
7. Add representability check in store (Issue 10)
8. Check all non-deterministic branches (Issue 5)

### Priority 3 (Completeness)
9. Add Alloc predicate tracking (Issue 11)
10. Add alignment constraints (Issue 12)
11. Fix sandbox error handling (Issue 15)

### Priority 4 (Polish)
12. Add missing audit comments
13. Implement Global context
14. Add action recording

---

## ESCAPE HATCH INVENTORY

| Location | Escape Hatch | Severity | Status |
|----------|--------------|----------|--------|
| Pexpr.lean:57 | `⟨0, addr⟩` for unknown provenance | CRITICAL | **FIXED** - Now throws error |
| Pexpr.lean:61 | `⟨0, 0⟩` for function pointers | CRITICAL | **FIXED** - Now throws error |
| Action.lean:73 | `_ => .unit` catch-all | CRITICAL | **FIXED** - Now fails on unsupported types |
| Action.lean:99 | `Ctype.void` hardcoded | CRITICAL | **FIXED** - Uses extractCtype/inferCtypeFromSize |
| Action.lean:125 | `Ctype.void` hardcoded | CRITICAL | **FIXED** - Uses KillKind.static type |
| Action.lean:157 | `Ctype.integer` hardcoded | CRITICAL | **FIXED** - Uses extractCtype |
| Action.lean:207 | `Ctype.integer` hardcoded | CRITICAL | **FIXED** - Uses extractCtype |
| Action.lean:37 | `id := 0` for all symbols | HIGH | **FIXED** - Uses counter in TypingState |
| Monad.lean:297 | Lost error in sandbox | MEDIUM | **FIXED** - Properly captures error |
| Expr.lean:45-48 | Skip resource match check | HIGH | OPEN |
| Expr.lean:157-158 | Placeholder function result | HIGH | OPEN |
| Expr.lean:191 | Only check first nd branch | HIGH | OPEN |
| Pexpr.lean:357-361 | Same bt for all sub-patterns | MEDIUM | OPEN |
| Test/CN.lean | Core IR vs muCore parameters | CRITICAL | OPEN (Issue 20) |

---

## NEW ISSUES (Discovered During Testing)

### Issue 20: Core IR vs muCore Parameter Handling (CRITICAL)

**Location**: Test infrastructure / Check.lean

**Problem**: CN operates on muCore where function parameters are directly available as values. Our implementation operates on Core IR where parameters are stored on the stack and must be loaded.

When verifying `int read(int *p) { return *p; }` with spec `requires take v = Owned<int>(p)`:

1. **CN/muCore approach**: Parameter `p` is directly available as a pointer value. The spec `Owned<int>(p)` refers to the memory that `p` points to.

2. **Core IR approach**: Parameter `p` is stored at a stack location. To use it:
   - First load the `int*` from the parameter's stack storage
   - Then load the `int` from that pointer

   This creates TWO load operations, the first of which needs `Owned<int*>` for the parameter storage itself.

**Evidence from JSON**:
```json
// First load - loads pointer from parameter storage
{ "tag": "Load", "ctype": "Pointer ... pointee_type: Integer" }

// Second load - dereferences the pointer
{ "tag": "Load", "ctype": "Basic ... Integer" }
```

**CN OCaml**: Works on muCore where `act.ct` provides the type being accessed directly, and parameters don't require stack loads.

**Fix Options**:

1. **Transform Core IR to muCore-like form**: Add a pass that identifies parameter loads and treats them specially, making parameter values directly available.

2. **Add implicit parameter storage resources**: When binding parameters, automatically add `Owned<T>(param_addr)` resources for their stack storage.

3. **Work at muCore level**: Use Cerberus's muCore output instead of Core IR (if available in JSON export).

**Severity**: CRITICAL - Without this fix, no memory-accessing function can be verified.

---

## CONCLUSION

The current implementation provides a **structural skeleton** that mirrors CN's approach, but contains **critical escape hatches** that would allow incorrect programs to pass verification. Before this can be used for actual verification, the critical issues must be addressed.

The ProofOracle abstraction is a good design decision that will allow plugging in different proof backends. However, using the `trivial` oracle in production would be unsound - it should be clearly marked as testing-only.

The codebase has good audit comments in some places (Context.lean, Monad.lean) but needs better correspondence documentation in the newer files (Action.lean, Expr.lean).
