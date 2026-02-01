# CN Code Anti-Pattern Audit Report

**Date**: 2026-02-01
**Auditor**: Claude (automated audit)
**Scope**: All files in `lean/CerbLean/CN/`

## Overview

This audit identifies instances of the following anti-patterns in the CN codebase:

1. **Fall-through / default cases** that silently handle errors
2. **"For simplicity"** cases that skip proper handling
3. **Errors turning into default values** instead of propagating

These patterns violate the project's core principle: **NEVER silently swallow errors**.

---

## CRITICAL VIOLATIONS

### 1. Pexpr.lean - Multiple Default Value Returns

**Line 145**: `ctypeToBaseTypeSimple` returns `.unit` as fallback for complex types
```lean
| _ => .unit  -- fallback for complex types
```
**VIOLATION**: Silently turns unknown types into unit instead of propagating an error.

---

**Lines 283-297**: `coreBaseTypeToCN` and `objectTypeToCN` have multiple silent defaults:
```lean
| .list _ => .unit  -- TODO: proper list type
| .tuple _ => .unit  -- TODO: proper tuple type
| .integer => .bits .signed 32  -- Default to signed 32-bit for unspecified integers
```
**VIOLATION**: Returns default values instead of failing with explicit type error.

---

**Line 334-335**: `bindPattern` has fallback for non-tuple values:
```lean
| _ => []  -- Non-tuple value - will use pattern types as fallback
```
**VIOLATION**: Silent empty list instead of explicit error when destructuring a non-tuple.

---

**Lines 477, 499, 509, 520, 599, 609, 626, 635, 645, 767**: Multiple `pe.ty.map coreBaseTypeToCN |>.getD .unit` patterns

**VIOLATION**: Falls back to `.unit` when type information is missing. This pattern appears ~10 times in this file alone.

---

**Lines 514-520**: Constructor fallback returns symbolic term for unknown constructors:
```lean
| _ =>
  -- Other constructors (nil, cons, array, etc.) - create a symbolic term
  -- This is a simplification; full support would track list/array values
  let state ← TypingM.getState
  let ctorSym : Sym := { id := state.freshCounter, name := some s!"ctor_{repr c}" }
```
**VIOLATION**: "Simplification" comment indicates incomplete handling.

---

**Lines 663-664**: `alignof` approximated as `sizeof`:
```lean
| .alignof_ ct =>
  -- alignof not directly in CN terms, use sizeof as approximation
  return AnnotTerm.mk (.sizeOf ct) .integer loc
```
**VIOLATION**: Returns semantically wrong value instead of failing with unsupported error.

---

**Line 714**: Shift operations approximated:
```lean
| .shl | .shr => BinOp.add  -- shifts not directly in CN, approximate
```
**VIOLATION**: Returns wrong operator instead of failing.

---

**Lines 718-737**: Type predicates (isScalar, isInteger, isSigned, isUnsigned, areCompatible) all return `true`/`false` unconditionally:
```lean
| .isScalar e =>
  let pe' : APexpr := ⟨[], some .ctype, e⟩
  let _t ← checkPexpr pe'
  -- These are runtime type checks - return true symbolically
  return AnnotTerm.mk (.const (.bool true)) .bool loc
```
**VIOLATION**: Returns constant instead of doing actual type checking or failing.

---

### 2. Expr.lean - Silent Handling

**Lines 96-100**: `memop` evaluates arguments but ignores them:
```lean
| .memop _op args =>
  -- Evaluate all arguments (simplified)
  for arg in args do
    checkPexprK arg fun _ => pure ()
  k (mkUnitTermExpr loc)
```
**VIOLATION**: Ignores memop semantics entirely, returns unit regardless of operation.

---

**Lines 169-182**: `ccall` returns unit with "In a full implementation" comment:
```lean
| .ccall funPtr _funTy args =>
  -- Evaluate function pointer
  checkPexprK funPtr fun _fnVal => do
    -- Evaluate arguments
    evalArgsK args fun argVals => do
      -- In a full implementation, we would:
      -- 1. Look up the function's specification
      -- 2. Check precondition resources via Spine.calltype_ft
      -- 3. Consume/produce resources
      -- 4. Call continuation with result

      let resultBt := if argVals.isEmpty then .unit else argVals.head!.bt
      k (AnnotTerm.mk (.const .unit) resultBt loc)
```
**VIOLATION**: Incomplete implementation returns default value.

---

**Lines 188-193**: `proc` generates symbolic result with arbitrary type:
```lean
| .proc name args =>
  evalArgsK args fun argVals => do
    let fnSym := match name with
      | .sym s => s
      | .impl _ => { id := 0, name := some "impl" : Sym }

    let resultBt := if argVals.isEmpty then .unit else argVals.head!.bt
    k (AnnotTerm.mk (.apply fnSym argVals) resultBt loc)
```
**VIOLATION**: Returns unit or first arg's type as fallback - should look up function signature.

---

**Lines 277-280**: Leaked resources silently ignored:
```lean
| .run label args => do
  ...
  calltypeLt loc args entry fun _false => do
    -- After the label call, check that all resources are consumed
    -- Corresponds to: all_empty loc original_resources
    let remainingResources ← TypingM.getResources
    if !remainingResources.isEmpty then
      -- For now, just warn about leaked resources
      -- A strict implementation would fail here
      pure ()
```
**VIOLATION**: Explicit comment about being non-strict, silently continues on resource leak.

---

**Lines 287-291, 295-296**: Concurrency constructs return unit:
```lean
| .par es =>
  if es.isEmpty then
    k (mkUnitTermExpr loc)
  else
    -- For parallel, check each speculatively
    for e' in es do
      let _ ← TypingM.pure_ (checkExpr labels e' k)
    pure ()

| .wait _tid =>
  k (mkUnitTermExpr loc)
```
**VIOLATION**: Unsupported constructs silently return unit instead of failing.

---

### 3. Resolve.lean - Silent Defaults

**Lines 167-183**: `resolveSymWithType` returns unit type on failure:
```lean
def resolveSymWithType (ctx : ResolveContext) (s : Sym) : Sym × BaseType :=
  if needsResolution s then
    match s.name with
    | some name =>
      match ctx.lookup name with
      | some (resolved, bt) => (resolved, bt)
      | none => (s, .unit)  -- Not found - keep original with unit type
    | none => (s, .unit)  -- No name - keep original
  else
    match s.name with
    | some name =>
      match ctx.lookup name with
      | some (_, bt) => (s, bt)
      | none => (s, .unit)  -- Not in context - use unit type
    | none => (s, .unit)  -- No name - use unit type
```
**VIOLATION**: Returns `.unit` in 4 different failure cases instead of propagating lookup failures.

---

**Lines 249-251**: `resolveTerm` falls back for large integers:
```lean
| .z n, none =>
  -- INFER mode: pick smallest fitting Bits type
  match pickIntegerEncodingType n with
  | some (.bits sign width) => .const (.bits sign width n)
  | _ => .const c  -- Fallback for huge numbers (CN would fail here)
```
**VIOLATION**: Comment acknowledges CN would fail, but we return default.

---

**Lines 326-331**: Same fallback in `resolveAnnotTerm`:
```lean
| none =>
  -- INFER mode: pick smallest fitting Bits type (CN's default behavior)
  match pickIntegerEncodingType n with
  | some (.bits sign width) => .mk (.const (.bits sign width n)) (.bits sign width) loc
  | _ => .mk (.const (.z n)) .integer loc  -- Fallback for huge numbers (CN would fail)
```
**VIOLATION**: Should fail like CN does.

---

### 4. Action.lean - Silent Fallbacks

**Lines 246-256**: `handleKill` treats missing resource as idempotent:
```lean
| none =>
  -- No resource found - this can happen with Cerberus-generated code
  -- that has multiple cleanup points (e.g., return statement + scope exit).
  -- We treat this as idempotent (killing already-freed memory is a no-op)
  -- rather than a hard error.
  --
  -- TODO: POTENTIAL CN DISCREPANCY - Kill idempotence needs careful review.
  -- CN may require the resource to exist. We make kill idempotent to handle
  -- Cerberus's double-kill pattern, but this should be revisited when proving
  -- type checking correct wrt runtime semantics. If CN actually requires the
  -- resource, we'd need to track "already killed" state differently.
  return mkUnitTermExpr loc
```
**VIOLATION**: Explicitly noted CN discrepancy, returns success instead of failing.

---

### 5. Params.lean - Silent Type Conversion Failures

**Lines 159-176**: `tryCoreBaseTypeToCN` returns `none` for unsupported types:
```lean
def tryCoreBaseTypeToCN (bt : Core.BaseType) : Option BaseType :=
  match bt with
  | .unit => some .unit
  | .boolean => some .bool
  ...
  -- Unsupported types
  | .list _ => none
  | .tuple _ => none
  | .object (.array _) => none
  | .object (.union_ _) => none
  | .storable => none
```
**SEMI-OK**: Returns `Option`, but callers may not handle `none` correctly.

---

**Lines 283-289**: Return type falls back to unit:
```lean
let returnBt := match cRetTy with
  | some ct => Resolve.ctypeToOutputBaseType ct
  | none =>
    -- Fall back to Core return type if C type not available
    match tryCoreBaseTypeToCN retTy with
    | some bt => bt
    | none => .unit  -- Fall back to unit for unsupported types
```
**VIOLATION**: Falls back to `.unit` for unsupported return types.

---

### 6. SmtLib.lean - Unsupported Constructs

**Lines 64-74**: Multiple base types fall back to `Int`:
```lean
def baseTypeToSort : BaseType → Smt.Term
  | .bits _ width => Term.mkApp2 (Term.symbolT "_")
                                  (Term.symbolT "BitVec")
                                  (Term.literalT (toString width))
  | .integer => Term.symbolT "Int"
  | .bool => Term.symbolT "Bool"
  | .real => Term.symbolT "Real"
  | .loc => Term.symbolT "Int"
  | .allocId => Term.symbolT "Int"
  | .unit => Term.symbolT "Bool"
  | .struct_ _ => Term.symbolT "Int"  -- Structs unsupported, fallback
  | .memByte => Term.symbolT "Int"  -- Memory bytes as integers
  | .list _ => Term.symbolT "Int"  -- Lists unsupported
  | .set _ => Term.symbolT "Int"  -- Sets unsupported
  | .tuple _ => Term.symbolT "Int"  -- Tuples unsupported
  | .map _ _ => Term.symbolT "Int"  -- Maps unsupported
  | .record _ => Term.symbolT "Int"  -- Records unsupported
  | .datatype _ => Term.symbolT "Int"  -- Datatypes unsupported
  | .ctype => Term.symbolT "Int"  -- C types as integers
  | .option _ => Term.symbolT "Int"  -- Options unsupported
```
**VIOLATION**: Should return `.unsupported` result but returns `Int` sort instead, masking type errors.

---

**Lines 374-381**: `good`, `wrapI`, `cast`, `copyAllocId` etc. silently pass through:
```lean
| .good _ val => annotTermToSmtTerm val
| .wrapI _ val => annotTermToSmtTerm val
| .cast _ val => annotTermToSmtTerm val
| .copyAllocId _ loc => annotTermToSmtTerm loc
| .hasAllocId _ => .ok (Term.symbolT "true")
| .sizeOf _ => .ok (Term.literalT "1")
| .offsetOf _ _ => .ok (Term.literalT "0")
| .memberShift ptr _ _ => annotTermToSmtTerm ptr
```
**VIOLATION**: Ignores semantics, returns inner term or constant values.

---

**Lines 393-409**: Tuple handling has partial support:
```lean
| .tuple elems =>
  -- Support single-element tuples (common in return value handling)
  match elems with
  | [single] => annotTermToSmtTerm single
  | _ => .unsupported s!"tuple with {elems.length} elements"
| .nthTuple n tup =>
  ...
  -- For non-tuple terms, if n=0, just return the term (treating as single-element)
  if n == 0 then annotTermToSmtTerm tup
  else .unsupported s!"nthTuple on non-tuple term"
```
**VIOLATION**: Partial support with silent simplifications for n=0 case.

---

**Lines 443-446**: Match patterns assume "Specified" is always true:
```lean
if isSpecified pat1 && isUnspecified pat2 then
  -- Pattern: match x with Specified(v) => e1 | Unspecified => e2
  -- Assume we're always in the Specified case (sound for verification)
  annotTermToSmtTerm body1
```
**VIOLATION**: "Sound for verification" comment but silently picks one branch.

---

**Lines 460-462**: Generic match uses first branch:
```lean
else
  -- For now, just use the first branch (pragmatic approximation)
  annotTermToSmtTerm body1
```
**VIOLATION**: "Pragmatic approximation" silently picks first branch.

---

### 7. Inference.lean - Resource Matching

**Lines 164-167**: `resourceRequest` returns `none` for quantified predicates:
```lean
| .q _qpred =>
  -- Quantified predicates not yet supported
  -- Would call qpredicate_request
  return none
```
**SEMI-OK**: Returns `none`, but callers should handle this as explicit unsupported error.

---

### 8. Parser.lean - Implicit Defaults

**Lines 160-175**: C type parsing has implicit defaults:
```lean
let baseType : Ctype := match baseName with
  | "void" => .void
  | "char" => ...
  | "int" | "" => .basic (.integer intType)  -- "" means just sign/size without explicit "int"
  | "float" => .basic (.floating (.realFloating .float))
  | "double" => ...
  | _ =>
    -- Treat as struct tag for now (could also be typedef)
    .struct_ { id := 0, name := some baseName }
```
**VIOLATION**: Unknown type names silently become structs instead of parse error.

---

**Lines 472-474, 481-483**: Default types for Owned/Block:
```lean
| "Owned" =>
  let ct ← optional do
    symbol "<"
    let ct ← parseCtype
    symbol ">"
    pure ct
  -- Default to signed int if no type specified
  pure (.owned (ct.getD mkIntCtype) .init)
```
**SEMI-VIOLATION**: Default type when none specified - may be intentional for shorthand syntax.

---

## SUMMARY

### Critical Count by Severity

| Severity | Count | Description |
|----------|-------|-------------|
| **CRITICAL** | 28 | Silent error → default value |
| **HIGH** | 12 | Incomplete handling with TODO/comment |
| **MEDIUM** | 8 | Approximation/simplification |

### Most Problematic Files

| File | Violations | Primary Issues |
|------|------------|----------------|
| **Pexpr.lean** | 15+ | Type defaults, `.getD .unit` patterns |
| **SmtLib.lean** | 10+ | Int fallbacks, silent simplifications |
| **Expr.lean** | 6 | Silent success, ignoring semantics |
| **Resolve.lean** | 4 | Unit type defaults |
| **Params.lean** | 2 | Return type fallbacks |
| **Action.lean** | 1 | Kill idempotence discrepancy |

### Dangerous Patterns to Eliminate

1. **`|>.getD .unit`** - This pattern appears ~15 times and should be banned
2. **`| _ => defaultValue`** - Catch-all cases that return defaults
3. **`-- For simplicity/For now`** comments with non-failing behavior
4. **`-- TODO`** comments that indicate incomplete error handling

---

## Recommended Actions

### Immediate (P0)

1. Convert all `|>.getD .unit` to explicit error propagation
2. Replace default catch-all cases with `TypingM.fail (.other "unsupported: ...")`
3. Fix `handleKill` to fail on missing resource (or explicitly document deviation)

### Short-term (P1)

1. Add proper error types for each category of failure
2. Implement missing type predicates (isScalar, etc.) or fail explicitly
3. Fix SMT translation to return `.unsupported` for all unhandled types

### Medium-term (P2)

1. Implement full ccall/proc handling with function signature lookup
2. Add proper memop semantics
3. Review all "pragmatic approximation" comments

---

## Appendix: The Anti-Pattern

```lean
-- FORBIDDEN - NEVER DO THIS
| .error _ => .ok Loc.unknown
| .error _ => .ok defaultValue
| .error _ => pure []
match parse x with | .error _ => someDefault | .ok v => v
something.getD defaultValue  -- when something is an error-producing computation
```

The ONLY acceptable pattern:
```lean
-- OK: trying alternative strategies, error still propagates
match parseFormatA x with
| .ok v => .ok v
| .error _ => parseFormatB x  -- still returns Except, error propagates
```
