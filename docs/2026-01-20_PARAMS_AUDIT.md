# CN Parameter Handling Audit

**Date**: 2026-01-20
**Status**: ✅ FIXED - Lazy muCore transformation implemented (commit b213542)

## Summary

~~Our `Params.lean` implementation doesn't match CN's approach to parameter handling. CN transforms loads at compile time; we tried to use resources at type-checking time.~~

**UPDATE**: The fix has been implemented. We now use a "lazy muCore transformation" that:
1. Maps stack slot symbol IDs to value terms in `ParamValueMap`
2. Intercepts loads from parameter stack slots in `handleLoad`
3. Returns the parameter value directly without resource tracking

This matches CN's `C_vars.Value` pattern from `cn/lib/compile.ml`.

See:
- `Monad.lean`: Added `ParamValueMap` type and accessors
- `Action.lean:265-282`: Modified `handleLoad` to check for parameter loads
- `Params.lean`: Sets up the mapping when processing function parameters

## CN's Approach (core_to_mucore.ml)

### Key Data Structure: C_vars

```ocaml
(* compile.ml lines 329-334 *)
type state =
  | Value of Sym.t * SBT.t  (* the variable is a pure value *)
  | Points_to of IT.Surface.t  (* the variable points to memory *)
```

### How Parameters Are Set Up (make_function_args)

```ocaml
(* core_to_mucore.ml lines 745-755 *)
| ((mut_arg, (mut_arg', ct)), (pure_arg, cbt)) :: rest ->
    (* mut_arg = Core stack slot symbol *)
    (* pure_arg = muCore value symbol *)
    let arg_state = Translate.C_vars.Value (pure_arg, sbt) in
    let st = Translate.C_vars.add [ (mut_arg, arg_state) ] st in
    (* Maps: stack_slot -> Value(pure_value, type) *)
```

### How Loads Are Handled (compile.ml)

```ocaml
(* compile.ml line 1305 *)
| C_vars.Value (sym', sbt) -> IT.sym_ (sym', sbt, loc)
```

When a load from a parameter stack slot is encountered:
1. Look up the stack slot symbol in C_vars state
2. Find `Value(pure_sym, sbt)`
3. Return `IT.sym_(pure_sym, sbt, loc)` - **the value directly, no load!**

### Key Insight

**CN eliminates loads from parameter stack slots at compile time.** The load is replaced with a pure symbol reference. No resource tracking is involved for parameters.

## Our Approach (Params.lean) - Discrepancy

We tried to:
1. Create implicit `Owned<T>(stack_slot)` resources
2. Handle loads via normal resource consumption

### Why This Fails

1. In the body: `load(T, a_530)` where `a_530` is an alias of parameter `p`
2. `handleLoad` creates predicate with `pointer := term_for_a_530`
3. Our resource has `pointer := term_for_p` (original param, not alias)
4. Resource matching fails - different pointer terms

Even without aliasing, the approach is conceptually wrong:
- CN doesn't track resources for parameter stack slots
- Parameters are VALUES in muCore, not memory locations

## Correct Fix

Match CN's `C_vars` approach:

### 1. Track Parameter Value Mapping

```lean
/-- Maps stack slot symbol ID → (value symbol, value base type) -/
abbrev ParamValueMap := Std.HashMap Nat (Sym × BaseType)
```

### 2. Resolve Aliases to Values

When checking a load:
1. If pointer is a parameter stack slot (or alias), return value directly
2. No resource consumption for parameter loads

### 3. Where to Hook In

**Option A**: In `checkPexpr` when resolving symbols
- Intercept at symbol resolution level
- If symbol is alias of param, return value term

**Option B**: In `handleLoad`
- Check if pointer resolves to a parameter
- If so, return the value term without resource tracking

Option B is cleaner as it keeps the transformation localized to loads.

## Implementation Plan

1. Add `ParamValueMap` and alias information to `TypingState`
2. Modify `handleLoad` to check for parameter loads:
   ```lean
   def handleLoad ... := do
     let ptr ← checkPexpr ptrPe
     -- Check if this is a load from parameter stack slot
     if let some (valueSym, valueBt) ← resolveParamLoad ptr then
       return AnnotTerm.mk (.sym valueSym) valueBt loc
     -- Otherwise, normal resource-based load
     ...
   ```
3. Remove implicit resource creation for parameters
4. The spec's `take v = Owned<int>(p)` refers to `p` as the parameter VALUE (a pointer), not the stack slot

## Test Case Analysis

```c
int get_value(int *p)
/*@ requires take v = Owned<int>(p);
    ensures take v2 = Owned<int>(p);
            v == v2;
            return == v; @*/
{ return *p; }
```

Here `p` is a pointer parameter. The spec says "I have ownership of `*p`".

- **Core IR**: `p` is stack slot address, `load(ptr_type, p_slot)` gives pointer value
- **muCore/CN**: `p` IS the pointer value (after transformation)
- **Spec**: `Owned<int>(p)` where `p` is the pointer value

So the transformation should:
1. Map Core's `p_stack_slot` to muCore's `p_value` (the pointer)
2. Loads from `p_stack_slot` return `p_value` directly
3. Spec's `p` refers to `p_value`
4. `Owned<int>(p)` is ownership of memory at address `p_value`

## Files to Modify

- `CN/TypeChecking/Params.lean` - Simplify, remove resource creation
- `CN/TypeChecking/Monad.lean` - Add param value map to state (or pass through context)
- `CN/TypeChecking/Action.lean` - Modify `handleLoad` to check for parameter loads
