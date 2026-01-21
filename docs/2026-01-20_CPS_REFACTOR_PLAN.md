# CPS Refactor Plan for CN Type Checker

## Summary

Our current Hoare-style type checker requires branches to converge to the same resource structure. CN uses continuation-passing style (CPS) where each branch is verified independently to the function's postcondition. This document outlines the refactor to match CN's approach.

## Key Insight: CN's Branch Handling

In CN (`check.ml` lines 1985-2002), the `Eif` case:

```ocaml
| Eif (c_pe, e1, e2) ->
  check_pexpr c_pe (fun carg ->
    let aux lc _nm e =
      let@ () = add_c loc (LC.T lc) in
      check_expr labels e k
    in
    let@ () = pure (aux carg "true" e1) in
    let@ () = pure (aux (not_ carg loc) "false" e2) in
    return ())
```

Key observations:
1. **Both branches call the same continuation `k`** - no convergence check
2. **`pure` discards state changes** - each branch is speculatively checked
3. **Branch constraints are isolated** - `pure` restores state after checking

## Current vs. Target Design

### Current (Hoare-style)
```lean
partial def checkExpr (e : AExpr) : TypingM IndexTerm

-- If handling
| .if_ cond thenE elseE =>
  let savedState ← TypingM.getState
  let _thenResult ← withPathCondition condVal (checkExpr thenE)
  let thenCtx ← TypingM.getContext
  TypingM.setState savedState
  let elseResult ← withPathCondition (negTerm condVal) (checkExpr elseE)
  let elseCtx ← TypingM.getContext
  checkResourcesMatch thenCtx elseCtx  -- BRANCHES MUST CONVERGE
  return elseResult
```

### Target (CN CPS-style)
```lean
partial def checkExpr (e : AExpr) (k : IndexTerm → TypingM Unit) : TypingM Unit

-- If handling
| .if_ cond thenE elseE =>
  checkPexpr cond fun condVal => do
    let aux (cond : IndexTerm) (e : AExpr) : TypingM Unit := do
      TypingM.addC (.t cond)
      checkExpr e k  -- Both branches call same k
    TypingM.pure_ (aux condVal thenE)
    TypingM.pure_ (aux (negTerm condVal) elseE)
```

## Benefits of CPS Approach

1. **Multiple exit paths**: Early returns naturally work - they just call the postcondition continuation
2. **No artificial constraints**: Branches don't need same resource structure
3. **Match CN semantics**: Easier to reason about correspondence
4. **Path-sensitive**: Each path is verified independently with its own constraints

## Refactor Steps

### Step 1: Update Function Signatures

Change from:
```lean
partial def checkExpr (e : AExpr) : TypingM IndexTerm
partial def checkPexpr (pe : APexpr) : TypingM IndexTerm
partial def checkAction (pact : Paction) : TypingM IndexTerm
```

To:
```lean
partial def checkExpr (e : AExpr) (k : IndexTerm → TypingM Unit) : TypingM Unit
partial def checkPexpr (pe : APexpr) (k : IndexTerm → TypingM Unit) : TypingM Unit
partial def checkAction (pact : Paction) (k : IndexTerm → TypingM Unit) : TypingM Unit
```

### Step 2: Update Expression Cases

**Pure expression:**
```lean
-- Before
| .pure pe => checkPexpr pe

-- After
| .pure pe => checkPexpr pe k
```

**Weak sequencing:**
```lean
-- Before
| .wseq pat e1 e2 =>
  let v1 ← checkExpr e1
  let bindings ← bindPattern pat v1
  let result ← checkExpr e2
  unbindPattern bindings
  return result

-- After
| .wseq pat e1 e2 =>
  checkExpr e1 fun v1 => do
    let bindings ← bindPattern pat v1
    checkExpr e2 fun result => do
      unbindPattern bindings
      k result
```

**If-then-else:**
```lean
-- Before (requires convergence)
| .if_ cond thenE elseE =>
  let condVal ← checkPexpr cond
  let savedState ← TypingM.getState
  let _thenResult ← withPathCondition condVal (checkExpr thenE)
  let thenCtx ← TypingM.getContext
  TypingM.setState savedState
  let elseResult ← withPathCondition (negTerm condVal) (checkExpr elseE)
  let elseCtx ← TypingM.getContext
  checkResourcesMatch thenCtx elseCtx
  return elseResult

-- After (independent paths)
| .if_ cond thenE elseE =>
  checkPexpr cond fun condVal => do
    let checkBranch (cond : IndexTerm) (e : AExpr) : TypingM Unit := do
      TypingM.addC (.t cond)
      checkExpr e k
    TypingM.pure_ (checkBranch condVal thenE)
    TypingM.pure_ (checkBranch (negTerm condVal) elseE)
```

### Step 3: Update Top-Level Entry Point

```lean
/-- Check a function body against its specification.
    The continuation verifies the postcondition at each exit point. -/
def checkFunctionBody (spec : FunctionSpec) (body : AExpr) : TypeCheckResult :=
  let postconditionK (retVal : IndexTerm) : TypingM Unit := do
    -- Bind return value in postcondition
    processPostcondition spec.ensures retVal
    -- Verify all constraints
    verifyConstraints
    -- Check no resources leaked
    checkNoLeakedResources

  let computation : TypingM Unit := do
    processPrecondition spec.requires
    checkExpr body postconditionK

  runTypingM computation
```

### Step 4: Remove `checkResourcesMatch`

This function becomes unnecessary - branches don't need to converge.

## Files to Modify

| File | Changes |
|------|---------|
| `Expr.lean` | Update `checkExpr` signature and all cases (~300 lines) |
| `Pexpr.lean` | Update `checkPexpr` signature and all cases (~150 lines) |
| `Action.lean` | Update `checkAction` signature and cases (~100 lines) |
| `Check.lean` | Update entry points and postcondition handling (~50 lines) |

**Total**: ~600 lines affected

## Verification: `pure_` Must Discard State

Critical: our `pure_` must restore state after running the computation:

```lean
/-- Run a computation without modifying the state (for speculative checking)
    Corresponds to: pure in typing.ml lines 67-72 -/
def pure_ (m : TypingM α) : TypingM α := do
  let s ← getState
  let result ← m
  setState s  -- CRITICAL: restore state, discarding any changes
  return result
```

This is already correct in `Monad.lean`.

## Test Implications

1. **030-branch-mismatch.fail.c**: With CPS, this might PASS because branches don't need to converge. Need to verify what CN does here.

2. **New test needed**: Early return in one branch, normal flow in other - should pass with CPS.

## Migration Strategy

Option A: **Big bang refactor**
- Change all signatures at once
- Temporarily break compilation
- Fix all callers
- Risk: Hard to debug if something goes wrong

Option B: **Incremental with compatibility layer** (Recommended)
- Add new CPS functions alongside existing ones (e.g., `checkExprK`)
- Update callers one at a time
- Delete old functions when all callers migrated
- Safer but more code churn

## Decision Needed

Before implementing, verify:
1. What does CN do with `030-branch-mismatch.fail.c`? Does it pass or fail?
2. How does CN handle function postconditions that require specific resources?

If CN passes `030-branch-mismatch.fail.c`, then our test expectation was wrong.
