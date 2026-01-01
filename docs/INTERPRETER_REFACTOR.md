# Interpreter Refactor: Small-Step Semantics

## Critical Requirement: Exact Correspondence with Cerberus

**The Lean interpreter MUST mirror Cerberus semantics EXACTLY.**

- Each function must be auditable against the corresponding Cerberus code
- No innovation or "improvements" - only faithful translation
- Any deviation from Cerberus must be explicitly signed off by the user
- When in doubt, copy Cerberus's approach exactly

This is not about writing "good Lean code" - it's about creating a verifiable translation that can be audited for correctness against the Cerberus reference implementation.

## Validation Process

For each interpreter function:

1. **Identify Cerberus source**: Document the exact file and line numbers in Cerberus
2. **Translate faithfully**: Match the structure, not just the behavior
3. **Document correspondence**: Add comments linking Lean code to Cerberus code
4. **Audit**: Verify the translation matches case-by-case
5. **Sign-off**: Get user approval for any necessary deviations

### Correspondence Documentation Format

Each Lean function should have a header comment like:
```lean
/-- Corresponds to: cerberus/frontend/model/core_run.lem lines 1509-1529
    Function: Erun case in core_thread_step2
    Audited: [DATE] or "PENDING"
    Deviations: None (or list any with justification)
-/
```

## Problem

The current big-step interpreter has fundamental issues with control flow, particularly:
- Recursive function calls return wrong values
- The `save`/`run` mechanism for returns doesn't work correctly

The root cause is that big-step semantics don't match Cerberus's execution model. Cerberus uses **small-step operational semantics** with an explicit stack and continuation-based control flow.

### Why Big-Step Can't Be Fixed

The fundamental issue is how `save`/`run` works. In Cerberus's `collect_labeled_continuations` (core_aux.lem:1901-1906):

```lem
| Esseq pat e1 e2 ->
    Map.union
      (Map.map (fun (params, e) -> (params, Esseq pat e e2))  -- WRAP!
               (collect_labeled_continuations e1))
      (collect_labeled_continuations e2)
```

When `save` is inside `e1` of `sseq pat e1 e2`, the continuation body is **wrapped to include `e2`**. This means when `run` jumps to the continuation, it executes the continuation body AND THEN continues with `e2`.

In our big-step interpreter:
- `save` just executes its body
- `run` throws an exception to escape
- The exception bypasses `sseq`'s `e2` entirely

Big-step semantics fundamentally cannot express "jump to this point in the code and then continue normally." The continuation wrapping IS the mechanism that makes this work in Cerberus.

## Code Reuse Analysis

### KEEP (reusable as-is or with minor changes)

1. **`Monad.lean`** - Almost all of it:
   - `UB` type
   - `InterpError` type
   - `InterpEnv`, `InterpState`
   - `InterpM` monad and all its helpers (`getFile`, `getMemory`, `liftMem`, `throwUB`, etc.)
   - Remove `catchReturn` (failed fix attempt)

2. **`Env.lean`** - Symbol environment:
   - `EvalEnv` structure
   - `bind`, `bindAll`, `lookup`
   - Continuation collection (`withConts`, `lookupCont`) - wrapping logic needs fixing

3. **`Eval.lean`** - Pure expression evaluation (`evalPexpr`):
   - Big-step is **correct for pure expressions** - Cerberus's `eval_pexpr` is also essentially big-step
   - All operator implementations, constructors, pattern matching
   - Needs audit against `core_eval.lem`

4. **`Interpreter.lean`** - Entry point structure:
   - `InterpResult`, `runMain` structure
   - `extractReturnInt`
   - Will need modification but scaffolding is useful

### REPLACE (fundamentally broken)

1. **`Exec.lean`** - The `execExpr` function:
   - This is where big-step breaks down
   - Replace with small-step `step` function
   - `execAction` can probably be kept (memory operations)
   - `execBuiltin` can be kept
   - `callProc` logic is fine, just needs to push stack frame

### NEW (need to create)

1. **`State.lean`** - Thread state with explicit stack:
   - `ContElem`, `Continuation`, `Stack`, `ThreadState`
   - Stack manipulation functions

2. **`Step.lean`** - Single-step execution:
   - `step : ThreadState → InterpM StepResult`
   - Driver loop

### Summary

~60-70% of the code is reusable. The core issue is only in `execExpr` - the recursive structure that can't handle `save`/`run` properly. Everything else (monad, env, pure eval, memory actions, builtins) is fine.

## Cerberus Architecture

### Key Data Structures

From `cerberus/frontend/model/core_run_aux.lem`:

```
(* Thread state *)
type thread_state = <|
  arena: expr;           (* Current expression being evaluated *)
  stack: stack;          (* Call stack with continuations *)
  env: list (map Sym Value);  (* Scoped symbol environment *)
  ...
|>

(* Stack *)
type stack =
  | Stack_empty
  | Stack_cons (maybe Sym) continuation stack  (* proc_sym, cont, parent *)
  | Stack_cons2 ...

(* Continuation - what to do with the result *)
type continuation = list cont_elem

type cont_elem =
  | Ksseq Pattern Expr    (* Strong sequence: bind result, continue with Expr *)
  | Kwseq Pattern Expr    (* Weak sequence *)
  | Kcase ...             (* Case continuation *)
```

### Execution Model

From `cerberus/frontend/model/core_run.lem`:

**Single step** transforms `thread_state` → `thread_state`:

1. **Evaluate current arena** (the expression being worked on)
2. **Apply continuation** when arena becomes a value
3. **Manage stack** for procedure calls/returns

### Procedure Call (`Eccall`/`Eproc`)

Lines 958-970, 1029-1041:
```
Step_tau "Eccall" ... (
  call_proc ... >>= fun (proc_env, expr) ->
  return <| th_st with
    arena= expr;                                    (* Set arena to procedure body *)
    stack= push_empty_continuation (Just psym) sk;  (* Push new stack frame *)
    env= proc_env :: th_st.env                      (* Push new env scope *)
  |>
)
```

Key points:
- `call_proc` returns `(env, body)` - parameter bindings and procedure body
- **Push empty continuation** `[]` marks the call boundary
- **Push env scope** for the new procedure
- **Set arena** to procedure body

### Return via `Erun`

Lines 1509-1529:
```
| (Erun annots sym pes, Stack_cons (Just current_proc) cont sk) ->
    lookup labeled continuation for sym >>= fun (sym_bTys, cont_expr) ->
    let cont_expr' = substitute args into cont_expr
    return <| th_st with
      arena= cont_expr';                                  (* Jump to continuation *)
      stack= push_empty_continuation (Just current_proc) sk;  (* Push frame *)
    |>
```

Key insight: `Erun` doesn't "throw" - it **replaces the arena** with the continuation body (which includes everything that should happen after the return point).

### Labeled Continuations

From `cerberus/frontend/model/core_aux.lem` lines 1880-1910:

The `collect_labeled_continuations` function traverses the AST and builds a map from labels to continuation bodies. Critically, for sequences:

```
| Esseq pat e1 e2 ->
    Map.union
      (Map.map (fun (params, e) -> (params, Esseq pat e e2))  (* Wrap with rest! *)
               (collect_labeled_continuations e1))
      (collect_labeled_continuations e2)
```

When a `save` is inside `e1` of `sseq pat e1 e2`, its continuation body is **wrapped** to include `e2`. This means when `run` jumps to the continuation, it will execute `e2` after finishing the continuation.

### End of Procedure

Lines 1573-1598:
```
| (Epure value, Stack_cons current_proc [] (Stack_cons parent_proc cont sk')) ->
    (* Empty continuation [] means we hit procedure boundary *)
    return <| th_st with
      arena= apply_continuation cont (Epure value);  (* Apply parent's continuation *)
      stack= Stack_cons parent_proc [] sk';          (* Pop to parent frame *)
      env= tail th_st.env                            (* Pop env scope *)
    |>
```

When we reach a value with an empty continuation `[]`, we've finished the current procedure. Pop the stack frame and apply the parent's waiting continuation.

## Refactor Plan

### Phase 1: Data Structures

Create `lean/CToLean/Semantics/State.lean`:

```lean
/-- Continuation element - what to do with a result -/
inductive ContElem where
  | ksseq : APattern → Expr → ContElem   -- Strong sequence
  | kwseq : APattern → Expr → ContElem   -- Weak sequence
  | kcase : List (APattern × Expr) → ContElem  -- Case branches remaining
  | kif : Expr → Expr → ContElem         -- If branches (for effectful condition)
  deriving Repr, Inhabited

/-- Continuation - list of things to do with results -/
abbrev Continuation := List ContElem

/-- Stack frame -/
structure StackFrame where
  procSym : Option Sym      -- Current procedure (None for top-level)
  cont : Continuation       -- What to do when arena becomes a value
  deriving Repr, Inhabited

/-- Execution stack -/
abbrev Stack := List StackFrame

/-- Thread state -/
structure ThreadState where
  arena : AExpr             -- Current expression being evaluated
  stack : Stack             -- Call stack
  env : List (HashMap Sym Value)  -- Scoped symbol bindings
  labeledConts : HashMap Sym (List (Sym × BaseType) × Expr)  -- Pre-collected continuations
  deriving Inhabited
```

### Phase 2: Core Step Function

Create `lean/CToLean/Semantics/Step.lean`:

```lean
/-- Result of a single step -/
inductive StepResult where
  | step : ThreadState → StepResult      -- Continue with new state
  | done : Value → StepResult            -- Program finished
  | error : InterpError → StepResult     -- Error occurred
  deriving Inhabited

/-- Take a single step of execution -/
def step (st : ThreadState) : InterpM StepResult := do
  match st.arena.expr with
  | .pure pe =>
    -- Try to evaluate to a value
    match valueFromPexpr pe with
    | some v => applyStackContinuation st v
    | none =>
      let v ← evalPexpr st.env pe
      pure (.step { st with arena := mkPure v })

  | .sseq pat e1 e2 =>
    -- Push continuation and focus on e1
    let cont' := .ksseq pat e2 :: currentCont st
    pure (.step { st with
      arena := e1
      stack := updateCont st.stack cont' })

  | .save (label, _) params body =>
    -- Substitute default values and continue with body
    let body' ← substituteDefaults st.env params body
    pure (.step { st with arena := body' })

  | .run label args =>
    -- Jump to labeled continuation
    match st.labeledConts.find? label with
    | none => pure (.error (.illformedProgram s!"run: label {label.name} not found"))
    | some (params, contBody) =>
      let argVals ← args.mapM (evalPexpr st.env)
      let body' := substituteArgs params argVals contBody
      -- Push empty continuation to mark return point
      let stack' := pushEmptyFrame st.stack
      pure (.step { st with arena := body', stack := stack' })

  | .ccall funPtr _ argExprs =>
    -- Function call - evaluate to values first, then call
    ...

/-- Apply stack continuation when arena is a value -/
def applyStackContinuation (st : ThreadState) (v : Value) : InterpM StepResult := do
  match st.stack with
  | [] =>
    -- Empty stack - program done
    pure (.done v)

  | frame :: rest =>
    match frame.cont with
    | [] =>
      -- Empty continuation - end of procedure, return to caller
      match rest with
      | [] => pure (.done v)  -- No caller - done
      | parentFrame :: grandparent =>
        -- Apply parent's continuation with return value
        applyContElem parentFrame.cont v { st with
          stack := parentFrame :: grandparent
          env := st.env.tail  -- Pop env scope
        }

    | contElem :: contRest =>
      applyContElem contElem v { st with
        stack := { frame with cont := contRest } :: rest
      }

/-- Apply a single continuation element -/
def applyContElem (elem : ContElem) (v : Value) (st : ThreadState) : InterpM StepResult :=
  match elem with
  | .ksseq pat e2 =>
    match matchPattern pat v with
    | none => pure (.error .patternMatchFailed)
    | some bindings =>
      let env' := bindAll st.env bindings
      pure (.step { st with arena := e2, env := env' })
  | .kwseq pat e2 =>
    -- Same as ksseq for sequential execution
    ...
```

### Phase 3: Procedure Calls

```lean
/-- Handle procedure call -/
def callProcedure (st : ThreadState) (sym : Sym) (args : List Value) : InterpM StepResult := do
  let file ← InterpM.getFile
  match lookupProc file sym with
  | some (params, body) =>
    -- Build parameter bindings
    let bindings := params.zip args |>.map fun ((p, _), v) => (p, v)
    let procEnv := HashMap.ofList bindings
    -- Collect labeled continuations for this procedure
    let labeledConts := collectLabeledContinuations body
    -- Push new stack frame with empty continuation
    let newFrame : StackFrame := { procSym := some sym, cont := [] }
    pure (.step {
      arena := body
      stack := newFrame :: st.stack
      env := procEnv :: st.env
      labeledConts := labeledConts
    })
  | none => pure (.error (.symbolNotFound sym))
```

### Phase 4: Driver Loop

```lean
/-- Run program to completion -/
partial def run (st : ThreadState) : InterpM Value := do
  match ← step st with
  | .done v => pure v
  | .error e => throw e
  | .step st' => run st'
```

### Phase 5: Collect Labeled Continuations

Port `collect_labeled_continuations` exactly:

```lean
/-- Collect all labeled continuations from an expression.
    Critical: for sequences, wrap continuations to include the rest of the sequence. -/
partial def collectLabeledContinuations (e : AExpr) : HashMap Sym (List (Sym × BaseType) × Expr) :=
  match e.expr with
  | .pure _ => {}
  | .memop _ _ => {}
  | .action _ => {}

  | .sseq pat e1 e2 =>
    -- Key insight: continuations in e1 need to include e2!
    let conts1 := collectLabeledContinuations ⟨[], e1⟩
    let conts1' := conts1.map fun (params, body) =>
      (params, Expr.sseq pat body e2)  -- Wrap with e2!
    let conts2 := collectLabeledContinuations ⟨[], e2⟩
    conts1'.merge conts2

  | .wseq pat e1 e2 =>
    -- Same wrapping logic
    ...

  | .save (label, _) params body =>
    let innerConts := collectLabeledContinuations ⟨[], body⟩
    innerConts.insert label (params.map fun (s, ty, _) => (s, ty), body)

  | .if_ _ e1 e2 =>
    (collectLabeledContinuations ⟨[], e1⟩).merge (collectLabeledContinuations ⟨[], e2⟩)

  | _ => {}
```

## Key Differences from Current Implementation

1. **Explicit stack** instead of implicit call stack via recursion
2. **Continuations wrap subsequent code** - `save` inside `sseq e1 e2` includes `e2`
3. **`run` doesn't throw** - it modifies arena and pushes empty frame
4. **Procedure return** detected by empty continuation `[]`
5. **Step-by-step execution** allows debugging and matches Cerberus exactly

## Testing Strategy

1. Start with simplest cases: `001-return-literal.c`
2. Add `sseq` handling: `007-local-var.c`
3. Add function calls: `016-func-simple.c`
4. Add recursion: `017-func-recursive.c` (the failing case)
5. Verify with `tests/debug/rec-*.c` progression

## Files to Modify/Create

- `lean/CToLean/Semantics/State.lean` - New data structures
- `lean/CToLean/Semantics/Step.lean` - Core step function
- `lean/CToLean/Semantics/Exec.lean` - Replace with step-based execution
- `lean/CToLean/Semantics/Interpreter.lean` - Update entry point

## References

- `cerberus/frontend/model/core_run.lem` - Main execution semantics
- `cerberus/frontend/model/core_run_aux.lem` - Data structures, stack operations
- `cerberus/frontend/model/core_aux.lem` - `collect_labeled_continuations`
- `cerberus/frontend/model/core_eval.lem` - Pure expression evaluation

## Audit Checklist

### Data Structures (State.lean)

| Lean Type | Cerberus Source | File:Lines | Audited |
|-----------|-----------------|------------|---------|
| `ContElem` | `cont_elem` | core_run_aux.lem:~50-60 | PENDING |
| `Continuation` | `continuation` | core_run_aux.lem:~45 | PENDING |
| `StackFrame` | Part of `stack` | core_run_aux.lem:~70-80 | PENDING |
| `Stack` | `stack` | core_run_aux.lem:~70-80 | PENDING |
| `ThreadState` | `thread_state` | core_run_aux.lem:~90-110 | PENDING |

### Core Functions (Step.lean)

| Lean Function | Cerberus Function | File:Lines | Audited |
|---------------|-------------------|------------|---------|
| `step` | `core_thread_step2` | core_run.lem:~800-1650 | PENDING |
| `applyStackContinuation` | `Epure` cases | core_run.lem:~1540-1616 | PENDING |
| `applyContElem` | `apply_continuation` | core_run_aux.lem:~160-200 | PENDING |
| `collectLabeledContinuations` | `collect_labeled_continuations` | core_aux.lem:1880-1931 | PENDING |

### Expression Cases in step()

| Case | Cerberus Location | Audited |
|------|-------------------|---------|
| `Epure` | core_run.lem:1540-1616 | PENDING |
| `Esseq` | core_run.lem:1470-1488 | PENDING |
| `Ewseq` | core_run.lem:~1450-1470 | PENDING |
| `Eif` | core_run.lem:~1300-1350 | PENDING |
| `Ecase` | core_run.lem:~1350-1400 | PENDING |
| `Eaction` | core_run.lem:~1200-1300 | PENDING |
| `Esave` | core_run.lem:1491-1501 | PENDING |
| `Erun` | core_run.lem:1503-1529 | PENDING |
| `Eccall` | core_run.lem:~900-1000 | PENDING |
| `Eproc` | core_run.lem:1002-1042 | PENDING |
| `Ebound` | core_run.lem:1643-1649 | PENDING |
| `Eunseq` | core_run.lem:~1400-1450 | PENDING |

### Helper Functions

| Lean Function | Cerberus Function | File:Lines | Audited |
|---------------|-------------------|------------|---------|
| `callProc` | `call_proc` | core_run.lem:30-70 | PENDING |
| `pushEmptyFrame` | `push_empty_continuation` | core_run_aux.lem:139-142 | PENDING |
| `matchPattern` | `match_pattern` | core_aux.lem:~1700-1800 | PENDING |
| `evalPexpr` | `eval_pexpr` | core_eval.lem:~100-500 | PENDING |
