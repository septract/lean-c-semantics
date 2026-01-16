# Core Interpreter Design

This document describes the design of the Lean interpreter for Cerberus Core IR.

## Goal

Implement a Lean interpreter that matches Cerberus semantics closely enough for differential testing. Start with simple programs and incrementally expand coverage.

## Prerequisites

### OCaml Version for Cerberus Execution

Cerberus requires OCaml 4.14.1. It crashes with SIGSEGV (exit code 139) on OCaml 5.x.

**Solution**: Use `make cerberus-setup` to create a dedicated opam switch:

```bash
# First-time setup (creates cerberus-414 opam switch)
make cerberus-setup

# This will:
# 1. Create opam switch with OCaml 4.14.1
# 2. Install all dependencies
# 3. Pin and install Cerberus
# 4. Verify execution works
```

See `CLAUDE.md` for detailed manual setup instructions if needed.

## Architecture

### Cerberus Interpreter (Reference)

The Cerberus interpreter (`core_run.lem` + `core_eval.lem`) uses small-step operational semantics with:
- **Arena**: Current expression being evaluated
- **Stack**: Call stack with continuations (`Ksseq`, `Kwseq`, etc.)
- **Environment**: Symbol-to-value bindings (scoped as a list of maps)
- **Memory state**: Handled by the memory model

### Lean Interpreter (This Implementation)

We use **big-step semantics** rather than Cerberus's small-step approach. This is simpler to implement and sufficient for sequential programs.

## File Structure

```
lean/CToLean/Semantics/
├── Monad.lean       # Interpreter monad (State + Error + Reader)
├── Env.lean         # Environment and symbol lookup
├── Eval.lean        # Pure expression evaluation
├── Exec.lean        # Effectful expression execution
├── Builtin.lean     # Built-in functions (printf stub, etc.)
└── Interpreter.lean # Top-level entry point
```

## Core Types

### Interpreter Monad

```lean
structure InterpEnv where
  file : File                          -- Program being executed
  typeEnv : TypeEnv                    -- For sizeof/alignof

structure InterpState where
  memory : MemState                    -- Memory state
  stdout : String := ""                -- Captured stdout
  stderr : String := ""                -- Captured stderr

inductive InterpError where
  | undefinedBehavior (ub : UndefinedBehavior) (loc : Option Loc)
  | memoryError (err : MemError)
  | typeError (msg : String)
  | notImplemented (feature : String)
  | illformedProgram (msg : String)

abbrev InterpM := ReaderT InterpEnv (StateT InterpState (Except InterpError))
```

### Symbol Environment

```lean
structure SymEnv where
  scopes : List (HashMap Sym Value) := [{}]

def SymEnv.lookup (env : SymEnv) (sym : Sym) : Option Value
def SymEnv.bind (env : SymEnv) (sym : Sym) (val : Value) : SymEnv
def SymEnv.pushScope (env : SymEnv) : SymEnv
def SymEnv.popScope (env : SymEnv) : SymEnv
```

## Key Design Decisions

### 1. Big-Step vs Small-Step

Use big-step for simplicity. Cerberus's small-step is needed for:
- Concurrency (`Eunseq`, `Epar`) - out of scope
- Step-by-step debugging - not needed initially

### 2. Pattern Matching

```lean
def matchPattern (pat : APattern) (val : Value) : Option (List (Sym × Value))
def applyBindings (env : SymEnv) (bindings : List (Sym × Value)) : SymEnv
```

### 3. save/run for Return

Core uses `save`/`run` for return statements:
```
save ret_505: loaded integer (a_517: loaded integer:= Specified(0)) in
  ... ;
  run ret_505(return_value)
```

Implement as continuation-like control flow in the interpreter.

### 4. Unsequenced Evaluation

`Eunseq` evaluates expressions in nondeterministic order. For MVP:
- Evaluate left-to-right (deterministic)
- Note: This may miss UB from sequence point violations

## Mapping: Cerberus to Lean

| Cerberus | Lean |
|----------|------|
| `core_run_state` | `InterpState` |
| `thread_state.env` | `SymEnv` |
| `thread_state.arena` | Current expression (implicit in recursion) |
| `thread_state.stack` | Call stack (implicit in recursion) |
| `Core_eval.eval_pexpr` | `evalPexpr` |
| `Core_run.core_thread_step2` | `execExpr` |
| `call_proc` | `callProc` |
| `select_case` + `match_pattern` | `matchPattern` |

## Implementation Phases

### Phase 1: Minimal Interpreter

**Target**: Empty main, return const

**Pure Expression Cases** (`Eval.lean`):
- `val` - Return the value directly
- `sym` - Look up in environment
- `op` - Binary operations (arithmetic, comparison)
- `ctor` - Constructors (`Cspecified`, `Ctuple`, etc.)
- `case_` - Pattern matching
- `let_` - Local binding
- `if_` - Conditional
- `convInt` - Integer type conversion
- `wrapI` - Wrapping arithmetic
- `catchExceptionalCondition` - Overflow checking

**Effectful Expression Cases** (`Exec.lean`):
- `pure` - Evaluate inner pexpr
- `sseq` - Strong sequencing (let binding)
- `wseq` - Weak sequencing
- `bound` - Bounds marker
- `save`/`run` - Continuation capture and resume (for return)

**Target tests**:
- `0001-emptymain.c` - Returns 0 (implicit)
- `0002-return_const.c` - Returns 150 (arithmetic)

### Phase 2: Variables and Memory

**Target**: Local variables

**Memory Actions** (`Exec.lean`):
- `action` with `create` - Allocate local variable
- `action` with `store` - Write to memory
- `action` with `load` - Read from memory
- `action` with `kill` - End of scope deallocation

**Target tests**:
- `0004-return_var.c` - Local variable
- `0005-return_var_arith.c` - Variable arithmetic

### Phase 3: Control Flow

**Target**: Loops, conditionals

- `if_` - Effectful conditional
- Boolean operations
- Comparison operations

**Target tests**:
- `0008-cond_integer.c` - Conditional expression
- `0010-if_int.c` - If statement
- `0015-while_break.c` - While loop

### Phase 4: Function Calls

**Target**: Recursive functions

- `proc` - Call user-defined procedure
- `ccall` - C function call

**Target tests**:
- `0021-fact.c` - Recursive factorial

### Phase 5: Differential Testing

Compare Lean interpreter output against Cerberus `--exec --batch` results.

**Success Criteria**:

| Phase | Target | Test Count |
|-------|--------|------------|
| 1 | Empty main + return const | 2 |
| 2 | Local variables | 5 |
| 3 | Control flow | 10 |
| 4 | Function calls | 20 |
| 5 | Full CI suite | 80% of 121 |

## Reference Files

**Cerberus**:
- `cerberus/frontend/model/core_run.lem` - Execution semantics
- `cerberus/frontend/model/core_eval.lem` - Pure evaluation
- `cerberus/frontend/model/core_aux.lem` - Pattern matching, substitution
- `cerberus/frontend/model/mem_common.lem` - Memory operations

**Lean (existing)**:
- `lean/CToLean/Core/Expr.lean` - Expression types
- `lean/CToLean/Core/Value.lean` - Value types
- `lean/CToLean/Memory/Concrete.lean` - Memory implementation
- `lean/CToLean/Memory/Interface.lean` - Memory operations

## Out of Scope

- Concurrency (`Epar`, `Eunseq` with true nondeterminism)
- Floating point (beyond basic operations)
- Variadic functions
- Full stdlib (printf formatting, etc.)
- Atomic operations
- CHERI/PNVI memory models
