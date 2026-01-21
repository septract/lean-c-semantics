# CN Type System Implementation Plan

## The Two Levels of Type Checking in CN

CN has **two distinct but integrated** type checking systems:

### Level 1: Traditional Type Checking (wellTyped.ml)

**Purpose**: Verify that CN index terms and assertions are well-typed with respect to base types.

**What it checks**:
- Is this term a `Bool`? An `Integer`? A `Loc` (pointer)?
- Do operands have compatible types? (`x + y` requires both to be numeric)
- Are patterns complete and non-redundant?
- Do function arguments match expected types?

**Key functions in CN OCaml**:
```ocaml
type 'a t = Context.t -> ('a * Context.t, error) Result.t

ensure_base_type : loc -> expect:BT.t -> BT.t -> unit t
ensure_bits_type : loc -> BT.t -> unit t
check_term : loc -> BT.t -> term -> IT.t t     (* check term has expected type *)
infer_term : term -> IT.t t                     (* infer term's type *)
```

**This is necessary but NOT sufficient** - a well-typed program can still have memory safety bugs.

### Level 2: Separation Logic Verification (check.ml)

**Purpose**: Verify memory safety by tracking resource ownership through program execution.

**What it checks**:
- Does the function have permission to read/write memory locations?
- Are resources properly consumed and produced?
- Do postconditions follow from preconditions + execution?

**Key functions in CN OCaml**:
```ocaml
check_expr : labels -> expr -> (IT.t -> unit m) -> unit m
check_pexpr : pexpr -> (IT.t -> unit m) -> unit m
predicate_request : loc -> situation -> predicate -> (predicate * output) m
```

**This IS the verification system** - it implements separation logic as a refinement type system.

### How They Integrate: The Lift Pattern

CN uses a clever architecture where Level 1 is **embedded inside** Level 2:

```
┌─────────────────────────────────────────────────┐
│ Level 2: check.ml (Separation Logic)            │
│                                                 │
│   check_expr e (fun result ->                   │
│     (* First: Level 1 type checking *)          │
│     let@ () = WellTyped.ensure_base_type ... in │
│                                                 │
│     (* Then: Level 2 SL verification *)         │
│     let@ resource = predicate_request ... in    │
│     ...                                         │
│   )                                             │
└─────────────────────────────────────────────────┘
                    │
                    │ uses Lift functor
                    ▼
┌─────────────────────────────────────────────────┐
│ Level 1: wellTyped.ml (Basic Type Checking)     │
│                                                 │
│   module Lift(M : ErrorReader) = struct         │
│     let ensure_base_type loc ~expect has =      │
│       let@ context = M.get_context () in        │
│       M.lift (run context (check has expect))   │
│   end                                           │
└─────────────────────────────────────────────────┘
```

The `Lift` functor takes a monad `M` that can:
- `get_context()` - access the typing context
- `lift` - convert WellTyped errors to M's error type

This allows WellTyped functions to run inside the Typing monad seamlessly.

## Separation Logic Correspondence

CN type checking implements separation logic proof rules:

| CN Operation | Separation Logic Rule |
|--------------|----------------------|
| `add_r` (produce resource) | Introduce assertion |
| `predicate_request` (consume resource) | Use assertion as precondition |
| Sequencing (`wseq`/`sseq`) | Composition rule |
| `pure` (speculative check) | Frame rule |
| Branch checking | Disjunction |
| Function call | Procedure call rule |

### Example: Store Operation

```
// Hoare triple for store:
{Owned<T>(Uninit)(p)}  *p = v  {Owned<T>(Init)(p) ∧ *p == v}
```

CN type checking for store:
1. **Consume** `Owned<T>(Uninit)(p)` from context (precondition)
2. **Produce** `Owned<T>(Init)(p)` with value `v` (postcondition)

### Example: Load Operation

```
// Hoare triple for load:
{Owned<T>(Init)(p) ∧ *p == v}  x = *p  {Owned<T>(Init)(p) ∧ *p == v ∧ x == v}
```

CN type checking for load:
1. **Consume** `Owned<T>(Init)(p)` from context, get value `v`
2. **Produce** `Owned<T>(Init)(p)` back with same value (non-destructive read)
3. **Return** the value `v`

## Current Implementation Assessment

### What We Have (Lean)

| File | Purpose | Level | Status |
|------|---------|-------|--------|
| `Context.lean` | Typing context data structure | Infrastructure | ✅ Complete |
| `Monad.lean` | TypingM monad + ProofOracle | Infrastructure | ✅ Complete (incl. ParamValueMap) |
| `Inference.lean` | Resource matching algorithm | Level 2 (SL) | ✅ Complete |
| `Check.lean` | Spec clause processing | Level 2 (SL) | ✅ Complete |
| `Pexpr.lean` | Pure expression → IndexTerm | Level 2 (SL) | ✅ Complete |
| `Action.lean` | Memory action checking | Level 2 (SL) | ✅ Complete |
| `Expr.lean` | Effectful expression walking | Level 2 (SL) | ✅ Complete (basic) |
| `Params.lean` | Function parameter handling | Level 2 (SL) | ✅ Complete |

### What's Working

**Level 1 (Traditional Type Checking)**:
- IndexTerms are typed by construction (carry `bt : BaseType`)
- No explicit runtime type checking needed - construction-time typing is sufficient

**Level 2 (Separation Logic - Core Walking)**:
- ✅ `check_expr` - walk effectful Core expressions
- ✅ `check_pexpr` - walk pure Core expressions
- ✅ Memory action handling (create, kill, store, load)
- ✅ Pattern matching and variable binding
- ✅ Resource leak detection at function end
- ✅ Lazy muCore transformation for parameters

### Remaining Work

- Branch resource checking (both branches should agree)
- Non-deterministic choice (check all branches)
- Function calls with specifications
- Representability checks

## Implementation Plan

### Phase 1: Core Expression Walking (Level 2)

This is the main work. Implement `check_expr` that walks Core expressions.

#### File: `CN/Typing/Pexpr.lean` (~200 lines)

Convert Core pure expressions to CN index terms:
- Variable lookup
- Literal values
- Binary operations
- Conditionals
- Let bindings
- Member access
- Function calls

#### File: `CN/Typing/Action.lean` (~150 lines)

Handle memory actions with resource tracking:
- `create` → produce `Owned<T>(Uninit)`
- `kill` → consume `Owned<T>(Uninit)`
- `store` → consume `Uninit`, produce `Init`
- `load` → consume/produce `Init`, return value

#### File: `CN/Typing/Expr.lean` (~300 lines)

Walk effectful Core expressions:
- `pure` → delegate to checkPexpr
- `action` → delegate to checkAction
- `wseq`/`sseq` → thread resources through sequence
- `let_` → bind value, check body
- `if_` → check both branches with path conditions
- `ccall` → use callee's spec
- `case_` → check all branches

#### File: `CN/Typing/Check.lean` (update)

Wire everything together for function verification:
1. Process precondition (add initial resources)
2. Check body expression (walk Core, track resources)
3. Process postcondition (verify final resources)
4. Verify constraints
5. Check no resource leaks

### Phase 2: Integration and Testing

1. Update `CN/Typing.lean` to export new modules
2. Create test cases:
   - Simple allocate → store → load → free
   - Resource errors (use-after-free, double-free)
   - Memory leak detection
   - Conditional branching

## File Structure

```
CerbLean/CN/TypeChecking/
├── Context.lean      ✅ Done - typing context
├── Monad.lean        ✅ Done - typing monad + oracle + ParamValueMap
├── Inference.lean    ✅ Done - resource inference
├── Check.lean        ✅ Done - spec clause processing
├── Pexpr.lean        ✅ Done - pure expression checking
├── Action.lean       ✅ Done - memory action checking
├── Expr.lean         ✅ Done - effectful expression checking
├── Params.lean       ✅ Done - function parameter handling
└── TypeChecking.lean ✅ Done - re-exports
```

## Correspondence to CN OCaml

| Our File | CN OCaml File | Key Functions |
|----------|---------------|---------------|
| `Typing/Monad.lean` | `typing.ml` | State monad, provable |
| `Typing/Context.lean` | `context.ml` | add_a, add_l, add_c, add_r |
| `Typing/Inference.lean` | `resourceInference.ml` | predicate_request_scan |
| `Typing/Check.lean` | `check.ml` | bind_arguments, check_procedure |
| `Typing/Pexpr.lean` | `check.ml` | check_pexpr |
| `Typing/Action.lean` | `check.ml` | Eaction cases |
| `Typing/Expr.lean` | `check.ml` | check_expr |

## Success Criteria

1. **Level 1**: IndexTerms are well-typed by construction ✅ DONE

2. **Level 2**: Can verify simple functions with:
   - Memory allocation (`create`) ✅ DONE
   - Memory write (`store`) ✅ DONE
   - Memory read (`load`) ✅ DONE
   - Memory deallocation (`kill`) ✅ DONE (via free_proxy)
   - Sequential composition (`wseq`/`sseq`) ✅ DONE
   - Conditionals (`if`) ✅ DONE

3. **Error detection**:
   - Use-after-free: load/store after kill ✅ TESTED (011-use-after-free.fail.c)
   - Double-free: kill after kill ✅ TESTED (010-double-free.fail.c)
   - Memory leak: resources remain at function end ✅ TESTED (014-resource-leak.fail.c)
   - Uninitialized read: load before store ✅ TESTED (012-read-uninit.fail.c)

## Scope

**In scope (v0.1)**:
- `Owned<T>` predicates (Init/Uninit)
- Basic memory operations
- Sequential control flow
- Pure constraints

**Deferred**:
- Quantified predicates (`each`)
- User-defined predicates
- Loop invariants
- Function calls with specs
- Soundness proofs
