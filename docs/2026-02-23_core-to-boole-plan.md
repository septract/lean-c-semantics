# Cerberus Core → Boole Translation Plan

*Created: 2026-02-23*

## Goal

Translate programs from the Cerberus Core intermediate representation (as
formalized in CerbLean) into Boole verification programs, enabling formal
verification of C programs through SMT-based and Lean-based proof pipelines.

## Overview

**Source:** Cerberus Core IR — a formal intermediate representation for C semantics,
implemented in Lean 4 at `/Users/miked/Projects/CerbLean/`. Includes an interpreter
achieving 98%+ compatibility with the OCaml reference implementation.

**Target:** Boole — an intermediate verification language built on Strata/Core, with
Boogie-like syntax. Supports preconditions, postconditions, loop invariants,
quantifiers, and both SMT-based and Lean-based verification.

**Approach:** Build a Lean function that takes a Cerberus Core `File` (the top-level
program type) and produces a `Boole.Program` (or `Core.Program`, since they're
structurally identical in Strata). Construction is done directly via Lean
constructors — no need to go through the `#strata` text macro.

---

## 1. AST Comparison

### Cerberus Core (source)

**Key files** in `CerbLean/Core/`:

| File | Contents |
|------|----------|
| `Expr.lean` | `Pexpr` (pure), `Expr` (effectful), `Action` (memory) |
| `Types.lean` | `BaseType`, `ObjectType`, `CoreType`, `Binop`, `Iop`, `Memop` |
| `Value.lean` | `Value`, `MemValue`, `PointerValue`, `IntegerValue` |
| `Ctype.lean` | `Ctype_`, `IntegerType`, `Qualifiers` |
| `File.lean` | `File`, `FunDecl`, `GlobDecl`, `TagDef` |
| `MuCore.lean` | `LabelDef`, `MuProc`, `collectSaves`, `removeSave` |

**Program structure:**
```
File
├── funs : Map Sym FunDecl        -- function/procedure definitions
├── globs : List (Sym × GlobDecl) -- global variables
├── tagDefs : TagDefs             -- struct/union definitions
├── impl : ImplDefs               -- sizeof, alignof, int ranges
└── main : Option Sym             -- entry point
```

**Expression layers:**
1. `Pexpr` — pure: arithmetic, logic, pattern matching, struct/union ops
2. `Expr` — effectful: memory ops, sequencing, procedure calls, control flow
3. `Action` — memory: create, kill, load, store, fence, RMW

### Boole / Strata Core (target)

**Key files** in `.lake/packages/Strata/Strata/Languages/`:

| File | Contents |
|------|----------|
| `Boole/Boole.lean` | `Boole.Program`, `Boole.Decl`, `Boole.Procedure` |
| `Core/Program.lean` | `Core.Program`, `Core.Decl`, `Core.Procedure` |
| `Core/Expressions.lean` | `Expression.Expr` (lambda-based), `Expression.Ty` |
| `Core/Procedure.lean` | `Procedure.Header`, `Procedure.Spec` |

**Program structure:**
```
Boole.Program
├── decls : List Decl
    ├── var (name, type, init)     -- global variable
    ├── type (TypeDecl)            -- type declaration / alias
    ├── ax (Axiom)                 -- logical axiom
    ├── proc (Procedure)           -- procedure with spec + body
    └── func (Function)            -- pure function with body
```

**Boole.Procedure:**
```
Procedure
├── header : Header               -- name, inputs, outputs
├── spec : Spec                    -- requires, ensures, modifies
└── body : List Statement          -- sequential statements
```

**Boole statements:** assignment, if/else, while (with invariant), assert, assume,
call, labeled blocks, havoc, variable declarations.

**Boole expressions:** Based on Strata's lambda expression language (`LExpr`).
Integers, booleans, bitvectors, maps, arithmetic/logic/comparison operators,
quantifiers, function application, map indexing/update.

---

## 2. Type Mapping

### Initial (sequential, no provenance)

| Cerberus Core | Boole | Notes |
|---------------|-------|-------|
| `int`, `long`, etc. (signed) | `int` | Unbounded integer; use `bvN` for bounded |
| `unsigned int`, etc. | `int` | Or `bvN` for precise overflow semantics |
| `_Bool` | `bool` | Direct |
| `pointer` | `int` | Flat address model (no provenance) |
| `array(T, n)` | `Map int T'` | Index by integer offset |
| `struct_(tag)` | Multiple variables or `Map field_id T'` | See below |
| `union_(tag)` | Uninterpreted + axioms | Or last-written semantics |
| `void` | `unit` / omit | For return types |
| `BaseType.unit` | (none) | Effectful procedures returning unit |
| `BaseType.boolean` | `bool` | Direct |
| `BaseType.ctype` | (skip) | Type-as-value, not needed for verification |

### Struct encoding

**Option A — Flattened fields:** Each struct field becomes a separate Boole variable.
For `struct Point { int x; int y; }` at pointer `p`, generate:
```
var p_x : int;
var p_y : int;
```

**Option B — Map-based:** Use `Map field_id int` where `field_id` is an enum.
More compositional but requires encoding field identity.

**Recommendation:** Start with Option A for simplicity. Handles most C verification
patterns. Switch to Map-based when structs are passed by value or stored in arrays.

### Memory model

**Flat byte-addressable heap:**
```
type Heap := Map int int;
var heap : Heap;
```

**Load/store translation:**
```
// C: *p = v
heap[p] := v;

// C: x = *p
x := heap[p];
```

For multi-byte values, either:
- Abstract to word-level (one map entry per logical value) — simpler
- Model byte-level with `Map int byte` and encode/decode — faithful

**Recommendation:** Start with word-level abstraction. Most verification properties
don't depend on byte layout.

### Allocation tracking

```
type AllocMap := Map int bool;  // addr → is_allocated
var alloc : AllocMap;

// malloc(n): choose fresh addr, set alloc[addr] := true
// free(p): assert alloc[p]; alloc[p] := false
// deref(p): assert alloc[p]
```

---

## 3. Expression Translation

### Pure expressions (Pexpr → Boole expression)

| Cerberus `Pexpr` | Boole |
|-------------------|-------|
| `sym s` | Variable reference `s` |
| `val (integer v)` | Integer literal `v` |
| `val (true_)` / `val (false_)` | `true` / `false` |
| `op add e1 e2` | `e1' + e2'` |
| `op sub e1 e2` | `e1' - e2'` |
| `op mul e1 e2` | `e1' * e2'` |
| `op div e1 e2` | `e1' / e2'` |
| `op eq e1 e2` | `e1' == e2'` |
| `op lt e1 e2` | `e1' < e2'` |
| `op and e1 e2` | `e1' && e2'` |
| `op or e1 e2` | `e1' \|\| e2'` |
| `not_ e` | `!e'` |
| `if_ c t e` | `if c' then t' else e'` |
| `let_ pat e1 e2` | Let-binding (inline or temp variable) |
| `case_ scrut branches` | Nested if/else chain |
| `arrayShift ptr ty idx` | `ptr + idx * sizeof(ty)` |
| `memberShift ptr tag member` | `ptr + offsetof(tag, member)` |
| `struct_ tag members` | Construct field variables |
| `memberof tag member e` | Field access |
| `convInt ity e` | Type cast (truncation/extension) |
| `wrapI ity op e1 e2` | Overflow-checking arithmetic |

### Effectful expressions (Expr → Boole statements)

| Cerberus `Expr` | Boole |
|------------------|-------|
| `pure pe` | Translate `pe` as expression |
| `let_ pat e1 e2` | `var tmp := e1'; [bind pat to tmp]; e2'` |
| `sseq pat e1 e2` | Sequential: translate `e1`, bind result, translate `e2` |
| `wseq pat e1 e2` | Same as `sseq` for sequential programs |
| `if_ cond then_ else_` | `if (cond') { then' } else { else' }` |
| `case_ scrut branches` | Nested if/else |
| `memop load [ty, ptr]` | `tmp := heap[ptr']` |
| `memop store [ty, ptr, val]` | `heap[ptr'] := val'` |
| `action (create ...)` | Allocate: find fresh address, set alloc |
| `action (kill ...)` | Free: `assert alloc[p]; alloc[p] := false` |
| `proc name args` | `call name(args')` |
| `ccall fptr fty args` | Resolve function pointer, translate as `call` |
| `run label args` | Goto label (Boole labeled blocks) |
| `nd es` | Nondeterministic choice → `havoc` + assume |

### Pattern binding

Cerberus uses pattern matching extensively. Translation strategy:

```
// Cerberus: let (x, y) = pair_expr in body
// Boole:
var x : int;
var y : int;
x := first(pair_expr');
y := second(pair_expr');
body'
```

For simple `sym` patterns, just bind directly. For constructor patterns
(`Specified v` vs `Unspecified`), generate if/else branches.

---

## 4. Procedure Translation

### Function declarations

```
// Cerberus:
FunDecl.proc loc env retTy params body

// Boole:
procedure name(param1: ty1, ...) returns (ret: retTy')
spec {
  // requires/ensures from CN annotations if available
}
{
  // translated body
}
```

### Global variables

```
// Cerberus:
GlobDecl.def_ coreTy cTy init

// Boole:
var name : ty;
// Initialize in a setup procedure or inline
```

### MuCore continuation handling

Before translation, apply the MuCore transformation (`transformProc`):

1. `collectSaves` extracts all `Esave` nodes into a `LabelDefs` map
2. `removeSave` replaces `Esave` with `Erun`

Then translate:
- `LabelDef.label info` → Boole labeled block
- `Erun label args` → Boole `goto label` or tail call

For simple cases (loop bodies, early returns), continuations map directly to
Boole's structured control flow. For complex continuation patterns, use labeled
blocks:

```
// Boole labeled block:
label_name: {
  // body
} end : {}
```

---

## 5. Specification Translation

### From CN annotations (if available)

CN specs attached to Cerberus functions translate naturally:

| CN | Boole |
|----|-------|
| `requires P` | `requires P'` |
| `ensures P` | `ensures P'` |
| `take v = Owned<T>(p)` | Assert `alloc[p]`; `v := heap[p]` |
| `each(i in [lo..hi]): Owned<T>(p+i)` | `forall i: int :: lo <= i && i < hi ==> alloc[p+i]` |
| CN index terms | Direct translation to Boole expressions |

### Without CN (from the C semantics alone)

Generate basic safety specs:
- No null pointer dereference: `requires ptr != 0`
- No use-after-free: `assert alloc[ptr]` before load/store
- No double-free: `assert alloc[ptr]` before free
- Array bounds: `assert 0 <= idx && idx < len`
- Division by zero: `assert divisor != 0`

---

## 6. What to Skip (Phase 1)

- **Concurrency:** `par`, `unseq`, `wait`, atomics, memory orders
- **Provenance:** Pointer provenance tracking (use flat address model)
- **Floating point:** `FloatingType`, `FloatingValue`
- **Unspecified values:** `LoadedValue` with `Unspecified` — treat as havoc
- **`wseq` nondeterminism:** Treat as `sseq` (valid for sequential programs)
- **`nd` / nondeterministic choice:** Translate as havoc + assume if encountered
- **CHERI / capability hardware extensions**
- **Dynamic annotations / race detection**

---

## 7. Implementation Plan

### Phase 1: Infrastructure

1. **Create module:** `CslibTest/CoreToBoole.lean` (or new package)
2. **Import both ASTs:** Cerberus Core types + Strata/Boole types
3. **Define translation monad:** State for fresh names, type environment,
   struct layouts (from `TagDefs`)

```lean
structure TransState where
  freshCounter : Nat
  structLayouts : HashMap Sym (List (Identifier × Ctype))
  implDefs : ImplDefs  -- for sizeof/alignof
  tempVars : List Boole.Decl  -- accumulated variable declarations

abbrev TransM := StateT TransState (Except String)
```

### Phase 2: Type translation

```lean
def translateCtype : Ctype → TransM Boole.Expression.Ty
def translateBaseType : BaseType → TransM Boole.Expression.Ty
```

### Phase 3: Expression translation

```lean
def translatePexpr : Pexpr → TransM Boole.Expression.Expr
def translateBinop : Binop → TransM (Boole.Expression.Expr → Boole.Expression.Expr → Boole.Expression.Expr)
```

### Phase 4: Statement translation

```lean
def translateExpr : Expr → TransM (List Boole.Statement)
def translateAction : Action → TransM (List Boole.Statement)
```

### Phase 5: Program translation

```lean
def translateFunDecl : Sym → FunDecl → TransM Boole.Decl
def translateFile : File → TransM Boole.Program
```

### Phase 6: Integration

```lean
def verifyCoreProg (file : File) : Except String (Strata.Program) := do
  let boole ← translateFile file |>.run initialState
  -- Convert Boole.Program to Strata.Program for verification
  return coreToGeneric boole.toCoreProg
```

### Toolchain consideration

CerbLean uses Lean v4.26.0, Boole-sandbox uses v4.27.0. These need to be
aligned before the packages can be combined. Either:
- Bump CerbLean to v4.27.0
- Or build the translator as a standalone pass that serializes/deserializes

---

## 8. Example Translation

### Input (C via Cerberus Core)

```c
int max(int x, int y) {
    if (x >= y) return x;
    else return y;
}
```

Cerberus Core IR (simplified):
```
proc max(x: object integer, y: object integer) → object integer =
  sseq (x_val ← load(int, &x))
  sseq (y_val ← load(int, &y))
  if (x_val >= y_val) then
    pure x_val
  else
    pure y_val
```

### Output (Boole)

```
procedure max(x: int, y: int) returns (r: int)
spec {
  ensures (r == x || r == y);
  ensures (r >= x && r >= y);
}
{
  if (x >= y) {
    r := x;
  } else {
    r := y;
  }
};
```

Note: The translation elides the memory operations since parameters are
passed by value and can be represented directly as Boole integers.

---

## 9. Testing Strategy

1. **Unit tests:** Translate individual Pexpr/Expr nodes, check output
2. **Round-trip:** Translate known-correct C programs, verify with Boole pipeline
3. **Comparison:** Run CerbLean interpreter on test inputs, verify Boole specs
   are consistent with concrete execution
4. **Regression:** Use CerbLean's 760+ test suite as source programs

---

## 10. Open Questions

1. **Strata API stability:** The `Boole.Program` / `Core.Program` constructors are
   internal to Strata. Are they stable enough to depend on?

2. **Memory model precision:** Word-level abstraction loses byte-level aliasing.
   Is this acceptable for the target verification properties?

3. **Loop invariant generation:** Boole requires explicit loop invariants. Should
   the translator attempt to infer them, or require CN annotations?

4. **Toolchain alignment:** Best strategy for bridging v4.26.0 ↔ v4.27.0?
