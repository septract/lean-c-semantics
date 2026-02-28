# Core → Boole/Strata Compilation & Correctness Proof

*Created: 2026-02-26*

## Goal

1. Compile Cerberus Core programs into Strata Core (≈ Boole) programs
2. Prove the compilation correct: the compiled program has the same behavior
   as the CerbLean interpreter

This is a standard compiler correctness problem. The compiled Strata Core
program is the "standard encoding" — a second formalization we prove equivalent
to the interpreter.

---

## Why Strata Core (not Boole specifically)

Boole is syntactic sugar over Strata Core. The `#strata program Boole;` macro
just parses Boogie-like text into `Core.Program` constructors. For programmatic
AST construction (which is what a compiler does), we build `Core.Program`
directly. This means:

- We depend on Strata's base IVL, not the Boole frontend
- More stable API (Core is the foundation, Boole is a consumer)
- We still get Strata's verification pipeline (SMT, CBMC) for free
- Boole examples all reduce to Core programs internally

**Target type**: `Strata.Languages.Core.Program`

---

## What Strata Core Gives Us

### Expressions (Lambda dialect, 10 constructors)
```
const(int/bool/bitvec/string/real)  -- literals
op(name, ty?)                       -- named operators (+, -, *, etc.)
fvar(name, ty?)                     -- variable reference
bvar(idx)                           -- de Bruijn bound variable
abs(ty?, body)                      -- lambda abstraction
quant(∀/∃, ty?, trigger, body)      -- quantifiers
app(fn, arg)                        -- function application
ite(cond, then, else)               -- conditional expression
eq(e1, e2)                          -- equality
```

### Statements (Imperative dialect, 7 constructors)
```
cmd(init name ty val?)              -- declare variable
cmd(set name val)                   -- assignment
cmd(havoc name)                     -- nondeterministic assignment
cmd(assert label cond)              -- assertion (UB check)
cmd(assume label cond)              -- assumption (path filter)
cmd(call lhs proc args)             -- procedure call
ite(cond, then_stmts, else_stmts)   -- conditional
loop(guard, measure?, invs, body)   -- while loop with invariants
block(label, stmts)                 -- labeled block
exit(label?)                        -- jump out of block
```

### Procedures
```
procedure name(inputs) returns (outputs)
  spec { modifies [...]; requires [...]; ensures [...] }
  { body_stmts }
```

### Programs
```
program { decls: [var, type, axiom, proc, func, ...] }
```

### Built-in types
`int`, `bool`, `real`, `bvN`, `Map K V`, user-defined types

This is enough to encode everything.

---

## Full Encoding Plan

### 1. Memory State as Global Variables

The interpreter's `MemState` becomes Strata Core global variables:

```
// === Byte-addressable memory ===
var mem_val  : Map int int;     // addr → byte value (0-255, or -1 = uninit)
var mem_prov : Map int int;     // addr → provenance ID (-1 = none)

// === Allocation metadata ===
var alloc_base     : Map int int;    // allocId → base address
var alloc_size     : Map int int;    // allocId → size in bytes
var alloc_alive    : Map int bool;   // allocId → currently alive
var alloc_readonly : Map int int;    // allocId → readonly status
var alloc_taint    : Map int bool;   // allocId → PNVI-ae exposed

// === Counters ===
var next_alloc : int;
var last_addr  : int;

// === Dead allocation tracking (use-after-free) ===
var dead_alloc : Map int bool;       // allocId → was freed

// === Function pointers ===
var funptr : Map int int;            // addr → function ID

// === I/O ===
var stdout_buf : Map int int;        // index → char
var stdout_len : int;
```

This is a faithful representation of `MemState`. Every field maps directly.
The `HashMap Nat X` fields become `Map int X` in Strata Core.

### 2. Values

Core values carry type tags and provenance. In the compiled program, each
Core variable becomes one or more Strata variables depending on its type:

| Core Value | Strata Encoding |
|------------|----------------|
| `integer (val, prov)` | `x_val : int; x_prov : int` |
| `pointer (prov, null ty)` | `x_addr : int; x_prov : int` (addr = 0) |
| `pointer (prov, concrete _ addr)` | `x_addr : int; x_prov : int` |
| `pointer (prov, function sym)` | `x_addr : int; x_prov : int` (addr = funptr entry) |
| `boolean true/false` | `x : bool` |
| `unit` | (no variable needed) |
| `loaded (specified v)` | Same as the inner value |
| `loaded (unspecified ty)` | `havoc x_val` (nondeterministic) |
| `ctype ty` | `x : int` (encoded type ID) |
| `list elemTy elems` | `x : Map int T; x_len : int` |
| `tuple elems` | Flattened: `x_0, x_1, ...` |
| `struct_ tag members` | Flattened: `x_field1, x_field2, ...` |

Provenance is always tracked as a separate `int` variable. This is the key
difference from the lossy encoding in the original plan — we keep provenance
everywhere, exactly matching the interpreter.

### 3. Memory Operations as Procedures

Each memory operation becomes a Strata Core procedure with the full
Cerberus checks encoded as assertions:

```
procedure mem_alloc(size: int, align: int)
  returns (ptr_addr: int, ptr_prov: int)
  spec {
    modifies next_alloc, last_addr, alloc_base, alloc_size,
             alloc_alive, alloc_readonly, alloc_taint;
    ensures ptr_prov == old(next_alloc);
    ensures alloc_alive[ptr_prov];
    ensures alloc_base[ptr_prov] == ptr_addr;
    ensures alloc_size[ptr_prov] == size;
  }
{
  ptr_prov := next_alloc;
  next_alloc := next_alloc + 1;
  // Allocate downward from last_addr (matching Cerberus)
  last_addr := last_addr - size;
  // Align
  last_addr := last_addr - (last_addr mod align);
  ptr_addr := last_addr;
  alloc_base[ptr_prov] := ptr_addr;
  alloc_size[ptr_prov] := size;
  alloc_alive[ptr_prov] := true;
  alloc_readonly[ptr_prov] := 0;  // writable
  alloc_taint[ptr_prov] := false; // unexposed
};

procedure mem_load(addr: int, prov: int, size: int)
  returns (val: int, val_prov: int)
  spec {
    // Provenance validity
    requires prov >= 0;
    requires alloc_alive[prov];
    requires alloc_base[prov] <= addr;
    requires addr + size <= alloc_base[prov] + alloc_size[prov];
  }
{
  // Single-byte load (multi-byte needs encode/decode helpers)
  val := mem_val[addr];
  val_prov := mem_prov[addr];
  // UB on uninitialized read
  assert val >= 0;  // -1 = uninit
};

procedure mem_store(addr: int, prov: int, size: int,
                    val: int, val_prov: int)
  spec {
    requires prov >= 0;
    requires alloc_alive[prov];
    requires alloc_base[prov] <= addr;
    requires addr + size <= alloc_base[prov] + alloc_size[prov];
    requires alloc_readonly[prov] == 0;  // not readonly
    modifies mem_val, mem_prov;
  }
{
  mem_val[addr] := val;
  mem_prov[addr] := val_prov;
};

procedure mem_kill(addr: int, prov: int)
  spec {
    requires prov >= 0;
    requires alloc_alive[prov];
    requires alloc_base[prov] == addr;
    modifies alloc_alive, dead_alloc;
  }
{
  alloc_alive[prov] := false;
  dead_alloc[prov] := true;
};
```

Multi-byte loads/stores use helper functions that iterate over bytes and
encode/decode using little-endian arithmetic — exactly matching
`Concrete.lean`'s `bytesToInt`/`intToBytes`.

### 4. Provenance Operations

```
// Pointer-to-integer cast: strip provenance
procedure ptr_to_int(addr: int, prov: int) returns (val: int)
{
  val := addr;
  // PNVI-ae: expose the allocation
  if (prov >= 0) {
    alloc_taint[prov] := true;
  }
};

// Integer-to-pointer cast: recover provenance from exposed allocations
procedure int_to_ptr(val: int) returns (addr: int, prov: int)
{
  addr := val;
  // Find allocation containing this address that is exposed
  havoc prov;
  assume prov >= 0;
  assume alloc_alive[prov];
  assume alloc_taint[prov];  // must be exposed (PNVI-ae)
  assume alloc_base[prov] <= addr;
  assume addr < alloc_base[prov] + alloc_size[prov];
};

// Array shift (pointer arithmetic)
procedure array_shift(addr: int, prov: int, elem_size: int, idx: int)
  returns (result_addr: int, result_prov: int)
  spec {
    requires prov >= 0;
    requires alloc_alive[prov];
  }
{
  result_addr := addr + idx * elem_size;
  result_prov := prov;
  // Bounds check (one-past-end allowed)
  assert alloc_base[prov] <= result_addr;
  assert result_addr <= alloc_base[prov] + alloc_size[prov];
};
```

### 5. Nondeterminism and Race Detection (Eunseq)

For `Eunseq [e1, e2]`, we encode the VCC/HAVOC way:

```
// Track memory footprints per sub-expression
var fp_base : Map int int;     // footprint idx → base address
var fp_size : Map int int;     // footprint idx → size
var fp_kind : Map int int;     // footprint idx → 0=read, 1=write
var fp_owner : Map int int;    // footprint idx → which sub-expression
var fp_count : int;            // number of footprints

procedure record_footprint(owner: int, base: int, size: int, kind: int) {
  fp_base[fp_count] := base;
  fp_size[fp_count] := size;
  fp_kind[fp_count] := kind;
  fp_owner[fp_count] := owner;
  fp_count := fp_count + 1;
};

// After evaluating all sub-expressions, check for races
procedure check_no_race() {
  var i : int;
  var j : int;
  i := 0;
  while (i < fp_count)
    invariant 0 <= i && i <= fp_count
  {
    j := i + 1;
    while (j < fp_count)
      invariant i < j && j <= fp_count
    {
      if (fp_owner[i] != fp_owner[j]) {
        // Different sub-expressions
        if (fp_kind[i] == 1 || fp_kind[j] == 1) {
          // At least one write
          // Assert no overlap
          assert fp_base[i] + fp_size[i] <= fp_base[j]
              || fp_base[j] + fp_size[j] <= fp_base[i];
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
};
```

For the evaluation order nondeterminism itself:
```
// Eunseq [e1, e2]: evaluate in nondeterministic order
var order : int;
havoc order;
assume order == 0 || order == 1;
if (order == 0) {
  // e1 then e2
  <translate e1, recording footprints with owner=0>
  <translate e2, recording footprints with owner=1>
} else {
  // e2 then e1
  <translate e2, recording footprints with owner=1>
  <translate e1, recording footprints with owner=0>
}
call check_no_race();
```

The exclusion set mechanism from `DynAnnotation` maps naturally: the
`exclusionSet` tracks which sub-expressions are sequenced (via wseq/sseq),
and sequenced pairs skip the race check.

### 6. Expression Translation

#### Pure expressions (Pexpr → Strata Core Expr)

| Core Pexpr | Strata Core |
|------------|-------------|
| `PEsym s` | `fvar(s)` |
| `PEval (Vinteger (IntegerValue v p))` | Two vars: `const(v)`, `const(p)` |
| `PEval (Vtrue)` | `const(true)` |
| `PEval (Vfalse)` | `const(false)` |
| `PEop binop [e1, e2]` | `app(app(op(binop), e1'), e2')` |
| `PEnot e` | `app(op("not"), e')` |
| `PEif c t e` | `ite(c', t', e')` |
| `PElet pat e1 e2` | `init` + bind pattern + translate e2 |
| `PEcase scrut branches` | Nested `ite` chain |
| `PEarray_shift ptr ty idx` | `call array_shift(ptr, sizeof(ty), idx)` |
| `PEmember_shift ptr tag member` | `call member_shift(ptr, offsetof(tag, member))` |
| `PEstruct tag members` | Flatten members into field variables |
| `PEmemberof tag member e` | Select field variable |
| `PEconv_int ity e` | Truncation/extension arithmetic |
| `PEwrap_i ity e1 e2` | Modular arithmetic + overflow check |

#### Effectful expressions (Expr → List Strata Core Statement)

| Core Expr | Strata Core |
|-----------|-------------|
| `Epure pe` | Translate pe as expression |
| `Elet pat e1 e2` | Translate e1; bind pat; translate e2 |
| `Esseq pat e1 e2` | Same as let (strong sequence) |
| `Ewseq pat e1 e2` | Same as let (for sequential programs; nondeterminism handled via unseq) |
| `Eif cond then else` | `ite(cond', then_stmts, else_stmts)` |
| `Ecase scrut branches` | Nested `ite` chain |
| `Eaction (Create ...)` | `call mem_alloc(...)` |
| `Eaction (Kill ...)` | `call mem_kill(...)` |
| `Eaction (Store ...)` | `call mem_store(...)` |
| `Eaction (Load ...)` | `call mem_load(...)` |
| `Ecall proc args` | `call proc(args)` |
| `Eunseq [es]` | Havoc order + evaluate all + check_no_race |
| `Esave label params body` | Pre-collect into labeled blocks |
| `Erun label args` | `exit(label)` (jump to labeled block) |
| `End es` | `havoc result; assume result ∈ possible_values` |

### 7. Procedure and Program Translation

```
// Core FunDecl.proc:
//   proc(loc, env, retTy, params, body)
// → Strata Core Procedure:
procedure f(p1_val: int, p1_prov: int, ...) returns (ret_val: int, ret_prov: int)
spec {
  modifies mem_val, mem_prov, alloc_base, ...;  // all memory state
}
{
  // Allocate parameter objects (Cerberus passes by pointer)
  call (p1_addr, p1_alloc) := mem_alloc(sizeof(p1_ty), alignof(p1_ty));
  call mem_store(p1_addr, p1_alloc, sizeof(p1_ty), p1_val, p1_prov);
  // ... translate body ...
};
```

Global variables become initialization in a setup procedure:
```
procedure __init_globals()
spec { modifies mem_val, mem_prov, ...; }
{
  // For each global: allocate + initialize
  call (g_addr, g_prov) := mem_alloc(sizeof(g_ty), alignof(g_ty));
  call mem_store(g_addr, g_prov, sizeof(g_ty), g_init_val, g_init_prov);
};
```

The full program:
```
Core.File {funs, globs, tagDefs, impl, main}
→
Core.Program {
  decls: [
    // Memory model globals
    var mem_val, mem_prov, alloc_base, ...
    // Memory operation procedures
    proc mem_alloc, mem_load, mem_store, mem_kill, ...
    // Provenance procedures
    proc ptr_to_int, int_to_ptr, array_shift, ...
    // Tag definitions → type size/offset axioms
    axiom sizeof_Point == 8; axiom offsetof_Point_x == 0; ...
    // Global initialization
    proc __init_globals
    // Translated functions
    proc f1, proc f2, ...
    // Main
    proc main
  ]
}
```

### 8. Unspecified Values

When the interpreter loads an uninitialized byte, it gets `LoadedValue.unspecified`.
In Strata Core:

```
// Load might return unspecified
call (val, prov) := mem_load(addr, ptr_prov, size);
// If mem_val[addr] == -1 (uninit marker):
var is_specified : bool;
is_specified := (mem_val[addr] >= 0);
if (!is_specified) {
  havoc val;  // Unspecified: any value
}
```

This matches Cerberus exactly: unspecified values can be "anything" but using
them in certain ways is UB.

### 9. Integer Overflow and Wraparound

Cerberus's `wrapI` (modular arithmetic on fixed-width integers):
```
// wrapI(ity, op, e1, e2)
// Compute in unbounded int, then wrap to [min, max]
var raw : int;
raw := e1_val + e2_val;  // (or -, *, etc.)
// Signed wrap
var width : int;
width := sizeof_ity * 8;
var modulus : int;
modulus := 2^width;
result_val := ((raw + modulus/2) mod modulus) - modulus/2;
```

For signed overflow detection (UB):
```
assert raw >= -(2^(width-1));
assert raw < 2^(width-1);
```

---

## The Compiler Correctness Theorem

### What "correctness" means

For a Core program P, the compiler produces a Strata Core program `compile(P)`.
We need a concrete semantics for Strata Core programs. This is trivial to
define — it's just imperative code:

```lean
-- Strata Core operational semantics (straightforward)
def StrataExec : Core.Program → StrataState → Option (Value × StrataState)
```

Assignments update variables, ifs branch, loops iterate, procedure calls
push/pop frames, asserts fail if false, assumes filter paths, havoc picks
arbitrary values.

### The theorem

```lean
-- State encoding: CerbLean state ↔ Strata state
def encodeState : InterpState → StrataState
def decodeState : StrataState → InterpState
def encodeValue : Value → List (String × StrataVal)
def decodeValue : List (String × StrataVal) → Value

-- Soundness: if interpreter succeeds, compiled program succeeds
theorem compile_sound (f : Core.File) :
  ∀ result,
    runMain f = .ok result →
    ∃ ss, StrataExec (compile f) (initialStrataState f) = .ok (encodeResult result, ss)
      ∧ decodeState ss ≈ result.finalState

-- Completeness: if interpreter detects UB, compiled program hits assert
theorem compile_ub_detected (f : Core.File) :
  ∀ ub,
    runMain f = .error (.undefinedBehavior ub) →
    StrataExec (compile f) (initialStrataState f) = .assertFailed

-- Equivalence for nondeterminism: same set of possible outcomes
theorem compile_nd_equiv (f : Core.File) :
  ∀ results,
    allOutcomes f = results →
    strataAllOutcomes (compile f) = encodeResults results
```

### Proof structure

The proof goes by induction on the evaluation of the Core program. For each
Core expression form, we show the compiled Strata statements produce the same
state update:

```lean
-- Per-expression lemma (example for Elet)
theorem compile_let_correct :
  ∀ pat e1 e2 s,
    -- If e1 compiles correctly in state s
    compile_expr_correct e1 s →
    -- And e2 compiles correctly in the updated state
    compile_expr_correct e2 (bindPattern pat v1 s) →
    -- Then (let pat = e1 in e2) compiles correctly
    compile_expr_correct (Expr.let_ pat e1 e2) s
```

For memory operations, we prove each compiled procedure (mem_load, mem_store,
etc.) matches the corresponding function in `Concrete.lean`.

---

## Strata Core vs. Boole: Which to Target

**Answer: Target Strata Core constructors directly.**

| | Strata Core | Boole |
|--|-------------|-------|
| AST construction | Direct Lean constructors | Same (Boole = Core) |
| Verification | Core.verify → SMT | Same pipeline |
| Syntax sugar | None (programmatic) | `#strata` macro (text) |
| Stability | Foundation layer | Depends on Core |
| Dependencies | Strata only | Strata + CSLib + lean-smt |

Boole adds nothing for programmatic AST construction. It's useful for humans
writing programs by hand. Since we're generating programs from a compiler, we
go straight to Core.

We can still use `#strata program Boole;` syntax for examples and tests.

---

## Strata Dialect vs. Direct Translation

**Answer: Direct translation first, dialect later if needed.**

A Strata dialect (like C_Simp) gives you:
- DDM grammar for text parsing
- Integration with `strata verify` CLI
- CBMC backend for free

But it requires:
- Learning the DDM metaprogramming system
- Defining a grammar for Core's JSON format (awkward fit)
- Boilerplate for dialect registration

Since we're translating from Lean ASTs (not parsing text), the DDM grammar
buys us nothing. We just write a function `compile : Core.File → Strata.Core.Program`.

If we later want CLI integration or the CBMC backend, we can wrap the
compiler as a dialect then.

---

## Implementation Plan

### Phase 1: Memory Model Library (Strata Core procedures)

Write the "runtime library" of Strata Core procedures that model the
CerbLean memory model:

```
mem_alloc, mem_load, mem_store, mem_kill
ptr_to_int, int_to_ptr, array_shift, member_shift
check_no_race, record_footprint
encode_int, decode_int  (multi-byte helpers)
```

These are Strata Core `Procedure` values built programmatically in Lean.
They form a fixed preamble prepended to every compiled program.

**Deliverable**: `CoreToStrata/MemoryModel.lean`

### Phase 2: Expression Compiler

```lean
def compilePexpr : Pexpr → TransM Core.Expression.Expr
def compileExpr  : Expr → TransM (List Core.Statement)
```

Handle pure expressions first (arithmetic, comparison, pattern matching),
then effectful expressions (let, seq, if, call), then memory operations
(load, store, create, kill).

**Deliverable**: `CoreToStrata/Compile.lean`

### Phase 3: Program Compiler

```lean
def compileFunDecl : Sym → FunDecl → TransM Core.Decl
def compileFile    : Core.File → Except String Core.Program
```

Handle function declarations, global variables, tag definitions (struct
layouts), and the main entry point.

**Deliverable**: `CoreToStrata/Program.lean`

### Phase 4: Testing

- Round-trip: compile Core program, run Strata verification, check consistency
- Differential: for concrete programs, compare interpreter result with
  compiled program's execution
- Use the existing 760+ test suite as input programs

### Phase 5: Correctness Proof

- Define `StrataExec` operational semantics for Strata Core
- Prove `encodeState`/`decodeState` roundtrip
- Prove each memory operation procedure matches `Concrete.lean`
- Prove each expression compilation step preserves semantics
- Prove the full `compile_sound` theorem by induction

---

## Toolchain

CerbLean currently uses Lean v4.26.0. Strata uses v4.28.0.

**Options**:
1. **Bump CerbLean to v4.28.0** — cleanest, may require fixing breakage
2. **Pin Strata to an older commit compatible with v4.26.0** — fragile
3. **Standalone package**: new Lake package that depends on both CerbLean and
   Strata, forcing both to align — this is probably the right structure anyway

Option 3 is recommended. The compiler is a separate concern from the
interpreter; it should live in its own package (e.g., `CerbStrata/`) that
imports both `CerbLean` and `Strata`.

---

## Open Questions

1. **Multi-byte encoding**: The interpreter stores values as sequences of
   `AbsByte`. Do we model individual bytes in Strata, or abstract to
   word-level operations with axiomatized encode/decode? Word-level is simpler
   but loses byte-aliasing; byte-level is faithful but verbose.

   Recommendation: byte-level for the correctness proof (faithful), with
   word-level shortcuts available for verification use cases where byte
   aliasing doesn't matter.

2. **Struct layout**: Do we hardcode struct layouts from `TagDefs`, or
   axiomatize sizeof/offsetof? Hardcoding is simpler for per-program
   compilation; axiomatizing is more general.

   Recommendation: hardcode from `TagDefs` (we're compiling specific programs).

3. **Save/run (labeled continuations)**: These map to Strata Core's labeled
   blocks + exit. Need to verify the encoding handles mutual recursion
   between labels correctly.

4. **Extern functions (libc)**: The interpreter maps names like `printf`,
   `malloc` to built-in implementations. The compiled program needs
   corresponding Strata Core procedure stubs with specs.

5. **Fuel/termination**: The interpreter uses fuel for pure expression
   evaluation. The compiled Strata program doesn't need fuel (it's straight-
   line code with loops), but we need to handle the case where the
   interpreter runs out of fuel (compilation should detect unbounded
   recursion).
