# Reasoning About C Programs in Lean

This document explores approaches for formal reasoning about C programs once we have a working interpreter that matches Cerberus semantics.

## The Challenge

We have (or will have) an operational semantics for C in Lean that faithfully models Cerberus's Core IR execution. This gives us:
- Precise semantics matching a well-studied C formalization
- The ability to execute C programs in Lean
- A foundation for detecting undefined behavior

But operational semantics alone doesn't make reasoning easy. Proving properties about programs by unfolding step-by-step execution is tedious and doesn't scale. We need higher-level reasoning principles.

## Approach 1: Hoare Logic / Separation Logic

### Overview
Define a program logic on top of the operational semantics, with rules like:
```
{P} c {Q}
```
meaning "if precondition P holds before executing c, and c terminates without UB, then postcondition Q holds after."

### Separation Logic Variant
Separation logic is particularly well-suited to C because it handles pointer aliasing naturally:
```
{P * Q} c {R * Q}   -- frame rule: Q is preserved if c doesn't touch it
{x ↦ v} *x = w {x ↦ w}   -- points-to assertion
```

### Implementation Strategy

1. **Define assertion language**: Predicates over program states
   ```lean
   def Assertion := State → Prop

   -- Points-to assertion
   def pointsTo (addr : Pointer) (v : Value) : Assertion :=
     fun s => s.memory.load addr = some v

   -- Separating conjunction
   def sepConj (P Q : Assertion) : Assertion :=
     fun s => ∃ s1 s2, s = s1 ⊕ s2 ∧ P s1 ∧ Q s2
   ```

2. **Define Hoare triples**: Either deeply or shallowly embedded
   ```lean
   -- Shallow embedding (predicates are Lean Props)
   def hoare (P : Assertion) (c : Expr) (Q : Assertion) : Prop :=
     ∀ s, P s →
       match eval c s with
       | .ok (v, s') => Q s'
       | .ub _ => False  -- No UB allowed
   ```

3. **Prove reasoning rules sound** with respect to operational semantics:
   ```lean
   theorem seq_rule :
     hoare P c1 R → hoare R c2 Q → hoare P (seq c1 c2) Q

   theorem frame_rule :
     hoare P c Q → modifies c ∩ footprint R = ∅ →
     hoare (P * R) c (Q * R)
   ```

### Pros
- Well-understood theory (Separation Logic, Iris, VST)
- Compositional: reason about parts independently
- Can handle real C patterns (linked lists, trees, etc.)
- Existing tools and techniques to draw from

### Cons
- Significant effort to define and prove rules sound
- Loop invariants still required (no silver bullet)
- Separation logic can be complex for beginners
- May need to handle C-specific complications (integer overflow, alignment, etc.)

### Prior Art
- **VST** (Verified Software Toolchain): Separation logic for CompCert C in Coq
- **Iris**: Higher-order concurrent separation logic framework
- **CN**: Cerberus's own specification language (separation logic-based)

---

## Approach 1b: Using iris-lean

### Overview
[iris-lean](https://github.com/leanprover-community/iris-lean) is a Lean 4 port of Iris, the higher-order concurrent separation logic framework. It provides:

- **MoSeL**: The proof interface/tactic framework from Iris
- **uPred**: The foundational Iris logic
- A curated selection of Iris resources and algebraic structures

### Current Status (as of late 2024)

The project is actively maintained (latest release v4.26.0, December 2025) and tracks recent Lean versions. However, it has significant gaps:

1. **Never instantiated**: The separation logic axiomatization exists, but there's no concrete instantiation demonstrating it works for a real logic.

2. **No program logics**: There are no program logics built on top - you can't actually verify programs yet.

3. **Missing adequacy theorem**: No proof that the logic is sound with respect to an operational semantics.

4. **Incomplete CMRA/OFE theory**: The algebraic foundations (ordered families of equivalences, resource algebras) are partially ported.

### What We Would Need to Do

To use iris-lean for C verification, we would need to:

1. **Instantiate the logic** for our memory model:
   ```lean
   -- Define our resource algebra for C memory
   instance : CMRA CMemory where
     ...

   -- Prove the instantiation is valid
   theorem c_memory_adequate : ...
   ```

2. **Build a program logic** for Core IR:
   ```lean
   -- Weakest precondition for Core expressions
   def wp (e : Expr) (Φ : Value → iProp) : iProp := ...

   -- Prove standard rules
   theorem wp_seq : wp e1 (fun _ => wp e2 Φ) ⊢ wp (seq e1 e2) Φ
   ```

3. **Define C-specific resources**:
   ```lean
   -- Points-to assertion for C pointers
   def pointsTo (p : Pointer) (v : Value) : iProp := ...

   -- Ownership of allocated block
   def blockOwned (p : Pointer) (size : Nat) : iProp := ...
   ```

### Eileen Project

There's also the [Eileen project](https://www.markusde.ca/pages/eileen.html), a more ambitious effort to fully reimplement Iris in Lean from scratch (rather than porting). It aims to:
- Build proper OFE/CMRA hierarchies
- Develop concrete instantiations (Excl, Auth, etc.)
- Prove soundness theorems

However, Eileen is still in early planning/research stages.

### Pros of Using iris-lean
- Leverage existing MoSeL tactics (significant work already done)
- Higher-order logic handles callbacks, closures naturally
- Concurrent separation logic if we later support threads
- Active community (leanprover-community)
- Would benefit from future improvements to iris-lean

### Cons of Using iris-lean
- Significant work to instantiate for our use case
- No existing program logic to build on
- May be fighting the library's design choices
- Prototype status means potential breaking changes
- Complex framework - steep learning curve

### Assessment

iris-lean is a promising foundation but requires substantial investment to use for C verification. The key missing piece is a program logic - the MoSeL tactics exist but there's nothing to apply them to yet.

**Recommendation**: Monitor iris-lean's progress. If someone adds a basic program logic instantiation, it becomes much more attractive. For now, we might:
- Start with a simpler custom separation logic
- Design it to be compatible with iris-lean's interfaces
- Migrate to iris-lean when it matures

Alternatively, contributing to iris-lean by building the first program logic instantiation would benefit both projects.

---

## Approach 2: Weakest Precondition Calculus

### Overview
Instead of forward-reasoning Hoare logic, define a weakest precondition transformer:
```
wp(c, Q) = weakest P such that {P} c {Q}
```

### Implementation
```lean
def wp : Expr → Assertion → Assertion
| skip, Q => Q
| assign x e, Q => fun s => Q (s.update x (eval e s))
| seq c1 c2, Q => wp c1 (wp c2 Q)
| if b c1 c2, Q => fun s =>
    if eval b s then wp c1 Q s else wp c2 Q s
| while b c, Q => -- requires loop invariant annotation
```

### Pros
- More algorithmic than Hoare logic
- Can generate verification conditions automatically
- Natural fit for symbolic execution

### Cons
- Loops still need invariants
- WP for memory operations gets complicated
- Less compositional than separation logic for pointer programs

---

## Approach 3: Denotational Semantics + Equivalence Proof

### Overview
Define a cleaner, more abstract semantics and prove it equivalent to the operational semantics.

### Possible Denotational Models

#### 3a. Monadic Semantics
```lean
-- State + Error + UB monad
abbrev M := StateT State (ExceptT Error (ExceptT UB Id))

def eval : Expr → M Value
| var x => do let s ← get; return s.lookup x
| binop op e1 e2 => do
    let v1 ← eval e1
    let v2 ← eval e2
    applyOp op v1 v2  -- may throw UB
| load e => do
    let ptr ← eval e
    memLoad ptr  -- may throw UB
```

#### 3b. Game Semantics
Model programs as strategies in a game between program and environment. Useful for:
- Handling nondeterminism (unspecified behavior)
- Reasoning about program equivalence
- Compositional semantics

#### 3c. Domain-Theoretic Semantics
For handling recursion and non-termination properly:
```lean
-- Lift domain with bottom for non-termination
inductive Lift (α : Type) where
  | bot : Lift α
  | up : α → Lift α
```

### Equivalence Theorem
```lean
theorem operational_denotational_equiv :
  ∀ e s, eval_operational e s = eval_denotational e s
```

### Pros
- Cleaner reasoning (no step-counting)
- Can use equational reasoning
- May reveal program equivalences more naturally

### Cons
- Extra layer of definitions to maintain
- Equivalence proof can be substantial
- May lose some operational intuition

---

## Approach 4: Refinement Types / Liquid Types

### Overview
Extend the type system to track properties of values:
```lean
-- Refined integer type
def Int32 (p : Int → Prop) := { x : Int32 // p x }

-- Non-null pointer
def NonNullPtr := { p : Pointer // p ≠ null }

-- Array with bounds
def BoundedArray (n : Nat) := { arr : Array // arr.size = n }
```

### Implementation
```lean
-- Function that requires non-null input
def deref (p : NonNullPtr) : M Value := ...

-- Bounds-checked array access
def arrayGet (arr : BoundedArray n) (i : Fin n) : Value := ...
```

### Pros
- Type-driven: properties checked at definition time
- Integrates with Lean's type system naturally
- Can catch many bugs at "compile time"

### Cons
- Limited to properties expressible in types
- Complex invariants still need manual proofs
- Subtyping/coercion overhead

---

## Approach 5: Symbolic Execution

### Overview
Execute programs symbolically, building up path conditions:
```lean
structure SymState where
  pathCond : List Prop      -- constraints on symbolic values
  memory : SymbolicMemory   -- symbolic memory state

def symEval : Expr → SymState → List (Value × SymState)
```

### Pros
- Automatic exploration of paths
- Can find bugs without specifications
- Useful for test generation

### Cons
- Path explosion for loops
- Needs SMT solver integration
- Not a complete verification method

---

## Approach 6: Certified Translation to Simpler IR

### Overview
Translate C programs to a simpler intermediate representation where reasoning is easier, and prove the translation correct.

### Possible Targets

#### 6a. Functional Programs
Transform imperative C to functional Lean:
```lean
-- C loop becomes Lean recursion
def sumArray_c : Array Int → Int := -- original C
def sumArray_lean (arr : Array Int) : Int :=
  arr.foldl (· + ·) 0

theorem translation_correct :
  ∀ arr, eval sumArray_c arr = sumArray_lean arr
```

#### 6b. Guarded Command Language
Dijkstra's GCL with explicit nondeterminism:
```
if x > 0 → y := 1
[] x ≤ 0 → y := 0
fi
```

### Pros
- Reason in a cleaner language
- Translation proof done once
- Can use existing Lean reasoning

### Cons
- Not all C programs translate nicely
- Translation correctness proof is work
- May lose connection to original C

---

## Approach 7: Rely-Guarantee for Concurrency

### Overview
If we eventually support concurrent C, use rely-guarantee reasoning:
```
R, G ⊢ {P} c {Q}
```
- R: what the environment may do
- G: what this thread guarantees
- Threads compose if each thread's guarantee implies others' rely

### Pros
- Compositional concurrent reasoning
- Well-studied theory

### Cons
- Only needed for concurrent code
- Complex methodology

---

## Approach 8: Predicate Transformers + Dijkstra Monads

### Overview
Use Dijkstra monads to give specifications as part of the type:
```lean
-- Dijkstra monad: computations with pre/post specs
def Dijkstra (pre : State → Prop) (post : State → Value → State → Prop) :=
  (s : State) → pre s → { p : Value × State // post s p.1 p.2 }
```

### Pros
- Specifications in types
- Compositional via monad operations
- Used successfully in F*/Low*

### Cons
- Complex types
- Learning curve
- May not fit Lean idioms perfectly

---

## Approach 9: CN Integration / Translation

### Overview

[CN](https://github.com/rems-project/cn) is Cerberus's own separation-logic refinement type system for C. Since we're already building on Cerberus, there's a natural question: can we leverage CN specifications or translate them to Lean?

### What CN Provides

CN is a mature verification system that:
- Uses Cerberus's Core IR (same as us!)
- Has separation-logic ownership types
- Supports refinement types with SMT-decidable constraints
- Has been used to verify real systems (e.g., Google's pKVM hypervisor)
- Provides both static verification and runtime testing (Fulminate, POPL 2025)

### CN Specification Syntax

CN annotations live in special comments:
```c
int add(int x, int y)
/*@ requires let sum = (i64) x + (i64) y;
             -2147483648i64 <= sum; sum <= 2147483647i64
    ensures return == (i32) sum
@*/
{ return x+y; }

void write(int *p, int v)
/*@ requires take old = Owned<int>(p)
    ensures take new = Owned<int>(p);
            new == v
@*/
{ *p = v; }
```

Key constructs:
- `requires`/`ensures`: Pre/postconditions
- `take v = Owned<T>(p)`: Ownership assertion (like points-to)
- `Block<T>(p)`: Uninitialized memory
- `each(i; range) { Resource }`: Iterated separating conjunction
- `let x = expr`: Logical variable binding

### Integration Options

#### Option A: Parse CN specs, translate to Lean propositions

```
C + CN annotations → Cerberus → Core IR + CN specs (JSON?)
                                        ↓
                              Lean parser extracts specs
                                        ↓
                              Lean theorems to prove
```

**Pros:**
- Users write specs once (in CN syntax they may already know)
- CN specs are well-tested on real code
- Shared tooling with Cerberus ecosystem

**Cons:**
- Need to parse CN's spec language
- CN's spec language may not map cleanly to Lean
- Dependent on CN's internal representation

#### Option B: Lean-native specs inspired by CN

Define a Lean DSL that mirrors CN's style:
```lean
-- CN-inspired ownership predicates
def Owned (T : CType) (p : Pointer) (v : T.denote) : Assertion := ...
def Block (T : CType) (p : Pointer) : Assertion := ...

-- CN-style function spec
structure FnSpec where
  requires : Assertion
  ensures : Value → Assertion

-- Example
def add_spec : FnSpec := {
  requires := fun s =>
    let sum := s.args[0]!.toInt64 + s.args[1]!.toInt64
    -2147483648 ≤ sum ∧ sum ≤ 2147483647
  ensures := fun ret s =>
    ret = s.args[0]! + s.args[1]!
}
```

**Pros:**
- Full Lean expressiveness
- No parsing overhead
- Can use dependent types, tactics, etc.

**Cons:**
- Users learn new syntax
- No direct compatibility with CN tools

#### Option C: Prove CN sound w.r.t. our semantics

The most ambitious: formalize CN's type system in Lean and prove it sound against our operational semantics.

```lean
-- CN typing judgment
inductive CNTyped : Expr → CNType → Prop where
  ...

-- Soundness theorem
theorem cn_soundness :
  CNTyped e τ →
  ∀ s, τ.precondition s →
    (eval e s).isOk ∧ τ.postcondition (eval e s).get
```

**Pros:**
- Gold standard: proves CN itself is correct
- Any CN-verified code is transitively verified in Lean
- Major research contribution

**Cons:**
- Enormous undertaking
- CN's type system is complex (resource inference, etc.)
- Would need to track CN's evolution

### Recommendation

**Short term**: Option B (Lean-native specs inspired by CN)
- Design our assertion language to look like CN where sensible
- Makes future integration easier
- Users familiar with CN will recognize patterns

**Medium term**: Option A (parse CN specs)
- If CN adds JSON export of specs, parse them
- Automatic translation for existing CN-verified code

**Long term**: Option C (soundness proof)
- Only if there's research interest/funding
- Would be a significant publication

### CN Resources
- [CN GitHub](https://github.com/rems-project/cn)
- [CN Tutorial](https://rems-project.github.io/cn-tutorial/)
- [POPL 2023 Paper](https://www.cl.cam.ac.uk/~cp526/popl23.html)
- [Iris Workshop 2024 Slides](https://iris-project.org/workshop-2024/slides/pulte.pdf)

### Where Do CN Types Live?

**Key finding**: CN specs are attached at the **AIL level** (Cerberus's intermediate language), NOT in Core IR.

The Cerberus pipeline:
```
C source → Cabs → AIL (CN specs attached here) → Core IR (CN stripped) → JSON
                    ↓                               ↓
              (typing only)                   (executable semantics)
```

**Important**: AIL has no interpreter - it's only for typing/elaboration. The executable semantics are defined **only at the Core level**:
- `core_eval.lem` - Big-step semantics for pure expressions
- `core_run.lem` - Small-step semantics for effectful expressions
- `driver.lem` - Drives Core execution with memory model

This means CN type-checks against AIL structure but the *meaning* of programs (including UB) is defined by Core execution. So our approach of defining a refinement type system over Core IR and proving it sound w.r.t. the Core interpreter is the right architecture - it matches how Cerberus itself works.

AIL's sigma structure includes CN fields:
```ocaml
(* cerberus/frontend/model/ail/ailSyntax.lem *)
type sigma 'a = <|
  ...
  cn_functions: list sigma_cn_function;
  cn_predicates: list sigma_cn_predicate;
  cn_datatypes: list sigma_cn_datatype;
  cn_decl_specs: list sigma_cn_decl_spec;  (* function specs *)
  ...
|>
```

But Core's `generic_file` has **no CN fields** - they're deliberately excluded.

### Option: Add CN Specs to JSON Export

We could potentially modify Cerberus to export CN specs alongside Core IR:

**What would be needed:**
1. Modify `cerberus/ocaml_frontend/pprinters/json_core.ml` to include CN specs
2. Either:
   - Add CN fields to Core's `generic_file` type, or
   - Export a separate JSON file with CN specs indexed by symbol
3. Extend our Lean parser to handle CN spec types
4. Coordinate with Cerberus team (they might be interested!)

**Example extended JSON structure:**
```json
{
  "funs": { ... },  // existing Core functions
  "cn_specs": {     // NEW: CN specifications
    "add": {
      "requires": ["let sum = (i64) x + (i64) y", "sum <= INT_MAX"],
      "ensures": ["return == (i32) sum"]
    },
    "write": {
      "requires": [{"take": "old", "resource": "Owned<int>(p)"}],
      "ensures": [{"take": "new", "resource": "Owned<int>(p)"}, "new == v"]
    }
  }
}
```

**Pros:**
- Users write specs in CN (familiar, tested)
- Single source of truth
- Could verify CN-annotated code directly

**Cons:**
- Requires Cerberus modification
- CN spec language is complex
- Ties us to CN's design decisions

**Assessment**: Worth proposing to the Cerberus team. Even a minimal export of function pre/postconditions would be valuable.

---

## Approach 10: Refinement Types over Core IR (CN-style in Lean)

### Overview

CN's fundamental insight is that you can build a refinement type system directly over Cerberus's Core IR. Since we're already parsing Core IR into Lean, we could define a similar refinement type system natively in Lean. This is arguably the most natural approach given our architecture.

### Why This Fits Well

1. **We already have Core AST types in Lean** - the substrate is there
2. **Refinement types are natural in Lean** - dependent types subsume refinement types
3. **Bidirectional type checking is well-understood** - clean implementation path
4. **CN provides a proven design** - we can learn from their choices

### CN's Type System Architecture

CN uses four typing contexts:
- **C**: Computational variables → base types (runtime values)
- **L**: Logical variables → base types (ghost/specification values)
- **R**: Available resources (ownership, like separation logic heap)
- **Φ**: Constraints (refinement predicates, sent to SMT)

A CN type judgment looks like:
```
C; L; R; Φ ⊢ e : τ ⊣ C'; L'; R'; Φ'
```
The contexts can change (bidirectional flow) as we typecheck.

### Lean Implementation Sketch

```lean
-- Typing contexts
structure Contexts where
  comp : List (Symbol × BaseType)      -- computational vars
  logic : List (Symbol × BaseType)     -- logical/ghost vars
  resources : ResourceSet              -- available ownership
  constraints : List Prop              -- refinement constraints

-- Refined types
inductive RType where
  | base (b : BaseType) (φ : Value → Prop)           -- {v : b | φ(v)}
  | owned (T : CType) (p : Pointer)                  -- Owned<T>(p)
  | block (T : CType) (p : Pointer)                  -- Block<T>(p)
  | fn (pre : Contexts → Prop) (post : Value → Contexts → Prop)

-- Bidirectional typing judgment
inductive HasType : Contexts → Expr → RType → Contexts → Prop where
  | var :
      (x, τ) ∈ Γ.comp →
      HasType Γ (Expr.var x) (RType.base τ (· = Γ.lookup x)) Γ

  | load :
      HasType Γ e (RType.base ptrType ptrPred) Γ' →
      RType.owned T p ∈ Γ'.resources →
      HasType Γ (Expr.load e) (RType.base T.toBase (· = mem[p]))
               (Γ'.consumeResource (RType.owned T p))

  | store :
      HasType Γ e_ptr ptrType Γ₁ →
      HasType Γ₁ e_val valType Γ₂ →
      RType.owned T p ∈ Γ₂.resources →
      HasType Γ (Expr.store e_ptr e_val) RType.unit
               (Γ₂.updateResource p v)
  -- ... etc
```

### Key Design Decisions

#### 1. Resources as Linear Types
CN treats ownership as a linear resource that must be consumed exactly once:
```lean
-- Resource consumption
def Contexts.consumeResource (Γ : Contexts) (r : Resource) : Contexts :=
  { Γ with resources := Γ.resources.erase r }

-- Linearity check: all resources consumed by function end
def checkLinear (Γ_start Γ_end : Contexts) : Prop :=
  Γ_end.resources ⊆ Γ_start.resources  -- only allowed to consume, not create
```

#### 2. Constraints Go to SMT (or Lean tactics)
CN sends refinement constraints to Z3. In Lean, we have options:
- **Decide at definition time**: use `decide` for decidable props
- **Leave as proof obligations**: user provides proofs
- **External SMT**: call Z3/CVC5 via FFI (like SMTLib tactics)
- **Lean's `omega`/`simp`**: for arithmetic constraints

```lean
-- Example: checking array bounds
def arrayAccess_safe (arr : Pointer) (i : Int) (len : Nat) : Prop :=
  0 ≤ i ∧ i < len

-- Could be decided by omega tactic
example : arrayAccess_safe arr 5 10 := by omega
```

#### 3. Ghost Variables for Specification
CN's logical variables (L context) are ghost - they don't exist at runtime:
```lean
-- Ghost/logical variables are erased
@[reducible] def Ghost (α : Type) := α

-- In specs, we can refer to "old" values
def swap_spec : FnSpec := {
  pre := fun Γ =>
    ∃ (v1 v2 : Ghost Int),
      Γ.resources.contains (Owned Int p1 v1) ∧
      Γ.resources.contains (Owned Int p2 v2)
  post := fun Γ Γ' =>
    Γ'.resources.contains (Owned Int p1 Γ.ghost.v2) ∧
    Γ'.resources.contains (Owned Int p2 Γ.ghost.v1)
}
```

### Soundness Theorem: The Key Payoff

**This is the crucial point**: we prove that the refinement type system is *sound* with respect to the interpreter. This is analogous to Hoare logic soundness - the syntactic typing judgment implies semantic truth of the specified properties.

The type system lets users specify *arbitrary properties* via refinement predicates. Soundness says: if typing succeeds, those properties actually hold when the program executes.

```lean
/-
  SOUNDNESS THEOREM (Semantic Validity of Refinement Types)

  The refinement type system is a way of *specifying* program behavior.
  Soundness proves these specifications are *true* of the actual execution.

  This is analogous to Hoare logic soundness:
    - Hoare: if ⊢ {P} c {Q} is derivable, then ⊨ {P} c {Q} is true
    - Here:  if Γ ⊢ e : τ is derivable, then e satisfies τ semantically
-/

-- A type τ is "semantically satisfied" by execution when:
--   1. The preconditions in τ imply the program doesn't UB
--   2. If the program terminates, the result satisfies τ's postconditions
--   3. Any properties asserted by τ (via refinements) actually hold

def SemanticallyValid (Γ : Contexts) (e : Expr) (τ : RType) (Γ' : Contexts) : Prop :=
  ∀ mem,
    Γ.constraintsSatisfied →           -- preconditions hold
    Γ.resourcesValidIn mem →           -- we own what we claim
    match eval e (Γ.toState mem) with
    | .ub _ => False                   -- no undefined behavior
    | .ok (v, mem', s') =>
        τ.refinement v ∧               -- result satisfies the refinement predicate!
        Γ'.resourcesValidIn mem' ∧     -- output ownership is valid
        Γ'.constraintsSatisfied        -- output constraints hold

-- THE MAIN THEOREM: typing implies semantic validity
theorem soundness :
  HasType Γ e τ Γ' →                   -- syntactic: e has type τ
  SemanticallyValid Γ e τ Γ'           -- semantic: τ's properties hold of e
```

### What This Really Says

The key insight is that **refinement predicates become true propositions**:

```lean
-- User specifies: "this function returns a sorted array"
def sort_type : RType :=
  RType.fn
    (args := [("arr", ArrayPtr), ("len", Nat)])
    (pre := fun Γ =>
      -- precondition: we own the array
      Γ.hasResource (OwnedArray Γ.arr Γ.len))
    (post := fun ret Γ Γ' =>
      -- postcondition: array is now sorted
      Γ'.hasResource (OwnedArray Γ.arr Γ.len) ∧
      IsSorted (readArray Γ'.mem Γ.arr Γ.len))  -- ← arbitrary property!

-- Soundness gives us:
theorem sort_correct :
  HasType Γ sort_impl sort_type Γ' →   -- sort_impl type-checks
  ∀ mem, Γ.valid mem →
    let (_, mem') := eval sort_impl (Γ.toState mem)
    IsSorted (readArray mem' Γ.arr Γ.len)   -- the array really is sorted!
```

This is the power: **any property you can express in the refinement becomes a theorem about the program's behavior**.

### Comparison to Hoare Logic Soundness

The structure is exactly parallel to Hoare logic:

| Hoare Logic | Refinement Types |
|-------------|------------------|
| `{P} c {Q}` | `Γ ⊢ e : {v:τ \| φ(v)}` |
| Derivable in proof system | Derivable via typing rules |
| Soundness: derivable ⟹ valid | Soundness: well-typed ⟹ φ holds |
| `⊨ {P} c {Q}`: if P holds and c terminates, Q holds | If preconditions hold and e terminates, φ(result) holds |

The difference is that refinement types integrate specifications *into* types, making them compositional by construction.

### The Full Picture: Safety + Correctness

Soundness gives us both:

1. **Safety (no UB)**: If preconditions hold, execution doesn't hit UB
2. **Functional correctness**: If execution terminates, the refinement predicate holds

```lean
-- For a function f with type:
--   (x : Int) → {y : Int | y = x * 2}
-- Soundness says:
--   1. Calling f won't cause UB (if Int is in range)
--   2. f returns exactly x * 2

-- For a function with type:
--   (p : Ptr) → requires Owned<Int>(p, v) → ensures Owned<Int>(p, v + 1)
-- Soundness says:
--   1. If we own *p with value v, the call won't UB
--   2. Afterward, *p contains v + 1
```

### Proving Soundness

The proof proceeds by induction on the typing derivation. For each typing rule, we show the corresponding semantic property holds:

```lean
-- For each typing rule, prove the semantic interpretation holds
theorem typing_rule_sound :
  -- E.g., for the load rule:
  HasType Γ e (RType.base PtrType ptrPred) Γ₁ →
  (Owned T p) ∈ Γ₁.resources →
  HasType Γ (Expr.load e) (RType.base T.toBase (· = valueAt p)) Γ₂ →
  -- Semantically: if we own p, loading from it gives the value there
  SemanticallyValid Γ (Expr.load e) (RType.base T.toBase (· = valueAt p)) Γ₂

-- The main theorem follows by induction
theorem soundness : HasType Γ e τ Γ' → SemanticallyValid Γ e τ Γ'
  := by induction ... <;> apply typing_rule_sound
```

### Why This is Better Than Just Progress/Preservation

Standard type soundness (progress + preservation) only says "well-typed programs don't get stuck." We get much more:

| Standard Type Soundness | Refinement Type Soundness |
|------------------------|---------------------------|
| No runtime type errors | No runtime type errors |
| Programs don't get stuck | Programs don't UB |
| — | **User-specified properties hold** |
| — | **Functional correctness provable** |

The refinement predicates let us state and prove **arbitrary correctness properties**, not just safety.

### The Trust Chain

```
┌────────────────────────────────────────────────────────────────────────┐
│                         WHAT WE PROVE                                  │
├────────────────────────────────────────────────────────────────────────┤
│                                                                        │
│  1. Define refinement type system over Core IR (in Lean)               │
│                           ↓                                            │
│  2. Prove SOUNDNESS: typing ⟹ semantic validity                       │
│     (machine-checked in Lean, proved once)                             │
│                           ↓                                            │
│  3. User writes spec: "sort returns sorted array"                      │
│     Type checker verifies: sort_impl : SortSpec                        │
│                           ↓                                            │
│  4. By soundness: eval sort_impl produces sorted array                 │
│                           ↓                                            │
│  5. Since interpreter matches Cerberus (differential testing)...       │
│                           ↓                                            │
│  6. CONCLUSION: real C execution satisfies the spec                    │
│                                                                        │
└────────────────────────────────────────────────────────────────────────┘
```

**What's verified vs. validated:**
- **Proved (machine-checked)**: Soundness of type system w.r.t. interpreter
- **Proved (machine-checked)**: Each program's typing derivation (via type checker)
- **Validated (testing)**: Interpreter matches Cerberus
- **Trusted**: Cerberus correctly models C, Lean's logic is consistent

### Advantages Over Hoare Logic

| Aspect | Hoare Logic | Refinement Types |
|--------|-------------|------------------|
| Compositionality | Via rule application | Via type composition |
| Inference | Manual loop invariants | Bidirectional propagation |
| Automation | VC generation | Type checking algorithm |
| Integration | External specs | Types are specs |
| Lean fit | Define as Props | Native dependent types |

### Advantages Over iris-lean

| Aspect | iris-lean | Refinement Types |
|--------|-----------|------------------|
| Complexity | Higher-order, step-indexed | First-order, simpler |
| Setup | Need CMRA instantiation | Just define type rules |
| Concurrency | Built-in | Would need extension |
| Learning curve | Steep (Iris concepts) | Moderate (familiar types) |
| Proof burden | Iris tactics | Lean tactics + SMT |

### Challenges

1. **Defining the type system precisely**: Many rules, need to get them right
2. **Termination of type checking**: Bidirectional systems need care
3. **Resource inference**: CN has clever tricks for inferring iterated resources
4. **Completeness**: Will we reject valid programs?

### The Separation Logic Question

**Key issue**: The resource types (`Owned<T>(p)`, `Block<T>(p)`) and their composition are fundamentally separation logic concepts. To reason about them properly, we need:

- **Separating conjunction (∗)**: "I own P and separately own Q"
- **Frame rule**: If `{P} c {Q}` and c doesn't touch R, then `{P ∗ R} c {Q ∗ R}`
- **Magic wand (−∗)**: For describing how ownership transfers

#### Option A: Minimal Custom Separation Logic

Build just enough separation logic for our needs:

```lean
-- Minimal separation logic for resources
structure SepState where
  heap : Pointer → Option Value

-- Separating conjunction: disjoint heaps
def sepConj (P Q : SepState → Prop) : SepState → Prop :=
  fun s => ∃ s1 s2, s = s1 ⊕ s2 ∧ disjoint s1 s2 ∧ P s1 ∧ Q s2

-- Prove frame rule, etc. for our specific use case
theorem frame_rule : ...
```

**Pros**: Lightweight, tailored to our needs, no external dependencies
**Cons**: Reinventing the wheel, may miss subtleties, limited reuse

#### Option B: Use iris-lean

Instantiate iris-lean with our memory model:

```lean
-- Our memory as a CMRA (commutative resource algebra)
instance : CMRA CMemory where
  ...

-- Get separation logic for free
-- Owned<T>(p) becomes a points-to assertion in Iris
def Owned (T : CType) (p : Pointer) : iProp := p ↦ᵢ v
```

**Pros**: Battle-tested separation logic, MoSeL tactics, future-proof
**Cons**: Steep learning curve, need to instantiate CMRA, iris-lean still maturing

#### Option C: Hybrid - Simple Now, Iris Later

Start with a simple resource model that's *compatible* with separation logic but doesn't require the full machinery:

```lean
-- Resources as a multiset (simple model)
abbrev Resources := Multiset Resource

-- Disjoint union (separating conjunction at the resource level)
def Resources.disjointUnion (r1 r2 : Resources) : Option Resources :=
  if r1.Disjoint r2 then some (r1 ∪ r2) else none

-- Frame rule is trivial at this level
theorem frame_rule :
  hasType Γ e τ Γ' →
  (Γ.resources ∪ R).Disjoint →
  hasType (Γ.addResources R) e τ (Γ'.addResources R)
```

Then later, if we need more sophisticated reasoning:
- Redefine resources as Iris iProp
- Existing typing rules should mostly still work
- Gain access to iris-lean tactics

#### What CN Does

CN sidesteps much of this by:
1. **Not exposing separating conjunction to users** - you just list resources
2. **Automatically threading resources through** - the type system handles it
3. **Using ownership as tokens** - not full separation logic assertions

The CN paper notes they deliberately chose a simpler model than full separation logic to make inference predictable.

#### Recommendation

**Start with Option C** (simple resource multiset):
- Resources are just a collection you have
- Disjointness is implicit (can't have same resource twice)
- Frame rule comes for free
- Sufficient for most C verification

**Defer to iris-lean** if we need:
- Higher-order resources (storing predicates in memory)
- Concurrent reasoning
- Complex ownership patterns (fractional permissions, etc.)

This matches CN's pragmatic approach: enough separation logic to handle memory ownership, without the full complexity of Iris.

### Recommended Approach

**Phase 1: Core refinement types**
- Base types with refinements: `{x : Int | 0 ≤ x}`
- Simple ownership: `Owned<T>(p)` and `Block<T>(p)`
- Function pre/postconditions

**Phase 2: Resource inference**
- Iterated ownership for arrays
- Automatic resource threading

**Phase 3: User-defined predicates**
- Abstract predicates (like CN's `predicate` definitions)
- Recursive data structure specs

### Assessment

This is probably **the most promising approach** for our project because:

1. **Natural fit**: We already have Core IR in Lean; adding types is incremental
2. **Proven design**: CN shows it works for real systems code
3. **Lean synergy**: Dependent types make refinements natural
4. **Incremental**: Can start simple, add features as needed
5. **Explainable**: Refinement types are more familiar than separation logic

The main question is how much of CN's design to replicate vs. simplify. CN has sophisticated resource inference we might defer.

---

## Hybrid Approaches

### Combining Techniques

In practice, different techniques work better for different aspects:

1. **Separation Logic** for heap-manipulating code
2. **Refinement Types** for simple invariants
3. **WP Calculus** for generating VCs
4. **Symbolic Execution** for bug finding
5. **Denotational Semantics** for program equivalence

### Suggested Architecture
```
                    ┌─────────────────────┐
                    │  User Specifications │
                    │   (Hoare triples,   │
                    │    refinement types) │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │   Reasoning Layer   │
                    │  (Sep Logic rules,  │
                    │   WP transformer)   │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │  Soundness Proofs   │
                    │  (w.r.t. operational│
                    │     semantics)      │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │ Operational Semantics│
                    │  (Lean Interpreter) │
                    └─────────────────────┘
```

---

## Recommended Path Forward

Given the analysis above, **Approach 10 (Refinement Types over Core IR)** appears most promising. Here's a revised roadmap:

### Phase 1: Foundation (Current)
- Complete the interpreter matching Cerberus
- Ensure operational semantics is clean and well-documented
- Build test infrastructure for confidence

### Phase 2: Basic Refinement Types
- Define `RType` for refined base types: `{v : Int | φ(v)}`
- Implement typing contexts (computational, logical, constraints)
- Define typing rules for pure expressions
- **Goal**: Type-check simple arithmetic programs

### Phase 3: Ownership and Memory
- Add resource types: `Owned<T>(p)`, `Block<T>(p)`
- Define linear resource tracking in contexts
- Typing rules for `load`, `store`, `alloc`, `free`
- **Goal**: Type-check programs with pointer manipulation

### Phase 4: Soundness
- Prove progress: well-typed expressions can step
- Prove preservation: typing preserved after stepping
- Prove UB-freedom: well-typed programs don't hit UB
- **Goal**: Formal guarantee that typed programs are safe

### Phase 5: Automation & Usability
- Bidirectional type inference where possible
- Integration with `omega`/`simp` for constraint solving
- Consider SMT integration for harder constraints
- User-friendly error messages
- **Goal**: Practical tool for verifying C code

### Phase 6: Advanced Features (as needed)
- Iterated resources for arrays (`each` in CN)
- User-defined predicates for data structures
- Loop invariant inference
- Integration with iris-lean if it matures

### Alternative Paths

If refinement types prove too complex initially:

**Simpler alternative: Shallow Hoare Logic**
- Skip to Approach 1 (basic separation logic)
- Prove rules sound against interpreter
- Less automation, more manual proofs
- Can still evolve toward refinement types later

**If iris-lean matures:**
- Monitor the project for program logic additions
- Could migrate our resources/ownership model
- Would gain sophisticated tactics for free

---

## Open Questions

1. **How much of CN can we reuse?** CN is battle-tested on real systems (pKVM). Can we:
   - Parse CN specs and translate to Lean assertions?
   - Use CN's resource predicates as a template for our own?
   - Eventually prove CN's type system sound w.r.t. our semantics?
   See Approach 9 for detailed analysis.

2. **What's the right assertion language?** Should predicates be deeply or shallowly embedded?
   - Deep: assertions are syntax, can analyze/transform them
   - Shallow: assertions are Lean Props, full expressiveness
   - Hybrid: shallow for expressiveness, with reflected syntax for automation

3. **How to handle C's dark corners?** Integer overflow, strict aliasing, unspecified evaluation order...
   - Our Cerberus-based semantics already handles much of this
   - Key question: do we expose all the complexity or provide "safe" abstractions?

4. **What proof automation exists?** Can we leverage Lean 4's metaprogramming?
   - VC generation via tactics
   - Domain-specific decision procedures
   - Integration with external SMT solvers (like CN uses Z3)

5. **What's our primary use case?** This affects which approach to prioritize:
   - Bug finding → symbolic execution, testing
   - Full verification → separation logic, Hoare logic
   - Equivalence proofs → denotational semantics
   - Teaching → simpler is better

6. **Should we target Core IR or C source?**
   - Core IR: faithful to semantics, but further from user's code
   - C source: familiar, but need to handle preprocessing, parsing
   - Hybrid: specs in C comments (like CN), reasoning on Core

7. **iris-lean vs. custom logic?**
   - iris-lean has MoSeL tactics but no program logic yet
   - Building our own is more work but more control
   - Could design for future iris-lean compatibility

8. **Collaboration with Cerberus/CN team?**
   - They're actively developing CN and may be interested
   - Could coordinate on JSON export of specs
   - Potential research collaboration on soundness proofs

---

## References

### Separation Logic
- Reynolds, "Separation Logic: A Logic for Shared Mutable Data Structures" (2002)
- O'Hearn, "A Primer on Separation Logic" (2012)
- [Iris Lecture Notes](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf)

### Iris in Lean
- [iris-lean](https://github.com/leanprover-community/iris-lean) - Lean 4 port of Iris (MoSeL tactics, uPred logic)
- [Eileen: A plan for Iris in Lean](https://www.markusde.ca/pages/eileen.html) - Alternative reimplementation effort
- [What does iris-lean do?](https://www.markusde.ca/pages/iris_lean.html) - Analysis of current iris-lean status

### Verified C
- Appel, "Program Logics for Certified Compilers" (VST book)
- CompCert documentation

### Cerberus
- Memarian et al., "Cerberus-BMC" (2023)
- CN specification language documentation

### Lean Verification
- Lean 4 documentation on tactics and metaprogramming
- Mathlib proof techniques

### General
- Winskel, "The Formal Semantics of Programming Languages"
- Pierce, "Software Foundations" series
