# CN as a Separation Logic Type System Over Core

*Created: 2026-02-27*

## The Idea

Define CN verification as a **type system** (or program logic) directly over
the Cerberus Core AST. Each AST node is decorated with heap resource
annotations, and well-typedness implies memory safety.

```
Γ; H₁ ⊢ e : τ ⊣ H₂
```

"In context Γ, with resources H₁, expression e has type τ and produces
resources H₂."

This replaces CN's current architecture (an ad-hoc VC generator that walks
the AST, maintains mutable resource state, and defers to SMT) with a
**declarative** system where:

- The typing rules define what "correct" means
- A derivation tree IS a correctness proof
- CN becomes a proof search algorithm that finds derivation trees
- Soundness w.r.t. the interpreter is a single theorem

---

## What CN Actually Is (for context)

CN is a refinement type system + separation logic verifier for C. Key features:

**Specification language:**
```c
int increment(int *p)
/*@ requires take v = Owned<int>(p);
    ensures  take v2 = Owned<int>(p);
             v2 == v + 1;
             return == v; @*/
```

**Resources**: `Owned<T>(p)` (read/write ownership), `Block<T>(p)` (uninit),
user-defined predicates.

**Iterated resources**: `each(i; 0<=i<n) { Owned<int>(p+i) }` — ownership
of array ranges.

**Logical functions/predicates**: User-defined recursive predicates that
unfold/fold (e.g., linked list predicates).

**Current implementation** (OCaml, and our Lean port in `CerbLean/CN/`):
- Walks Core AST in continuation-passing style
- Maintains a mutable resource context (`List Resource`)
- At each memory operation: match request against context (syntactic, then SMT)
- At each constraint: generate an obligation, defer to SMT
- At function calls: consume precondition resources, produce postcondition resources
- Dead code: detect via "conditional failure" (prove branch unreachable post-hoc)

The problem: there are no clean typing rules. The "logic" is whatever the
OCaml code happens to do. This makes it hard to:
- State and prove soundness
- Understand what's actually being verified
- Separate specification from implementation

---

## The Type System

### Resources (Heap Propositions)

```lean
inductive SLProp where
  | emp                                                    -- empty heap
  | owned (ty : Ctype) (ptr : IndexTerm) (val : IndexTerm) -- Owned<T>(p, v)
  | block (ty : Ctype) (ptr : IndexTerm)                   -- Block<T>(p)
  | pred (name : Sym) (ptr : IndexTerm)
         (args : List IndexTerm) (out : IndexTerm)         -- user predicate
  | star (P Q : SLProp)                                    -- P ∗ Q
  | each (var : Sym) (ty : BaseType) (guard : IndexTerm)
         (body : SLProp)                                   -- iterated ∗
  | pure (p : IndexTerm)                                   -- pure constraint
  | ex (var : Sym) (ty : BaseType) (body : SLProp)         -- ∃x:τ. P
```

### Typing Judgments

**Pure expressions** (no heap change):
```
Γ ⊢ pe : τ          (standard typing, heap-irrelevant)
─────────────────
Γ; H ⊢ pure(pe) : τ ⊣ H
```

**Strong sequence** (resources thread through):
```
Γ; H₁ ⊢ e₁ : τ₁ ⊣ H₂       Γ, x:τ₁; H₂ ⊢ e₂ : τ₂ ⊣ H₃
─────────────────────────────────────────────────────────────
Γ; H₁ ⊢ sseq x = e₁ in e₂ : τ₂ ⊣ H₃
```

**Weak sequence** (same as strong for sequential programs):
```
Γ; H₁ ⊢ e₁ : τ₁ ⊣ H₂       Γ, x:τ₁; H₂ ⊢ e₂ : τ₂ ⊣ H₃
─────────────────────────────────────────────────────────────
Γ; H₁ ⊢ wseq x = e₁ in e₂ : τ₂ ⊣ H₃
```

**Conditional** (both branches from same pre-heap):
```
Γ ⊢ c : bool       Γ; H ⊢ e₁ : τ ⊣ H₁       Γ; H ⊢ e₂ : τ ⊣ H₂
────────────────────────────────────────────────────────────────────
Γ; H ⊢ if c then e₁ else e₂ : τ ⊣ H₁ ⊔ H₂
```

(Where `H₁ ⊔ H₂` is the join — both branches must produce compatible
resources. In practice: same resources, possibly with different values
expressed via a conditional.)

**Load** (consume Owned, read value, re-emit):
```
H = Owned<T>(p, v) ∗ H_frame
──────────────────────────────────────────
Γ; H ⊢ load(T, p) : loaded(v) ⊣ Owned<T>(p, v) ∗ H_frame
```

**Store** (consume Owned, update value):
```
H = Owned<T>(p, v_old) ∗ H_frame       Γ ⊢ v_new : T
──────────────────────────────────────────────────────
Γ; H ⊢ store(T, p, v_new) : unit ⊣ Owned<T>(p, v_new) ∗ H_frame
```

**Create** (produce fresh Block):
```
p fresh
──────────────────────────────────────────────────────
Γ; H ⊢ create(T, align) : ptr(p) ⊣ Block<T>(p) ∗ H
```

**Kill** (consume resource, nothing left):
```
H = Owned<T>(p, v) ∗ H_frame
──────────────────────────────────────────────────────
Γ; H ⊢ kill(p) : unit ⊣ H_frame
```

**Function call** (consume pre-resources, produce post-resources):
```
f has spec:  ∀args. { H_pre(args) } f(args) { ∃ret. H_post(args, ret) }
H = H_pre(vs) ∗ H_frame
──────────────────────────────────────────────────────
Γ; H ⊢ call f(vs) : τ ⊣ H_post(vs, ret) ∗ H_frame
```

**Frame** (admissible — anything not mentioned is preserved):
```
Γ; H₁ ⊢ e : τ ⊣ H₂
──────────────────────────────────────────────────────
Γ; H₁ ∗ H_frame ⊢ e : τ ⊣ H₂ ∗ H_frame
```

### Soundness Theorem

```lean
theorem soundness :
  HasType Γ H₁ e τ H₂ →     -- well-typed in the SL type system
  models σ Γ →                -- memory state models the variable context
  models σ H₁ →              -- memory state satisfies the resource precondition
  ∃ v σ',
    runInterp e σ = .ok (v, σ')  ∧  -- interpreter succeeds (no UB)
    hasBaseType v τ              ∧  -- result has expected type
    models σ' H₂                    -- final state satisfies postcondition
```

This single theorem says: well-typed programs don't go wrong. It connects
the type system to the interpreter.

---

## Complexities and Whether They're Fatal

### 1. Quantified Variables in Specs (Dependent Types)

CN specs have sequential dependencies:
```c
requires take v1 = Owned<int>(p);    // binds v1
         take v2 = Owned<int>(q);    // binds v2
         v1 + v2 > 0;               // uses both
```

The `take` pattern binds the stored value to a logical variable. Later
clauses can mention earlier-bound variables. This is a **telescope**:

```lean
(v1 : Int) × Owned<int>(p, v1) × (v2 : Int) × Owned<int>(q, v2) × (v1 + v2 > 0)
```

**Verdict: Encodable.** This is a dependent product (sigma type). The
typing rules naturally handle this — the bound variable enters the context
and is available in subsequent rules. This is exactly how CN's `LAT` chain
works (`define`, `resource`, `constraint` in sequence), and it maps directly
to dependent types.

In the typing rules, the function call rule becomes:
```
f spec: (v1 : Int) × Owned<int>(p, v1) × (v1 > 0) → ...
```

The caller must provide a resource `Owned<int>(p, v1)` for SOME `v1`,
plus a proof that `v1 > 0`. The existential quantification over `v1`
comes from matching the resource against the context.

### 2. Iterated Resources (`each`)

```c
requires each(int i; 0 <= i && i < n) { take v_i = Owned<int>(p + i) }
```

This is an iterated separating conjunction:
```
∗_{i=0}^{n-1} ∃v_i. Owned<int>(p + i, v_i)
```

**Operations needed:**
- **Instantiation**: Extract element `k` from `each(0..n)` to get `Owned<int>(p+k)`
- **Splitting**: Split `each(0..n)` into `each(0..k) ∗ each(k..n)`
- **Merging**: Combine `each(0..k) ∗ each(k..n)` back to `each(0..n)`
- **Update**: Replace element `k`'s value after a store

**Verdict: Hard but standard.** These operations require arithmetic
reasoning (is `k` in range? is `k < n`?) which generates pure VCs sent to
SMT. The typing rules for array access become:

```
H = each(i; guard(i)) { Owned<T>(p+i, v(i)) } ∗ H_frame
guard(k) holds            -- VC: prove index in range
────────────────────────────────────────────────────────
Γ; H ⊢ load(T, p+k) : loaded(v(k)) ⊣
    each(i; guard(i)) { Owned<T>(p+i, v(i)) } ∗ H_frame
```

The `v(i)` is a logical function from index to value. After a store at
index `k`, it becomes `v[k ↦ new_val]` (map update).

This is the approach used by Iris's arrays and VeriFast's arrays. It works,
but the arithmetic VCs can be complex.

### 3. User-Defined Predicates (Recursive)

```c
predicate List(pointer p) {
  if (p == NULL) { return Nil {}; }
  else {
    take h = Owned<struct node>(p);
    take tl = List(h.next);
    return Cons { head: h.data, tail: tl };
  }
}
```

This is an inductively-defined predicate. In separation logic terms:
```
List(p) ≜ (p = NULL ∧ emp)
         ∨ (∃h,tl. p ≠ NULL ∧ Owned<node>(p, h) ∗ List(h.next, tl))
```

**Operations needed:**
- **Unfold**: Replace `List(p)` with its definition (case split on p)
- **Fold**: Match resources against definition, replace with `List(p)`

**Verdict: Tractable with restrictions.** If predicates are well-founded
(every recursive call is on a structurally smaller pointer), unfolding
terminates. The typing rules need explicit fold/unfold steps:

```
unfold: Γ; List(p) ∗ H ⊢ e : τ ⊣ H'
    ↔   Γ; (p=NULL ∧ emp) ∨ (∃h,tl. Owned<node>(p,h) ∗ List(h.next,tl)) ∗ H ⊢ e : τ ⊣ H'
```

The complication is that fold/unfold must be triggered explicitly (or
heuristically). CN does this during resource inference — when a request
for `List(p)` doesn't match any resource directly, it tries unfolding
available predicates. In the type system, this becomes a proof search
strategy.

### 4. Resource Inference (Proof Search)

The typing rules are declarative: they say WHAT a correct derivation looks
like. But FINDING the derivation requires:

- **Frame inference**: Given `H = H_pre ∗ ?frame`, find `?frame`
- **Resource matching**: Given request `Owned<T>(p)`, find which resource in
  context provides it (may require pointer arithmetic reasoning)
- **Predicate folding**: When to fold/unfold recursive predicates
- **Existential witnesses**: When consuming `∃v. Owned<T>(p, v)`, what is `v`?

**Verdict: This is the hard engineering problem, not a theoretical one.**
The type system is sound regardless of how inference works. CN's current
approach (syntactic matching + SMT fallback) is one strategy. A cleaner
approach might use bidirectional type checking:

- **Checking mode**: Given pre-resources, check that the code produces
  post-resources (top-down, function bodies)
- **Synthesis mode**: Given code, synthesize what resources it needs
  (bottom-up, leaf expressions)

### 5. Conditional Branches and Dead Code

```c
if (x > 0) {
  // branch A: resources flow normally
} else {
  // branch B: might be unreachable
}
```

If branch B is unreachable (`x > 0` always holds), it shouldn't matter
that branch B would violate resource discipline.

**Verdict: Handled by adding path conditions to the context.** The typing
rule for conditionals becomes:

```
Γ, (c = true);  H ⊢ e₁ : τ ⊣ H₁
Γ, (c = false); H ⊢ e₂ : τ ⊣ H₂
─────────────────────────────────────
Γ; H ⊢ if c then e₁ else e₂ : τ ⊣ (c ? H₁ : H₂)
```

If `Γ ⊢ c = true` (branch B is dead), then the obligation for branch B
is vacuously satisfied. This is standard.

### 6. Ghost Variables and Logical-Only State

CN specs can introduce "ghost" variables that exist only in the logic:
```c
/*@ ghost int count; @*/
```

**Verdict: Natural.** Ghost variables are just universally quantified
variables in the typing context. They don't correspond to runtime values.

### 7. Loops (Save/Run Continuations)

Core doesn't have explicit loops — it has `Esave`/`Erun` (labeled
continuations). Loops manifest as:
```
save loop_label(args) =
  if (guard) {
    body;
    run loop_label(args')
  } else {
    exit
  }
```

Each label needs a **loop invariant** expressed as a resource assertion:
```
loop_label: { H_inv(args) } → { H_inv(args') }
```

**Verdict: Works, but requires invariants.** The typing rule for
`Erun label(args)` checks that current resources match the label's
invariant, and the typing of the label body checks preservation. Same
as Hoare logic's loop rule. The invariants must come from CN annotations.

### 8. The `old()` Problem

CN postconditions can refer to pre-state values:
```c
ensures v2 == v + 1;  // v from precondition, v2 from postcondition
```

This isn't `old()` in the Boogie sense — it's that `take` binds a
variable in the precondition scope that remains visible in the
postcondition.

**Verdict: Already handled.** The telescope structure (`LAT`/`LRT`)
naturally scopes this. Precondition-bound variables persist into the
postcondition context.

---

## TCB Analysis

The key advantage of this architecture is the **small trusted computing base**.

**Current CN (ad-hoc VC generator):**
```
TCB = CN VC generation code + SMT solver + "VCs correspond to program behavior"
```
If CN's OCaml (or our Lean port) has a bug in how it walks the AST, tracks
resources, or generates constraints, verification is unsound — and there's
no way to detect this short of auditing all of CN's code.

**Type system approach:**
```
TCB = HasType rules (~50-100 constructors) + soundness proof + Lean kernel
```
CN becomes **untrusted proof search**. It produces `HasType` derivation
trees (Lean proof terms). Lean's kernel checks them. If CN has a bug:
- It fails to find a derivation → safe (you get a type error, not unsoundness)
- It produces an invalid derivation → caught by Lean's kernel

The typing rules are small and auditable: one constructor per Core AST node,
each directly corresponding to a separation logic rule. The soundness proof
is machine-checked. CN can be arbitrarily buggy code and it cannot compromise
soundness.

This is the **proof-carrying code** paradigm: trust the checker (the typing
rules), not the prover (CN's search algorithm).

**Practical implication**: We can iterate aggressively on CN's implementation
(heuristics, optimizations, new features) without re-establishing soundness
each time. Soundness is a property of the type system, not of CN.

---

## Assessment: Will This Work?

### What works cleanly

- **Core control flow** (seq, let, if, call, pure): Standard SL rules,
  no complications
- **Basic Owned/Block**: Straightforward consume/produce rules
- **Dependent specs** (take-bound variables): Natural as dependent types /
  telescopes
- **Path conditions and dead code**: Standard path-sensitive typing
- **Ghost variables**: Just universally quantified context variables
- **Soundness statement**: Clean theorem connecting to the interpreter

### What's tractable but requires care

- **Iterated resources (`each`)**: Needs array-level rules with arithmetic
  VCs. Standard in the literature but adds complexity.
- **Recursive predicates**: Need fold/unfold rules with well-foundedness.
  Standard in Iris but adds to the metatheory.
- **Loops (save/run)**: Need invariant annotations. Same as any Hoare logic.

### What's genuinely hard

- **Frame inference**: Given resources and a function spec, automatically
  find the frame. This is decidable for simple cases but NP-hard in general
  (it's essentially the bi-abduction problem from Infer). CN solves it by
  syntactic matching + SMT; a clean system needs to be explicit about what
  inference strategy is used and when.

- **Resource matching with pointer arithmetic**: Is `Owned<int>(p + 2*i)`
  the same as `Owned<int>(q)` when `q = p + 2*i`? This requires an
  entailment check that mixes separation logic with arithmetic. CN defers
  this to SMT; the type system would need to call out to an oracle.

- **Predicate fold heuristics**: When should we unfold `List(p)` vs. keep
  it abstract? This is a proof search problem, not a typing problem. The
  type system can be complete in principle but the search space is large.

### What we should NOT try to solve

- **Automatic loop invariant inference**: Require annotations (like CN does)
- **Automatic predicate synthesis**: Require user-defined predicates
- **Full separation logic entailment**: Use SMT as an oracle for pure facts
- **Concurrency (par/unseq)**: Leave for later; focus on sequential subset

---

## Architecture

```
                  CN specs (annotations on C functions)
                           │
                           ▼
    Core AST ──────── Decorated Core AST
       │              (each node annotated with H_pre, H_post)
       │                       │
       ▼                       ▼
  Interpreter              Type Derivation
  (execution)              (proof of well-typedness)
       │                       │
       ▼                       ▼
  InterpResult          Pure VCs (arithmetic, pointer equality)
                               │
                               ▼
                          SMT / Lean tactics
```

**The three components:**

1. **SLProp + Typing Rules** (`CN/Logic/`): The declarative type system.
   Inductive type `HasType` with one constructor per Core expression form.
   This is the SPECIFICATION of what CN verifies.

2. **Type Checker** (`CN/TypeChecking/`): The algorithmic implementation.
   Walks the AST, maintains resource context, generates VCs. This is the
   IMPLEMENTATION of CN. It must produce valid derivation trees.

3. **Soundness Proof** (`CN/Soundness/`): Theorem connecting the type
   system to the interpreter. This is the CORRECTNESS theorem — well-typed
   programs don't UB.

**The key separation**: The typing rules (component 1) define WHAT is
verified, independently of HOW verification works. The type checker
(component 2) is the proof search engine. Soundness (component 3) connects
to the interpreter. Changing the type checker doesn't invalidate soundness.

---

## Relationship to Current CN Implementation

The current Lean CN code (`CerbLean/CN/`) roughly maps to component 2
(the type checker). What's missing is component 1 (the declarative rules)
and component 3 (the soundness proof).

**Refactoring path:**
1. Define `SLProp` and `HasType` (component 1) — new code
2. Refactor the existing type checker to produce `HasType` derivations
   instead of ad-hoc obligations — moderate refactor
3. Prove soundness (component 3) — significant new work

The existing CN code handles many engineering details (parse CN syntax,
convert index terms, match resources) that remain useful. The refactoring
adds a formal backbone without rewriting everything.

---

## Comparison: Type System vs. Strata/Boole

| | SL Type System | Strata/Boole |
|--|---|---|
| **Defined over** | Core AST directly | Compiled IVL program |
| **Logic** | Separation logic | First-order logic |
| **Memory model** | Resources (Owned, Block) | Maps (Map int int) |
| **Ownership** | Built-in (frame rule) | Encoded (ad-hoc) |
| **CN integration** | Natural (same concepts) | Requires encoding CN into FOL |
| **Soundness target** | Interpreter directly | Via compilation correctness |
| **Pure VC discharge** | SMT / Lean tactics | SMT via Strata |
| **Dependencies** | None (pure Lean) | Strata framework |
| **Iterated resources** | Native (each/∗) | Encoded in quantifiers |

**The SL type system is strictly better for the CN use case.** Strata/Boole
would require encoding separation logic concepts into first-order logic
(which is what VCC did, and it was notoriously complex). The type system
keeps separation logic native.

For pure verification (no memory, just arithmetic), Strata/Boole's SMT
pipeline would be convenient. But `lean-smt` provides the same capability
without the framework dependency.

---

## Open Questions

1. **How much of Iris do we need?** Iris provides a general framework for
   separation logic in Coq. We need much less — no step-indexing, no
   higher-order ghost state, no fancy modalities. Just basic separation
   logic with inductive predicates. But should we look at how Iris handles
   things like iterated separating conjunction?

2. **Semantic vs. syntactic model?** Do we define `SLProp` as syntax
   (inductive type of resource formulas) or semantics (predicates on memory
   states)? Syntax is easier to manipulate but needs a separate interpretation.
   Semantics is more direct but harder to do proof search on. Probably: syntax
   with a semantic interpretation function.

3. **How does this interact with the existing CN code?** The existing
   `CerbLean/CN/TypeChecking/` does resource tracking algorithmically. Can
   we instrument it to produce `HasType` proof terms, or do we need a
   separate verified checker?

4. **How do we handle CN features we haven't implemented yet?** The Lean CN
   port is partial. Do we define the full type system upfront (risk: getting
   it wrong) or incrementally (risk: redesigning as we go)?

5. **Is the soundness proof realistic?** The interpreter has ~150KB of code.
   Soundness requires reasoning about every expression form. Is there a way
   to structure the proof modularly (e.g., one lemma per expression form,
   composed via the typing rules)?
