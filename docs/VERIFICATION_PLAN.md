# Verification Planning Document

This document outlines strategies for enabling formal verification of C programs in Lean, building on the existing interpreter infrastructure.

## Current State

**What We Have:**
- Working Core IR parser (100% on 5500+ test files)
- Small-step interpreter matching Cerberus semantics (100% on minimal tests, 91% on CI)
- Concrete memory model with allocation-ID provenance
- `UndefinedBehavior` type covering all major UB categories
- `InterpM` monad: `ReaderT InterpEnv (StateT InterpState (Except InterpError))`

**What We Need:**
- A way to state and prove that programs don't exhibit undefined behavior
- Higher-level reasoning principles beyond step-by-step execution
- Potential SMT integration for automated proof discharge

## Goal: UB-Freeness Reasoning

The primary goal is to prove properties of the form:

```lean
theorem program_ub_free :
  ∀ inputs, precondition inputs →
    match runProgram program inputs with
    | .error (.undefinedBehavior _) => False
    | _ => True
```

More generally, we want to prove **functional correctness**:
```lean
theorem program_correct :
  ∀ inputs, precondition inputs →
    match runProgram program inputs with
    | .ok result => postcondition inputs result
    | .error (.undefinedBehavior _) => False
```

## Architectural Options

Based on the analysis in `docs/REASONING.md`, here are the viable approaches ranked by complexity and capability:

### Option 1: Direct Interpreter Reasoning (Simplest)

**Approach:** Prove properties directly about `InterpM` computations using Lean's native facilities.

```lean
/-- A computation is UB-free if it never produces a UB error -/
def UBFree {α : Type} (m : InterpM α) : Prop :=
  ∀ env state,
    match (m.run env).run state with
    | .ok _ => True
    | .error (.undefinedBehavior _) => False
    | .error _ => True  -- other errors are not UB

/-- Simple arithmetic is UB-free -/
theorem add_ubfree (a b : Int) (h : a + b ∈ Int32Range) :
  UBFree (evalBinop .add (Value.int a) (Value.int b)) := by
  ...
```

**Pros:**
- No new abstractions needed
- Direct correspondence to interpreter
- Can start immediately

**Cons:**
- Doesn't scale to complex programs
- No compositionality (can't reason about parts independently)
- Manual proofs for everything

**Recommendation:** Good for initial exploration and simple lemmas, but not sufficient for real programs.

### Option 2: Weakest Precondition (WP) Calculus

**Approach:** Define a WP transformer that computes the weakest precondition for a program to satisfy a postcondition without UB.

```lean
/-- Weakest precondition: what must be true before execution
    for the postcondition to hold after, with no UB -/
def wp (e : AExpr) (Q : Value → InterpState → Prop) : InterpState → Prop :=
  fun s => ∀ env,
    match runExpr env s e with
    | .ok (v, s') => Q v s'
    | .error (.undefinedBehavior _) => False
    | .error _ => True

-- Compositional rules
theorem wp_seq (e1 e2 : AExpr) (Q : Value → InterpState → Prop) :
  wp (seq e1 e2) Q = wp e1 (fun _ s => wp e2 Q s) := by
  ...

-- For conditionals
theorem wp_if (c : APexpr) (e1 e2 : AExpr) (Q : Value → InterpState → Prop) :
  wp (if_ c e1 e2) Q = fun s =>
    evalCond c s = some true  → wp e1 Q s ∧
    evalCond c s = some false → wp e2 Q s := by
  ...
```

**Pros:**
- Compositional reasoning
- Can generate verification conditions automatically
- Well-understood theory

**Cons:**
- Loops require invariants (no free lunch)
- Memory operations complicate the WP transformer
- Need to prove WP rules sound w.r.t. interpreter

**Recommendation:** Good middle ground. Provides structure without full separation logic complexity.

### Option 3: Refinement Types / Specifications

**Approach:** Define a type system over Core IR where types carry specifications (preconditions, postconditions, ownership).

This is the approach used by CN (Cerberus's verification tool) and is analyzed extensively in `docs/REASONING.md` (Approach 10).

```lean
/-- A refined type: base type + refinement predicate -/
structure RType where
  base : BaseType
  refine : Value → Prop

/-- Function specification -/
structure FnSpec where
  requires : InterpState → Prop
  ensures : Value → InterpState → InterpState → Prop

/-- Typing judgment: Γ ⊢ e : τ -/
inductive HasType : Ctx → AExpr → RType → Prop where
  | pure_int : (n ∈ Int32Range) → HasType Γ (pure (val (int n))) ⟨.int, fun v => v = int n⟩
  | binop_add : HasType Γ e1 τ1 → HasType Γ e2 τ2 →
      (∀ v1 v2, τ1.refine v1 → τ2.refine v2 → v1.toInt + v2.toInt ∈ Int32Range) →
      HasType Γ (binop .add e1 e2) ⟨.int, ...⟩
  ...

/-- Soundness: well-typed programs don't UB -/
theorem soundness : HasType Γ e τ → SemanticallyValid Γ e τ := by
  ...
```

**Pros:**
- Types are specifications (familiar paradigm)
- Compositional by construction
- Can track ownership/resources for memory safety
- Proven successful (CN, VST)

**Cons:**
- Significant upfront work to define type system
- Need to prove soundness
- May need resource/ownership tracking for full memory safety

**Recommendation:** The most scalable approach for real verification. Should be the eventual target.

### Option 4: Separation Logic via iris-lean

**Approach:** Use the iris-lean library to get separation logic infrastructure.

```lean
-- Using Iris-style propositions
def Owned (p : Pointer) (v : Value) : iProp := ...
def Block (p : Pointer) (size : Nat) : iProp := ...

-- Hoare triple with separation logic
def hoare (P : iProp) (e : AExpr) (Q : Value → iProp) : Prop := ...

-- Frame rule comes for free
theorem frame_rule : hoare P e Q → hoare (P ∗ R) e (fun v => Q v ∗ R) := ...
```

**Pros:**
- Battle-tested separation logic theory
- Natural handling of pointer aliasing
- MoSeL tactics available

**Cons:**
- iris-lean is still maturing (no program logic instantiated yet)
- Complex framework with steep learning curve
- Need to instantiate CMRA for our memory model

**Recommendation:** Monitor for future adoption, but too heavyweight for initial implementation.

## Recommended Phased Approach

### Phase 1: Foundation - UBFree Predicate & Simple Properties

**Goal:** Define basic predicates and prove simple properties directly.

**Tasks:**
1. Define `UBFree` predicate for interpreter computations
2. Define `Terminates` predicate (program doesn't loop forever or error)
3. Prove simple lemmas about primitive operations:
   - Integer arithmetic overflow conditions
   - Pointer dereference validity
   - Array bounds checking

**Deliverables:**
```lean
-- In CToLean/Theorems/UBFree.lean
def UBFree (m : InterpM α) : Prop := ...
def NoUB (e : AExpr) (env : InterpEnv) (state : InterpState) : Prop := ...

-- Simple lemmas
theorem int_add_safe (a b : Int) (h : a + b ∈ Int32Range) :
  UBFree (evalBinop .add (Value.int a) (Value.int b))

theorem load_safe (p : Pointer) (s : InterpState)
  (h_valid : s.memory.isValidPointer p)
  (h_init : s.memory.isInitialized p) :
  NoUB (load p) env s
```

### Phase 2: Weakest Precondition Infrastructure

**Goal:** Build WP calculus for compositional reasoning.

**Tasks:**
1. Define `wp` transformer for expressions
2. Prove soundness: `wp e Q s → (runExpr e s).satisfies Q`
3. Prove compositional rules (seq, if, let, etc.)
4. Handle loops with explicit invariant parameter

**Deliverables:**
```lean
-- In CToLean/Theorems/WP.lean
def wp (e : AExpr) (Q : Value → InterpState → Prop) : InterpState → Prop := ...

theorem wp_sound : wp e Q s → NoUB e env s ∧ (∀ v s', runExpr e s = .ok (v, s') → Q v s')

-- Compositional rules
theorem wp_seq : wp (seq e1 e2) Q = wp e1 (fun _ s => wp e2 Q s)
theorem wp_if : wp (if_ c e1 e2) Q = ...
theorem wp_let : wp (let_ x e1 e2) Q = wp e1 (fun v s => wp (e2.subst x v) Q s)
```

### Phase 3: SMT Integration (lean-smt)

**Goal:** Automate proof of arithmetic/logical verification conditions.

**Tasks:**
1. Integrate lean-smt for decidable subgoals
2. Define tactics that generate SMT queries from VCs
3. Handle common patterns: bounds checks, overflow, pointer arithmetic

**Deliverables:**
```lean
-- Tactic that dispatches to SMT
macro "smt" : tactic => ...

-- Example usage
theorem array_access_safe (arr : Pointer) (i : Nat) (len : Nat)
  (h_bounds : i < len) (h_valid : validArray arr len s) :
  NoUB (arrayLoad arr i) env s := by
  unfold NoUB arrayLoad wp
  smt  -- SMT solver proves i < len → no out-of-bounds
```

**lean-smt Resources:**
- GitHub: https://github.com/ufmg-smite/lean-smt
- Supports bitvectors, arrays, uninterpreted functions
- Can export to SMT-LIB format

### Phase 4: Function Specifications

**Goal:** Enable modular reasoning about functions.

**Tasks:**
1. Define function specification syntax (pre/postconditions)
2. Implement specification checking
3. Allow assuming function specs when verifying callers

**Deliverables:**
```lean
-- Function specification
structure FnSpec where
  name : Sym
  requires : List Value → InterpState → Prop
  ensures : List Value → InterpState → Value → InterpState → Prop

-- Specification registry
def specs : HashMap Sym FnSpec := ...

-- Modular verification: assume callee specs hold
theorem call_with_spec (spec : FnSpec) (args : List Value) (s : InterpState)
  (h_pre : spec.requires args s)
  (h_spec_valid : FnSpecValid spec) :
  NoUB (call spec.name args) env s ∧
  ∀ v s', runCall spec.name args s = .ok (v, s') → spec.ensures args s v s'
```

### Phase 5: Memory Ownership (Lightweight Separation Logic)

**Goal:** Track memory ownership for safe pointer reasoning.

**Tasks:**
1. Define resource predicates: `Owns`, `ValidPtr`, `Initialized`
2. Implement simple linear resource tracking
3. Prove frame-like properties

**Deliverables:**
```lean
-- Ownership predicates
def Owns (p : Pointer) (v : Value) (s : InterpState) : Prop := ...
def ValidPtr (p : Pointer) (s : InterpState) : Prop := ...

-- Separation-like composition
def SepAnd (P Q : InterpState → Prop) : InterpState → Prop := ...

-- Frame property for memory-safe operations
theorem store_frame (p : Pointer) (v : Value) (P : InterpState → Prop)
  (h_owns : Owns p old_v s)
  (h_frame : P.frameIndependent p) :
  P s → P (s.store p v) ∧ Owns p v (s.store p v)
```

## Key Design Decisions

### 1. Shallow vs. Deep Embedding

**Decision:** Use **shallow embedding** for predicates (they are Lean Props directly).

**Rationale:**
- Full Lean expressiveness
- No parsing/reflection overhead
- Can always add reflection layer later for automation

### 2. State Representation

**Decision:** Continue using `InterpState` directly, don't create separate logical state.

**Rationale:**
- Soundness is immediate (same state as interpreter)
- No extra abstraction barrier
- Can extract computational content for testing

### 3. Handling Loops

**Decision:** Require explicit invariants, use WP with invariant parameter.

**Rationale:**
- No magic - loop verification is fundamentally hard
- User provides invariant, system checks it
- Can add invariant inference heuristics later

### 4. SMT Integration Strategy

**Decision:** Use lean-smt for decidable arithmetic, keep higher-level reasoning in Lean.

**Rationale:**
- SMT excels at QF_BV, QF_LIA (bitvectors, linear integer arithmetic)
- Lean excels at inductive reasoning, memory ownership
- Hybrid approach gets best of both

## Example: Verifying a Simple Program

Consider verifying that `abs(x)` doesn't overflow:

```c
int abs(int x) {
    if (x < 0) return -x;
    return x;
}
```

**Specification:**
```lean
def abs_spec : FnSpec := {
  name := "abs"
  requires := fun args s =>
    args.length = 1 ∧
    ∃ x : Int, args[0]! = Value.int x ∧ x ≠ INT_MIN  -- precondition
  ensures := fun args s_pre v s_post =>
    ∃ x : Int, args[0]! = Value.int x ∧
    v = Value.int (Int.natAbs x) ∧
    s_post.memory = s_pre.memory  -- pure function
}
```

**Verification:**
```lean
theorem abs_correct : FnSpecValid abs_spec := by
  unfold FnSpecValid abs_spec
  intro args s h_pre
  obtain ⟨h_len, x, h_arg, h_not_min⟩ := h_pre
  -- Unfold the Core IR for abs
  simp only [abs_core_ir]
  -- Split on x < 0
  by_cases h : x < 0
  · -- Negative case: return -x
    -- Need to prove -x doesn't overflow
    have h_no_overflow : -x ∈ Int32Range := by
      -- x ≠ INT_MIN and x < 0 implies -x ≤ INT_MAX
      smt
    apply wp_if_true h
    apply wp_neg h_no_overflow
  · -- Non-negative case: return x
    apply wp_if_false h
    apply wp_pure
```

## Milestones and Success Criteria

| Phase | Milestone | Success Criteria |
|-------|-----------|------------------|
| 1 | UBFree predicate | Can state and prove 5 simple properties |
| 2 | WP calculus | Compositional rules for seq, if, let, call |
| 3 | SMT integration | `smt` tactic works for arithmetic VCs |
| 4 | Function specs | Can verify `abs`, `max`, `min` with specs |
| 5 | Memory ownership | Can verify simple pointer programs |

## Open Questions

1. **How much of CN's design to replicate?** CN has sophisticated resource inference. Start simple, add as needed.

2. **Should we support invariant inference?** Probably not initially - focus on verification with user-provided invariants.

3. **How to handle unbounded loops?** Use fuel/gas for termination, or require termination proofs.

4. **Integration with Cerberus CN specs?** Future work - could parse CN annotations from JSON export.

## References

- `docs/REASONING.md` - Detailed analysis of verification approaches
- `docs/modelling_investigation-2025-12-24.md` - Architecture recommendations
- [lean-smt](https://github.com/ufmg-smite/lean-smt) - SMT solver integration for Lean 4
- [iris-lean](https://github.com/leanprover-community/iris-lean) - Separation logic framework
- [CN Paper](https://www.cl.cam.ac.uk/~cp526/popl23.html) - Cerberus verification system
