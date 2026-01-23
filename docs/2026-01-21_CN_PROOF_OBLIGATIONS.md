# CN Proof Obligations Architecture

**Date**: 2026-01-21
**Status**: Design Document
**Author**: Claude + Mike

## Overview

This document describes the architecture for generating and discharging proof obligations in the CN type checker. The design separates **verification condition (VC) generation** from **VC discharge**, enabling multiple proof strategies while maintaining foundational soundness.

### Goals

1. **Foundational Soundness**: All proofs are checked by Lean's kernel - no trusted oracles
2. **Flexibility**: Support multiple proof strategies (SMT, omega, manual proofs, inductive lemmas)
3. **Provable Correctness**: Enable proving CN type checking sound w.r.t. interpreter semantics
4. **Extensibility**: Support complex heap predicates and resource entailments
5. **Integration**: Build on existing semantic machinery in `CN/Semantics/`

### Non-Goals (for now)

- Runtime verification (proofs happen at Lean elaboration time)
- Fully automated proving (some obligations may need manual proofs)
- Certified VC generation (we'll prove it correct, but the checker itself isn't verified)

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                      CN Type Checker                             │
│                                                                  │
│  - Resource tracking (Owned, predicates)                        │
│  - Constraint accumulation                                       │
│  - Optimistic/committed resource matching                        │
│  - Produces: TypeCheckResult with List Obligation               │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Proof Obligations                             │
│                                                                  │
│  Each obligation has:                                           │
│  - A Prop (what needs to be proven)                             │
│  - Source location (for error messages)                         │
│  - Description (human-readable)                                 │
│                                                                  │
│  Obligations are INDEPENDENT - proving one doesn't affect       │
│  which others exist (post-hoc discharge)                        │
└─────────────────────────────────────────────────────────────────┘
                              │
          ┌───────────────────┼───────────────────┐
          ▼                   ▼                   ▼
   ┌─────────────┐    ┌─────────────┐    ┌──────────────┐
   │     SMT     │    │   Omega     │    │   Inductive  │
   │   (smt)     │    │  (omega)    │    │   Lemmas     │
   └─────────────┘    └──────────────┘   └──────────────┘
          │                   │                   │
          └───────────────────┼───────────────────┘
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                 Foundational Lean Proofs                         │
│                                                                  │
│  Real proof terms checked by Lean's kernel                      │
└─────────────────────────────────────────────────────────────────┘
```

## Key Design Decision: No Separation Logic Syntax

We do **NOT** use a syntactic separation logic assertion language (`SLProp` with `*`, `-*`, etc.). Instead:

1. **Resources are data**: `List Resource` (already exists)
2. **Separation is semantic**: `interpResources` uses existential quantification over disjoint sub-heaps
3. **Frame property is a theorem**: `frame_derived` (already proven by Aristotle)

This is simpler and matches CN's actual design. The algebraic properties of partial commutative monoids (PCMs) emerge from the resource list structure, not from syntactic connectives.

### Why This Works

The existing `interpResources` already captures separation:

```lean
-- From CN/Semantics/Interpretation.lean
def interpResources (rs : List Resource) (ρ : Valuation) (h : HeapFragment) : Prop :=
  match rs with
  | [] => h = HeapFragment.empty
  | r :: rs' =>
    ∃ h1 h2,
      h1.disjoint h2 ∧           -- Separation!
      h = h1 ++ h2 ∧
      interpResource r ρ h1 ∧
      interpResources rs' ρ h2
```

And `frame_derived` shows resources compose correctly:

```lean
-- From CN/Semantics/Theorems.lean (proven by Aristotle)
theorem frame_derived
    (rs_used rs_frame : List Resource)
    (ρ : Valuation)
    (h_used h_frame : HeapFragment)
    (hDisj : h_used.disjoint h_frame)
    (hUsedSat : interpResources rs_used ρ h_used)
    (hFrameSat : interpResources rs_frame ρ h_frame)
    : interpResources (rs_used ++ rs_frame) ρ (h_used ++ h_frame)
```

## Key Design Decision: Post-Hoc Proof Discharge

Proof obligations are discharged **after** type checking completes, not during. This works because CN uses **optimistic/committed** resource matching:

### How CN Resource Matching Works

1. **Syntactic matching**: Find a resource that syntactically matches the request
2. **Add equality constraints**: If requesting `Owned(r)` and found `Owned(p)`, add constraint `r == p`
3. **No backtracking**: CN commits to the match and proceeds
4. **Prove later**: All constraints accumulated, checked after type checking

### Example

```c
void foo(int *p, int *q)
/*@ requires Owned(p); Owned(q); @*/
{
    int *r = cond ? p : q;
    *r = 1;  // Which Owned to consume?
}
```

CN's approach:
- Sees request for `Owned(r)`
- Picks one (say `Owned(p)`) based on heuristics/order
- Adds constraint `r == p`
- If unprovable (because `r` might equal `q`), verification fails

CN does **NOT** do case-splitting based on provability. This means:
- Type checking makes deterministic decisions
- All obligations are accumulated
- Obligations are independent - proving one doesn't change others
- Post-hoc discharge is valid

## Existing Infrastructure

### CN/Semantics/Heap.lean

```lean
-- Location in concrete memory
structure Location where
  allocId : Nat
  addr : Nat

-- Concrete values in memory
inductive HeapValue where
  | integer (ity : IntegerType) (val : Int)
  | pointer (addr : Option Location)
  | struct_ (tag : Sym) (fields : List (Identifier × HeapValue))
  | array (elemTy : Ctype) (elems : List HeapValue)
  | uninitialized (ty : Ctype)

-- Heap fragment with disjointness
structure HeapFragment where
  cells : List (Location × HeapValue)

def HeapFragment.disjoint (h1 h2 : HeapFragment) : Prop :=
  ∀ loc, loc ∈ h1.dom → loc ∉ h2.dom

-- Symbol to value mapping
abbrev Valuation := List (Sym × HeapValue)
```

### CN/Semantics/Interpretation.lean

```lean
-- Interpret Owned resource
def interpOwned (ct : Ctype) (loc : Location) (initState : Init) (v : HeapValue)
    (h : HeapFragment) : Prop :=
  h = HeapFragment.singleton loc v ∧
  match initState with
  | .init => valueMatchesType ct v
  | .uninit => True

-- Interpret resource list (with implicit separation)
def interpResources (rs : List Resource) (ρ : Valuation) (h : HeapFragment) : Prop
```

### Verification/SmtDemo.lean

Shows SMT integration:
```lean
-- SMT can prove universal properties
theorem int_add_comm (x y : Int) : x + y = y + x := by smt

-- With hypotheses
theorem pos_sum (x y : Int) (hx : x > 0) (hy : y > 0) : x + y > 0 := by
  smt [hx, hy]
```

## New Components

### IndexTerm Denotation

Interpret CN terms as values:

```lean
-- Extend HeapValue or create unified Value type
-- For now, work with existing HeapValue

-- Denotation function
def IndexTerm.denote (ρ : Valuation) : IndexTerm → Option HeapValue
  | ⟨.const (.z n), _, _⟩ => some (.integer defaultIntType n)
  | ⟨.const (.bool b), _, _⟩ =>
      some (.integer defaultIntType (if b then 1 else 0))
  | ⟨.sym s, _, _⟩ => ρ.lookup s
  | ⟨.binop .add t1 t2, _, _⟩ => do
      let .integer ty1 n1 ← t1.denote ρ | none
      let .integer ty2 n2 ← t2.denote ρ | none
      some (.integer ty1 (n1 + n2))
  | ⟨.binop .lt t1 t2, _, _⟩ => do
      let .integer _ n1 ← t1.denote ρ | none
      let .integer _ n2 ← t2.denote ρ | none
      some (.integer defaultIntType (if n1 < n2 then 1 else 0))
  -- ... etc
  | _ => none
```

### Logical Constraints as Props

```lean
def LogicalConstraint.toProp (ρ : Valuation) : LogicalConstraint → Prop
  | .t term =>
      term.denote ρ = some (.integer defaultIntType 1)  -- true = 1
  | .forall_ (x, bt) body =>
      ∀ v : HeapValue,
        hasBaseType v bt →
        body.denote (ρ.bind x v) = some (.integer defaultIntType 1)
```

### Proof Obligation Type

```lean
/-- A proof obligation produced by type checking -/
structure Obligation where
  /-- Human-readable description -/
  description : String
  /-- The proposition to prove -/
  prop : Prop
  /-- Source location for error reporting -/
  loc : Core.Loc
  /-- Category for choosing discharge strategy -/
  category : ObligationCategory

/-- Categories help choose discharge strategies -/
inductive ObligationCategory where
  | arithmetic      -- Use omega or smt
  | equality        -- Use rfl, simp, or smt
  | resourceMatch   -- Use frame_derived and resource lemmas
  | custom          -- Needs manual proof or specialized tactic
```

### Type Check Result

```lean
structure TypeCheckResult where
  /-- Did structural type checking succeed? -/
  success : Bool
  /-- Proof obligations to discharge -/
  obligations : List Obligation
  /-- Final typing context (for debugging) -/
  finalContext : Context
  /-- Error message if success = false -/
  error : Option TypeError

/-- All obligations as a single Prop -/
def TypeCheckResult.allObligations (r : TypeCheckResult) : Prop :=
  ∀ ob ∈ r.obligations, ob.prop
```

## Soundness Theorem Structure

```lean
/-- Main soundness theorem (to be proven)

If:
1. Type checking succeeds
2. All proof obligations are discharged

Then:
- The program has no undefined behavior when run in the interpreter
-/
theorem cn_soundness
    (prog : Core.AExpr)
    (spec : FunctionSpec)
    (result : TypeCheckResult)
    (h_tc : typeCheckFunction prog spec = result)
    (h_success : result.success = true)
    (h_obligations : result.allObligations)
    : ¬ hasUndefinedBehavior (interpret prog)
```

This connects:
1. **CN type checking** (syntactic, resource tracking)
2. **Proof obligations** (semantic, about values and heaps)
3. **Interpreter** (operational, actual execution)

## Discharge Strategies

### 1. SMT Solver (via `smt` tactic)

Best for:
- Linear arithmetic
- Boolean combinations
- Pointer equality/disequality
- Quantifier-free formulas

```lean
example (x y : Int) (hx : x > 0) (hy : y > 0) : x + y > 0 := by
  smt [hx, hy]
```

### 2. Omega Tactic

Best for:
- Linear integer arithmetic
- Faster than SMT for simple cases

```lean
example (x : Int) (h : x ≥ 0) : x + 1 > 0 := by omega
```

### 3. Resource Lemmas

For heap-related obligations, use existing lemmas:

```lean
-- Use frame_derived for resource composition
example (rs1 rs2 : List Resource) ... :
    interpResources (rs1 ++ rs2) ρ (h1 ++ h2) := by
  exact frame_derived rs1 rs2 ρ h1 h2 hDisj h1Sat h2Sat
```

### 4. Inductive Lemmas (Future)

For data structure properties (lists, trees):

```lean
-- Hand-proven lemma
theorem lseg_append : lseg x y → lseg y z → lseg x z := by
  intro hxy hyz
  induction hxy <;> simp [*]
```

### 5. Combined Tactic

```lean
/-- Try multiple strategies -/
macro "cn_discharge" : tactic =>
  `(tactic| first
    | rfl
    | decide
    | omega
    | smt [*]
    | (apply frame_derived; assumption)
    | assumption
  )
```

## Implementation Plan

### Phase 1: Denotation Functions

**File: `CN/Semantics/Denote.lean`** (new)

1. `IndexTerm.denote : Valuation → IndexTerm → Option HeapValue`
2. `LogicalConstraint.toProp : Valuation → LogicalConstraint → Prop`
3. Basic lemmas about denotation

### Phase 2: Obligation Infrastructure

**File: `CN/Verification/Obligation.lean`** (new)

1. `Obligation` structure
2. `ObligationCategory` enum
3. `TypeCheckResult` with obligations

### Phase 3: Update Type Checker

**File: `CN/TypeChecking/Monad.lean`** (modify)

1. Remove `ProofOracle` (or repurpose as discharge strategy selector)
2. Add obligation accumulation to `TypingState`
3. Replace `ensureProvable` with `addObligation`

**File: `CN/TypeChecking/Check.lean`** (modify)

1. Update to produce `TypeCheckResult` with obligations
2. Constraints become obligations, not inline checks

### Phase 4: Discharge Tactics

**File: `CN/Verification/Discharge.lean`** (new)

1. `cn_discharge` tactic
2. Strategy selection based on `ObligationCategory`
3. Integration with `smt`, `omega`

### Phase 5: Testing

1. Update existing tests to check obligation generation
2. Verify obligations can be discharged
3. Test `026-constraint-violation.fail.c` with real SMT

### Phase 6: Soundness Proof Structure

**File: `CN/Verification/Soundness.lean`** (new)

1. Statement of `cn_soundness`
2. Helper lemmas connecting:
   - Type checking validity
   - Obligation semantics
   - Interpreter behavior

## Example: Complete Verification

```lean
-- C function:
-- int read(int *p) { return *p; }
--
-- CN spec:
-- requires take v = Owned<int>(p);
-- ensures take v2 = Owned<int>(p); v == v2; return == v;

def readSpec : FunctionSpec := ...
def readBody : Core.AExpr := ...

-- Type check produces obligations
def readResult : TypeCheckResult := typeCheckFunction readBody readSpec

-- Verify type checking succeeded
example : readResult.success = true := rfl

-- Discharge all obligations
theorem read_obligations : readResult.allObligations := by
  unfold TypeCheckResult.allObligations
  intro ob h_mem
  fin_cases h_mem
  -- Each obligation discharged by appropriate strategy
  all_goals cn_discharge

-- Final safety theorem
theorem read_safe : ¬ hasUndefinedBehavior (interpret readBody) :=
  cn_soundness readBody readSpec readResult rfl rfl read_obligations
```

## Migration from Current Design

### Current: ProofOracle

```lean
structure ProofOracle where
  tryProve : LCSet → LogicalConstraint → ProvableResult

def ProofOracle.trivial : ProofOracle where
  tryProve _ _ := .true_  -- Accepts everything (unsound!)
```

### New: Obligation Accumulation

```lean
-- In TypingState
structure TypingState where
  context : Context
  obligations : List Obligation  -- Accumulated obligations
  freshCounter : Nat
  -- No more oracle!

-- In type checking
def addConstraintObligation (lc : LogicalConstraint) (loc : Loc) : TypingM Unit := do
  let ρ ← getCurrentValuation
  let ob : Obligation := {
    description := s!"Constraint at {loc}"
    prop := lc.toProp ρ
    loc := loc
    category := .arithmetic
  }
  modify fun s => { s with obligations := ob :: s.obligations }
```

## Open Questions

1. **HeapValue vs Value**: Should we unify `HeapValue` (from Semantics) with a new `Value` type, or just extend `HeapValue`?

2. **Valuation vs Env**: The existing `Valuation` uses `HeapValue`. Should we keep this or create a more abstract `Env`?

3. **Quantified constraints**: How to handle `each` (bounded quantification) - unroll finitely or use SMT quantifiers?

4. **User predicates**: How to handle user-defined CN predicates that need custom lemmas?

5. **Incremental checking**: Can we cache/reuse proofs when specs change slightly?

## References

- CN Paper: "CN: Verifying Systems C Code with Separation-Logic Refinement Types"
- Existing code: `CN/Semantics/*.lean`, `Verification/SmtDemo.lean`
- lean-smt: https://github.com/ufmg-smite/lean-smt
- Aristotle: Used to prove `frame_derived` theorem
