# CN Foundational Soundness Proof Plan

## Goal

Create a foundational proof architecture where for any C program:
1. With an AST representation embedded in Lean
2. Where the CN type checker succeeds
3. Where all proof obligations are discharged (by any means: SMT, omega, manual proofs)

We can prove a **foundational theorem** that the program satisfies its specification with respect to the interpreter semantics.

This is **translation validation**: we don't trust the type checker or SMT solver blindly - we produce Lean proofs that the kernel verifies.

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│ Soundness Theorem (proven once)                             │
│                                                             │
│ theorem cn_soundness :                                      │
│   ∀ (prog : AExpr) (spec : FunctionSpec) (obligations),     │
│     typeCheck prog spec = ok obligations →                  │
│     (∀ ob ∈ obligations, ob.toProp) →                       │
│     ∀ initialState, satisfiesPrecondition initialState →    │
│       ¬hasUB (interpret prog initialState) ∧                │
│       satisfiesPostcondition (interpret prog initialState)  │
└─────────────────────────────────────────────────────────────┘
                           │
                           │ instantiate with concrete program
                           ▼
┌─────────────────────────────────────────────────────────────┐
│ Per-Program Verification                                    │
│                                                             │
│ def myProg : AExpr := ...                                   │
│ def mySpec : FunctionSpec := ...                            │
│                                                             │
│ -- Type check succeeds (computed)                           │
│ theorem tc_ok : typeCheck myProg mySpec = ok obs := by      │
│   native_decide                                             │
│                                                             │
│ -- Obligations discharged (various tactics)                 │
│ theorem ob0 : obs[0].toProp := by omega                     │
│ theorem ob1 : obs[1].toProp := by smt [*]                   │
│ theorem ob2 : obs[2].toProp := by exact my_lemma            │
│                                                             │
│ -- Instantiate soundness → foundational safety proof        │
│ theorem myProg_safe := cn_soundness myProg mySpec obs tc_ok │
│                          ⟨ob0, ob1, ob2⟩                    │
└─────────────────────────────────────────────────────────────┘
```

## What We Already Have

| Component | File | Status |
|-----------|------|--------|
| Type checker | `CN/TypeChecking/Check.lean` | ✓ Works |
| Obligation structure | `CN/Verification/Obligation.lean` | ✓ Has `toProp` |
| Denotation functions | `CN/Semantics/Denote.lean` | ✓ `constraintToProp`, `denoteTerm` |
| Discharge tactics | `CN/Verification/Discharge.lean` | ✓ `cn_discharge` tries multiple |
| lean-smt | `lakefile.toml` | ✓ Integrated |
| Interpreter | `Semantics/Interpreter.lean` | ✓ `runMain` |
| Resource semantics | `CN/Semantics/Interpretation.lean` | ✓ `interpResources` |

## What's Missing

### 1. Relational Execution Semantics

The interpreter is currently imperative (`runMain : AFile → InterpResult`). For soundness proofs, we need a **relational view** that we can reason about.

**File**: `Semantics/Execution.lean` (new)

```lean
/-- Single-step relation -/
inductive StepRel : ThreadState → MemState → ThreadState → MemState → Prop

/-- Multi-step closure -/
inductive StepsStar : ThreadState → MemState → ThreadState → MemState → Prop

/-- Terminal (successful completion) -/
def isTerminal (st : ThreadState) : Prop

/-- Error (UB detected) -/
def isError (st : ThreadState) (mem : MemState) : Prop
```

### 2. Memory Correspondence

Connect CN's `HeapFragment` (separation logic) to interpreter's `MemState` (concrete memory).

**File**: `CN/Semantics/MemCorrespondence.lean` (new)

```lean
/-- Convert concrete memory to abstract heap -/
def memStateToHeapFragment (mem : MemState) : HeapFragment

/-- Ownership implies valid allocation -/
theorem owned_implies_valid : ...
```

### 3. Simulation Relation

Relate type checker state to interpreter state.

**File**: `CN/Verification/Soundness.lean` (new)

```lean
/-- Type checker context simulates interpreter state -/
def simulationRelation
    (ctx : Context)        -- Type checker's view
    (mem : MemState)       -- Interpreter's memory
    (rho : Valuation)      -- Symbol → Value mapping
    : Prop :=
  -- Resources correspond to memory contents
  -- Constraints are satisfied
  -- Variable bindings match
```

### 4. Soundness Theorem

The main metatheorem connecting type checking to execution safety.

```lean
theorem cn_soundness
    (prog : AExpr)
    (spec : FunctionSpec)
    (obligations : ObligationSet)
    (h_tc : typeCheck prog spec = ok obligations)
    (h_obs : ∀ ob ∈ obligations, ob.toProp)
    : ∀ initialState,
        satisfiesPrecondition spec initialState →
        let result := interpret prog initialState
        result.error = none ∧
        satisfiesPostcondition spec result
```

## Obligation Discharge Strategy

Obligations can be discharged by **any means** that produces a Lean proof:

| Obligation Category | Preferred Tactics |
|---------------------|-------------------|
| Arithmetic (bounds, overflow) | `omega`, `linarith`, `smt [*]` |
| Equality | `rfl`, `simp`, `decide` |
| Resource matching | `frame_derived`, manual proofs |
| Pointer validity | Custom lemmas |
| Complex/custom | Hand-written proofs |

The `cn_discharge` tactic tries multiple approaches automatically:
```lean
macro "cn_discharge" : tactic =>
  `(tactic| first
    | trivial | rfl | decide | assumption
    | simp [*] | omega
    | smt [*])
```

## Obligation.toProp Structure

```lean
def Obligation.toProp (ob : Obligation) : Prop :=
  ∀ ρ : Valuation,
    constraintSetToProp ρ ob.assumptions →
    constraintToProp ρ ob.constraint
```

This is a universally quantified implication - exactly what SMT/omega can handle after unfolding.

## Implementation Phases

### Phase 1: Enhance Discharge Tactics
- Add `cn_unfold` to properly unfold `Obligation.toProp`
- Ensure `smt [*]` receives goals in digestible form
- Test on existing CN test suite

**Files**: `CN/Verification/Discharge.lean`

### Phase 2: Relational Execution
- Define `StepRel` inductive type
- Define `StepsStar` (reflexive transitive closure)
- Prove basic properties

**Files**: `Semantics/Execution.lean` (new)

### Phase 3: Memory Correspondence
- Define `memStateToHeapFragment`
- Prove correspondence lemmas
- Connect to `interpResources`

**Files**: `CN/Semantics/MemCorrespondence.lean` (new)

### Phase 4: Simulation & Soundness
- Define `simulationRelation`
- Prove operation lemmas (store/load/create/kill preserve simulation)
- State and prove `cn_soundness`

**Files**: `CN/Verification/Soundness.lean` (new)

## Key Design Principles

1. **No serialization gap**: `denote` functions are formal Lean definitions, not string serialization
2. **Discharge-method agnostic**: Soundness theorem requires `ob.toProp` proofs, doesn't care how obtained
3. **Kernel-verified**: All proofs checked by Lean's kernel, no trusted external tools
4. **Incremental**: Can verify programs before full soundness proof is complete (trust obligations)

## Files to Modify/Create

| File | Action | Purpose |
|------|--------|---------|
| `CN/Verification/Discharge.lean` | Enhance | Better unfolding for SMT |
| `Semantics/Execution.lean` | Create | Relational execution semantics |
| `CN/Semantics/MemCorrespondence.lean` | Create | HeapFragment ↔ MemState |
| `CN/Verification/Soundness.lean` | Create | Simulation + soundness theorem |

## Success Criteria

1. Can discharge typical CN obligations using `cn_discharge` or specific tactics
2. Soundness theorem stated (even if `sorry`'d initially)
3. At least one simple program verified end-to-end with foundational proof
4. Clear path to completing soundness proof

## Open Questions

1. **Valuation representation**: Current `Valuation = List (Sym × HeapValue)` may not be SMT-friendly. May need alternative representation for discharge.

2. **Partial functions**: `denoteTerm` returns `Option HeapValue`. Need to handle `none` cases cleanly in proofs.

3. **Quantifier handling**: `∀ ρ : Valuation` is infinite. SMT handles via instantiation, but may need hints.

## Key Finding: `denoteTerm` is Partial

**Discovery during Phase 1 implementation (2026-01-22):**

The function `denoteTerm` is declared `partial` because it's recursive on deeply nested terms. This has important consequences:

1. `simp` cannot unfold `denoteTerm`
2. `native_decide` cannot evaluate expressions involving `denoteTerm`
3. `decide` requires the goal to be a closed decidable term

### Approaches That Work

1. **Assumption-based proofs**: When the constraint matches an assumption, we can use the assumption directly without evaluating `denoteTerm`. Example proof:
   ```lean
   theorem obWithAssumption_holds : obWithAssumption.toProp := by
     unfold Obligation.toProp constraintSetToProp
     intro ρ h_assumptions
     exact h_assumptions _ (List.mem_singleton.mpr rfl)
   ```

2. **Manual lemmas**: For specific concrete terms, we can write lemmas that expand the definition manually.

### What Needs More Work

For automatic discharge with `native_decide` or SMT, we would need:
- **Option A**: Make `denoteTerm` terminating (well-founded recursion)
- **Option B**: Use reflection/metaprogramming to generate proofs
- **Option C**: Create an SMT-friendly representation that doesn't go through `denoteTerm`

### Practical Impact

For the soundness proof:
- **Identity obligations** (constraint = assumption): Work now via `assumption` tactic
- **Derivable obligations** (constraint follows from assumptions): Need manual proofs or enhanced infrastructure

The test module `CerbLean/CN/Verification/DischargeTest.lean` documents these findings with working examples.
