# Generic Obligation Discharge Plan

Date: 2026-01-23

## Goal

Create a **GENERIC tactic** that discharges ANY list of obligations from ANY program:

```lean
theorem myProgram_obs : (checkFunction mySpec myProgram loc).obligations.allSatisfied := by
  cn_discharge_all  -- Works for ANY program, not specialized
```

## The Problem

Current `Obligation.toProp`:
```lean
def Obligation.toProp (ob : Obligation) : Prop :=
  ∀ ρ : Valuation,  -- Valuation = List (Sym × HeapValue)
    constraintSetToProp ρ ob.assumptions →
    constraintToProp ρ ob.constraint
```

**Why SMT can't handle this:**
- `Valuation = List (Sym × HeapValue)` - SMT doesn't understand HeapValue
- Universal quantifier over a complex type

**Previous failed approaches:**
- Introducing `ob` via `intro ob h_mem` creates an abstract variable
- Case-splitting on list membership requires knowing list length (program-specific)

## Solution: Pure Interpretation + Computed Conjunction

### Key Insight 1: Pure Interpretation Layer

We have `PureIntVal = Sym → Int` in PureDenote.lean. For arithmetic constraints, SMT CAN prove:
```lean
∀ σ : (Sym → Int), pure_assumptions σ → pure_constraint σ
```

### Key Insight 2: Compute the Conjunction, Don't Introduce Variables

Instead of:
```lean
intro ob h_mem  -- Creates abstract ob
```

Use simp to COMPUTE:
```lean
simp only [allSatisfied_cons, allSatisfied_nil]
-- For [ob1, ob2]: becomes ob1.toProp ∧ ob2.toProp ∧ True
```

This gives us CONCRETE obligation terms, not abstract variables.

### Architecture

```
allSatisfied [ob1, ob2]
       ↓ (simp with cons/nil lemmas)
ob1.toProp ∧ ob2.toProp ∧ True
       ↓ (split conjunction)
Goal 1: ob1.toProp  |  Goal 2: ob2.toProp
       ↓ (apply soundness)
Goal 1: ob1.pureToProp  |  Goal 2: ob2.pureToProp
       ↓ (concrete ob, reduces to pure arithmetic)
∀ σ, (0 < σ x) → (0 < σ x)  (SMT proves)
```

## Implementation Steps

### Step 1: Add `Obligation.pureToProp` to Obligation.lean

```lean
import CerbLean.CN.Semantics.PureDenote

def pureToProp (ob : Obligation) : Prop :=
  ∀ σ : PureIntVal,
    (match constraintSetToPureProp σ ob.assumptions with
     | some P => P
     | none => True) →
    (match constraintToPureProp σ ob.constraint with
     | some Q => Q
     | none => True)
```

### Step 2: Add Soundness Theorem to PureDenoteSound.lean

```lean
theorem Obligation.toProp_of_pureToProp (ob : Obligation)
    (h_pure : ob.pureToProp) : ob.toProp := by
  intro ρ h_assumptions
  let σ := extractPureVal ρ
  have h_compat := extractPureVal_compatible ρ
  sorry  -- Uses existing soundness infrastructure
```

### Step 3: Add allSatisfied rewriting lemmas

```lean
theorem allSatisfied_nil : ([] : ObligationSet).allSatisfied := by
  intro ob h; contradiction

theorem allSatisfied_cons (ob : Obligation) (obs : ObligationSet) :
    (ob :: obs).allSatisfied ↔ ob.toProp ∧ obs.allSatisfied := by
  simp only [ObligationSet.allSatisfied, List.mem_cons]
  constructor
  · intro h; exact ⟨h ob (Or.inl rfl), fun ob' h' => h ob' (Or.inr h')⟩
  · intro ⟨h1, h2⟩ ob' h'; rcases h' with rfl | h'; exact h1; exact h2 ob' h'
```

### Step 4: Rewrite cn_discharge_all

```lean
elab_rules : tactic
  | `(tactic| cn_discharge_all) => do
    -- Rewrite allSatisfied to conjunction (computes for any concrete list)
    evalTactic (← `(tactic| simp only [allSatisfied_cons, allSatisfied_nil]))
    -- Split conjunction into separate goals
    evalTactic (← `(tactic| repeat' (constructor <;> try trivial)))
    -- Each goal is ob.toProp for CONCRETE ob - apply soundness + SMT
    evalTactic (← `(tactic| all_goals (
      apply Obligation.toProp_of_pureToProp
      · intro σ h_assm; smt [h_assm])))
```

## Why This Works

1. `simp only [allSatisfied_cons, allSatisfied_nil]` COMPUTES for any concrete list
2. No abstract variable `ob` is introduced - we get concrete obligations directly
3. `repeat' constructor` splits any-length conjunction
4. Each goal has a CONCRETE `obi`, so `obi.pureToProp` reduces to pure arithmetic
5. SMT proves the pure arithmetic implication

## Files to Modify

| File | Changes |
|------|---------|
| `CN/Verification/Obligation.lean` | Add `pureToProp`, `allSatisfied_cons`, `allSatisfied_nil` |
| `CN/Semantics/PureDenoteSound.lean` | Add `toProp_of_pureToProp` theorem |
| `CN/Verification/Discharge.lean` | Rewrite `cn_discharge_all` |
| `CN/Verification/PipelineDemo.lean` | Test - remove sorry from `prePost_obs_satisfied` |
