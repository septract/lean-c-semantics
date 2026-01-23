/-
  CN Verification Pipeline Demo

  This module demonstrates the complete verification pipeline:
  1. Define a program AST and CN specification
  2. Run the type checker to get obligations
  3. Prove all obligations
  4. (Future) Instantiate soundness theorem

  We start with the simplest possible examples to show the pipeline
  is structurally correct from a type perspective.
-/

import CerbLean.CN.TypeChecking
import CerbLean.CN.Verification.Obligation
import CerbLean.CN.Verification.Discharge
import CerbLean.CN.Types
import CerbLean.CN.Semantics.Denote
import CerbLean.CN.Semantics.PureDenoteSound

namespace CerbLean.CN.Verification.PipelineDemo

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types
open CerbLean.CN.TypeChecking
open CerbLean.CN.Verification
open CerbLean.CN.Semantics

/-! ## Example 1: Spec-Only Checking (No Program)

These examples use `checkSpecStandalone` which only checks the spec structure
in isolation, without an actual Core program. This is useful for testing the
type checker infrastructure.

**Important**: When checking a real program with `checkFunction`, even trusted
specs generate UB-related obligations from:
- Memory operations (valid pointers, no use-after-free)
- Arithmetic (no overflow, no division by zero)
- Array accesses (bounds checking)

The `trusted` flag only means we trust the functional spec annotations -
we still verify the program is UB-free.
-/

/-- A trusted function specification (spec-only, no program).
    With an actual program, this would still generate UB obligations. -/
def trustedSpec : FunctionSpec :=
  { requires := { clauses := [] }
  , ensures := { clauses := [] }
  , trusted := true
  }

/-- Type check result for trusted spec -/
def trustedResult : TypeCheckResult :=
  checkSpecStandalone trustedSpec

-- Verify type checking succeeds
#eval trustedResult.success  -- true

-- Verify no obligations
#eval trustedResult.obligations.length  -- 0

/-- Type checking succeeds for trusted spec -/
theorem trusted_tc_success : trustedResult.success = true := by
  native_decide

/-- All obligations satisfied (vacuously true - no obligations from spec-only check).
    Note: With an actual program, checkFunction would generate UB obligations. -/
theorem trusted_obs_satisfied : trustedResult.obligations.allSatisfied := by
  -- trustedResult.obligations is [], so this is vacuously true
  -- (checkSpecStandalone only checks spec structure, not program execution)
  intro ob h_mem
  -- For spec-only checking, obligations = []
  simp only [trustedResult, checkSpecStandalone, checkFunctionSpec, trustedSpec,
             TypeCheckResult.ok] at h_mem
  -- h_mem : ob ∈ [] which is false
  contradiction

/-! ## Example 2: Empty Spec (No Obligations)

An empty (non-trusted) spec also has no obligations.
-/

/-- Empty function specification -/
def emptySpec : FunctionSpec :=
  { requires := { clauses := [] }
  , ensures := { clauses := [] }
  , trusted := false
  }

def emptyResult : TypeCheckResult :=
  checkSpecStandalone emptySpec

#eval emptyResult.success  -- true
#eval emptyResult.obligations.length  -- 0

theorem empty_tc_success : emptyResult.success = true := by
  native_decide

theorem empty_obs_satisfied : emptyResult.obligations.allSatisfied := by
  intro ob h_mem
  -- Need to show the obligation list is empty after running type checker
  simp only [emptyResult, checkSpecStandalone, checkFunctionSpec, emptySpec] at h_mem
  -- After unfolding, we should see obligations = []
  simp only [TypingM.run, processPrecondition, processPostcondition] at h_mem
  -- The computation returns ok with empty obligations
  sorry  -- TODO: need to trace through Except.ok to see obligations = []

/-! ## Example 3: Precondition Only (No Obligations)

Precondition constraints are assumptions, not obligations.
-/

/-- Helper to create a symbol -/
def mkSym (id : Nat) (name : String) : Sym := { id := id, name := some name }

/-- Helper to create an integer constant term -/
def mkIntConst (n : Int) : IndexTerm :=
  ⟨.const (.z n), .integer, Loc.t.unknown⟩

/-- Helper to create a symbol term -/
def mkSymTerm (s : Sym) : IndexTerm :=
  ⟨.sym s, .integer, Loc.t.unknown⟩

/-- Helper to create a binary operation -/
def mkBinOp (op : BinOp) (left right : IndexTerm) : IndexTerm :=
  ⟨.binop op left right, .bool, Loc.t.unknown⟩

def xSym : Sym := mkSym 1 "x"

/-- Spec with precondition constraint: requires x > 0 -/
def preOnlySpec : FunctionSpec :=
  { requires := { clauses := [.constraint (mkBinOp .lt (mkIntConst 0) (mkSymTerm xSym))] }
  , ensures := { clauses := [] }
  , trusted := false
  }

def preOnlyResult : TypeCheckResult :=
  checkSpecStandalone preOnlySpec

#eval preOnlyResult.success  -- true
#eval preOnlyResult.obligations.length  -- 0 (preconditions are assumptions)

theorem preOnly_tc_success : preOnlyResult.success = true := by
  native_decide

theorem preOnly_obs_satisfied : preOnlyResult.obligations.allSatisfied := by
  intro ob h_mem
  -- Precondition constraints don't generate obligations
  sorry  -- TODO: trace through to show obligations = []

/-! ## Example 4: Postcondition Constraint (One Obligation)

This is the interesting case - postcondition constraints become obligations.
We'll construct the same constraint that the type checker generates and prove it.
-/

/-- The constraint: 0 < x (i.e., x > 0) -/
def xPositiveConstraint : LogicalConstraint :=
  .t (mkBinOp .lt (mkIntConst 0) (mkSymTerm xSym))

/-- Spec with postcondition constraint: requires x > 0; ensures x > 0
    The postcondition should be provable from the precondition. -/
def simplePostSpec : FunctionSpec :=
  { requires := { clauses := [.constraint (mkBinOp .lt (mkIntConst 0) (mkSymTerm xSym))] }
  , ensures := { clauses := [.constraint (mkBinOp .lt (mkIntConst 0) (mkSymTerm xSym))] }
  , trusted := false
  }

def simplePostResult : TypeCheckResult :=
  checkSpecStandalone simplePostSpec

#eval simplePostResult.success  -- true
#eval simplePostResult.obligations.length  -- 1

theorem simplePost_tc_success : simplePostResult.success = true := by
  native_decide

/-- Verify we get exactly 1 obligation -/
theorem simplePost_one_obligation : simplePostResult.obligations.length = 1 := by
  native_decide

/-- The manually constructed obligation that matches what the type checker generates.
    Obligation: given assumption (x > 0), prove (x > 0).
    This is trivially true - the constraint equals an assumption. -/
def expectedObligation : Obligation :=
  { description := "x > 0 → x > 0"
  , constraint := xPositiveConstraint
  , assumptions := [xPositiveConstraint]  -- The precondition becomes an assumption
  , loc := Loc.t.unknown
  , category := .arithmetic
  }

/-- Prove the expected obligation using the same technique as Test/Discharge.lean.
    Since the constraint equals an assumption, we just need to extract it. -/
theorem expectedObligation_holds : expectedObligation.toProp := by
  unfold Obligation.toProp expectedObligation
  intro ρ h_assumptions
  -- h_assumptions : constraintSetToProp ρ [xPositiveConstraint]
  -- goal : constraintToProp ρ xPositiveConstraint
  -- The constraint IS one of the assumptions, so we can extract it directly
  unfold constraintSetToProp at h_assumptions
  -- h_assumptions says: ∀ lc ∈ [xPositiveConstraint], constraintToProp ρ lc
  exact h_assumptions xPositiveConstraint (List.mem_singleton.mpr rfl)

/-- Helper: if a constraint is in the assumptions, the obligation holds -/
theorem obligation_holds_if_constraint_in_assumptions
    (ob : Obligation)
    (h : ob.constraint ∈ ob.assumptions) : ob.toProp := by
  unfold Obligation.toProp
  intro ρ h_assumptions
  unfold constraintSetToProp at h_assumptions
  exact h_assumptions ob.constraint h

/-- The key theorem: all obligations are satisfied.

    For this simple case where the postcondition constraint equals the
    precondition constraint, the obligation is trivially satisfied:
    the constraint is literally one of the assumptions.

    The generated obligation has:
    - constraint = xPositiveConstraint (0 < x)
    - assumptions = [xPositiveConstraint] (the precondition)

    We prove this by showing the constraint is in the assumptions.
-/
theorem simplePost_obs_satisfied : simplePostResult.obligations.allSatisfied := by
  intro ob h_mem
  -- Use the helper lemma: show constraint ∈ assumptions
  apply obligation_holds_if_constraint_in_assumptions
  -- Now we need to show: ob.constraint ∈ ob.assumptions
  -- This requires knowing what 'ob' is from the type checker output.
  --
  -- The type checker generates an obligation where:
  -- - constraint = the postcondition constraint (x > 0)
  -- - assumptions = the precondition constraints [x > 0]
  --
  -- Since they're the same, the constraint is in the assumptions.
  -- However, proving this requires either:
  -- 1. Tracing through the monad computation (complex)
  -- 2. Decidable equality on LogicalConstraint (we need BEq instance)
  -- 3. Reflection to compare the terms

  -- For now, we demonstrate the pipeline structure is correct
  -- and leave the computational extraction as future work.
  sorry

/-- Alternative proof using the same technique as Test/Discharge.lean.

    This shows that IF we had the obligation structure explicitly,
    the proof would work. The challenge is extracting this from
    the type checker output.
-/
theorem expected_obligation_proof : expectedObligation.toProp := by
  apply obligation_holds_if_constraint_in_assumptions
  -- expectedObligation.constraint = xPositiveConstraint
  -- expectedObligation.assumptions = [xPositiveConstraint]
  simp only [expectedObligation, xPositiveConstraint]
  exact List.mem_singleton.mpr rfl

/-! ## Soundness Theorem Sketch

The soundness theorem connects:
- Type checking success
- Obligation discharge
- Program EXECUTION (via interpreter)
- Specification satisfaction

The key insight: type checking + obligation discharge guarantees that
EXECUTING the program takes you from a precondition-satisfying state
to a postcondition-satisfying state, without undefined behavior.
-/

-- Note: The actual soundness theorem would reference the interpreter
-- (CerbLean.Semantics.Interpreter.runMain) but we use placeholders here.

/-- Placeholder: state satisfies precondition resources and constraints -/
def satisfiesPrecondition (_spec : FunctionSpec) (_mem : Unit) : Prop := True

/-- Placeholder: result satisfies postcondition resources and constraints -/
def satisfiesPostcondition (_spec : FunctionSpec) (_result : Unit) : Prop := True

/-- The CN Soundness Theorem (CORRECT VERSION)

    Given:
    1. A Core program (prog : AExpr)
    2. A CN specification (spec : FunctionSpec)
    3. Type checking the program against the spec succeeds
    4. All generated proof obligations are satisfied

    Then:
    For any initial memory state satisfying the precondition:
    - Executing the program does not cause undefined behavior
    - The final state satisfies the postcondition

    This is the key metatheorem connecting:
    - Syntactic analysis (type checker)
    - Semantic execution (interpreter)
    - Specification satisfaction (pre/post conditions)

    Note: The actual theorem would use:
    - interpret : AExpr → MemState → InterpResult
    - InterpResult.error = none (no UB)
    - Resource interpretation for pre/post conditions
-/
theorem cn_soundness
    (prog : Core.AExpr)      -- The Core program to verify
    (spec : FunctionSpec)    -- The CN specification
    (loc : Loc)
    (h_tc : (checkFunction spec prog loc).success = true)
    (h_obs : (checkFunction spec prog loc).obligations.allSatisfied)
    : ∀ initialMem,
        satisfiesPrecondition spec initialMem →
        -- Execute the program and check the result
        -- (Using placeholder types for now - real version uses interpreter)
        satisfiesPostcondition spec () := by
  sorry  -- FUTURE WORK: Prove by induction on program structure

/-! ## Example 5: Actual Core Program (No-op)

This is the key example: an actual Core program with the full pipeline.
A no-op program that returns unit - the simplest possible program.
-/

/-- A no-op Core program: just returns unit.
    Equivalent to C function: void f() { } -/
def noopProgram : Core.AExpr :=
  { annots := []
  , expr := .pure
      { annots := []
      , ty := some .unit
      , expr := .val .unit
      }
  }

/-- Empty spec for the no-op program -/
def noopSpec : FunctionSpec :=
  { requires := { clauses := [] }
  , ensures := { clauses := [] }
  , trusted := false
  }

/-- Run the type checker on the actual program -/
def noopResult : TypeCheckResult :=
  checkFunction noopSpec noopProgram Loc.t.unknown

-- Check what happens
#eval noopResult.success
#eval noopResult.obligations.length
#eval noopResult.error

/-- Type checking the no-op program succeeds -/
theorem noop_tc_success : noopResult.success = true := by
  native_decide

/-- How many obligations does the no-op program generate? -/
theorem noop_obligation_count : noopResult.obligations.length = 0 := by
  native_decide

/-- All obligations satisfied for the no-op program.
    cn_discharge_all_for handles both empty and non-empty obligation lists:
    - Empty list: derives contradiction from h_mem : ob ∈ []
    - Non-empty list: proves each ob.toProp using cn_discharge -/
theorem noop_obs_satisfied : noopResult.obligations.allSatisfied := by
  cn_discharge_all_for noopResult.obligations

/-! ## What a Real Verification Looks Like

For a concrete program, the verification would be:

```lean
-- 1. The Core AST (parsed from C via Cerberus)
def myProgram : Core.AExpr := ...

-- 2. The CN specification (parsed from annotations)
def mySpec : FunctionSpec := ...

-- 3. Type checking succeeds (computed, proved by native_decide)
theorem myProgram_tc : (checkFunction mySpec myProgram .unknown).success = true := by
  native_decide

-- 4. All obligations proved (using cn_discharge, SMT, manual proofs)
theorem myProgram_obs : (checkFunction mySpec myProgram .unknown).obligations.allSatisfied := by
  intro ob h_mem
  cn_discharge  -- or specific proofs for each obligation

-- 5. Instantiate soundness to get the semantic guarantee
theorem myProgram_correct :
    ∀ initialMem, satisfiesPrecondition mySpec initialMem →
    satisfiesPostcondition mySpec () :=
  cn_soundness myProgram mySpec .unknown myProgram_tc myProgram_obs
```

The power: Once cn_soundness is proved, verifying a new program just requires:
1. Showing type checking succeeds (decidable)
2. Proving the generated obligations (automatic for arithmetic via SMT)
-/

/-! ## Summary

This module demonstrates the verification pipeline structure:

1. **Define**: FunctionSpec (CN annotations)
2. **Type Check**: checkSpecStandalone → TypeCheckResult
3. **Prove TC Success**: native_decide (decidable computation)
4. **Prove Obligations**: cn_discharge, SMT, or manual proofs
5. **Instantiate Soundness**: Get semantic correctness theorem

The pipeline is structurally sound. What remains:
- Prove the soundness theorem (cn_soundness)
- Make cn_discharge robust for real obligations
- Add support for function bodies (not just spec-only checking)
-/

end CerbLean.CN.Verification.PipelineDemo
