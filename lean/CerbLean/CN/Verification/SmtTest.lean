/-
  Test file: Understanding the SMT blocker for computed obligation lists

  The goal: make this work generically:

  theorem myProgram_obs : (checkFunction mySpec myProgram loc).obligations.allSatisfied := by
    cn_discharge_all  -- Should work without knowing list length statically
-/

import CerbLean.CN.TypeChecking
import CerbLean.CN.Verification.Obligation
import CerbLean.CN.Verification.Discharge
import CerbLean.CN.Semantics.Denote
import Smt

namespace CerbLean.CN.Verification.SmtTest

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types
open CerbLean.CN.TypeChecking
open CerbLean.CN.Verification
open CerbLean.CN.Semantics

/-! ## Test 1: Literal list - this should work -/

def ob1 : Obligation :=
  { description := "test"
  , constraint := .t ⟨.const (.bool true), .bool, Loc.t.unknown⟩
  , assumptions := []
  , loc := Loc.t.unknown
  , category := .arithmetic
  }

-- Literal list: simp should reduce allSatisfied [ob1] to ob1.toProp ∧ True
#check ([ob1] : ObligationSet)

theorem literal_list_test : ([ob1] : ObligationSet).allSatisfied := by
  simp only [ObligationSet.allSatisfied_cons, ObligationSet.allSatisfied_nil]
  -- Goal should now be: ob1.toProp ∧ True
  constructor
  · -- ob1.toProp
    unfold Obligation.toProp ob1
    intro ρ h_assumptions
    -- Goal: constraintToProp ρ (.t ⟨.const (.bool true), .bool, _⟩)
    unfold constraintToProp
    simp only [denoteAnnotTerm, denoteTerm, denoteConst, heapValueIsTrue, boolToHeapValue]
    decide
  · trivial

/-! ## Test 2: Computed list from type checker -/

def mkSym (id : Nat) (name : String) : Sym := { id := id, name := some name }
def mkIntConst (n : Int) : IndexTerm := ⟨.const (.z n), .integer, Loc.t.unknown⟩
def mkSymTerm (s : Sym) : IndexTerm := ⟨.sym s, .integer, Loc.t.unknown⟩
def mkBinOp (op : BinOp) (left right : IndexTerm) : IndexTerm :=
  ⟨.binop op left right, .bool, Loc.t.unknown⟩

def xSym : Sym := mkSym 1 "x"

/-- Spec: requires x > 0; ensures x > 0 -/
def prePostSpec : FunctionSpec :=
  { requires := { clauses := [.constraint (mkBinOp .lt (mkIntConst 0) (mkSymTerm xSym))] }
  , ensures := { clauses := [.constraint (mkBinOp .lt (mkIntConst 0) (mkSymTerm xSym))] }
  , trusted := false
  }

/-- A no-op Core program -/
def noopProgram : Core.AExpr :=
  { annots := []
  , expr := .pure { annots := [], ty := some .unit, expr := .val .unit }
  }

/-- The computed result -/
def prePostResult : TypeCheckResult :=
  checkFunction prePostSpec noopProgram Loc.t.unknown

-- Verify we get 1 obligation
#eval prePostResult.obligations.length  -- Should be 1

/-! ## The Key Question: Can simp reduce allSatisfied for a COMPUTED list? -/

-- Let's see what happens when we try to simp
theorem computed_list_test : prePostResult.obligations.allSatisfied := by
  -- Try the simp approach
  simp only [ObligationSet.allSatisfied_cons, ObligationSet.allSatisfied_nil]
  -- What is the goal now? Let's see...
  sorry

-- Let's try with more aggressive unfolding
theorem computed_list_test2 : prePostResult.obligations.allSatisfied := by
  -- First unfold prePostResult to get the actual list
  unfold prePostResult checkFunction
  -- Now simp
  simp only [ObligationSet.allSatisfied_cons, ObligationSet.allSatisfied_nil]
  sorry

-- What if we use native_decide to compute the list first?
theorem computed_list_test3 : prePostResult.obligations.allSatisfied := by
  -- Can we use decide/native_decide to help?
  have h_len : prePostResult.obligations.length = 1 := by native_decide
  -- Now we know there's exactly 1 element, but the list is still opaque
  sorry

/-! ## Test: What does the goal look like after simp? -/

-- Use a tactic to show us the goal state
theorem show_goal_state : prePostResult.obligations.allSatisfied := by
  simp only [ObligationSet.allSatisfied_cons, ObligationSet.allSatisfied_nil]
  trace "{goal}"
  sorry

/-! ## The Real Question: Is the issue that simp doesn't compute through checkFunction? -/

-- Let's try forcing computation
theorem force_compute_test : prePostResult.obligations.allSatisfied := by
  -- native_decide can compute Bool, but allSatisfied is Prop...
  -- What if we had a decidable version?
  sorry

/-! ## Alternative: Reflect the obligations to a computed form -/

-- The issue might be that `prePostResult.obligations` doesn't reduce
-- Let's check if we can make it reduce

-- #reduce prePostResult.obligations.length  -- HITS MAX RECURSION
-- #reduce prePostResult.obligations  -- This might be too expensive

-- Check if the list head is accessible
#check (prePostResult.obligations.head?)

/-! ## KEY INSIGHT: The problem is that simp can't reduce through checkFunction

The type checker computation is too complex for the kernel to normalize.
We need a different approach.

Options:
1. Use `native_decide` somehow (but allSatisfied returns Prop, not Bool)
2. Provide a decidable instance for allSatisfied
3. Use reflection: prove a Bool version, then lift to Prop
4. Case split explicitly on the computed length
-/

/-! ## Approach: Decidable allSatisfied -/

-- First, we need Obligation.toProp to be decidable
-- But toProp is: ∀ ρ : Valuation, constraintSetToProp ρ assumptions → constraintToProp ρ constraint
-- This is NOT decidable in general (universal over infinite domain)

-- HOWEVER, for the special case where constraint ∈ assumptions, it IS trivially true
-- regardless of valuation. Can we detect this?

def Obligation.constraintInAssumptions (ob : Obligation) : Bool :=
  ob.assumptions.any (· == ob.constraint)

-- If constraint is in assumptions, the obligation trivially holds
theorem obligation_trivial_if_in_assumptions (ob : Obligation)
    (h : ob.constraint ∈ ob.assumptions) : ob.toProp := by
  intro ρ h_assm
  exact h_assm ob.constraint h

-- Now: can we use native_decide on the Bool check?
#eval prePostResult.obligations.all (·.constraintInAssumptions)  -- Should be true!

-- The strategy: if ALL obligations have constraint ∈ assumptions, we can prove it
theorem all_trivial_test : prePostResult.obligations.allSatisfied := by
  -- Step 1: Check that all obligations are trivial (constraint in assumptions)
  have h_all_trivial : prePostResult.obligations.all (·.constraintInAssumptions) = true := by
    native_decide
  -- Step 2: Now we need to convert this to allSatisfied
  -- This requires: List.all p = true → ∀ x ∈ list, p x = true
  -- And then: constraintInAssumptions = true → constraint ∈ assumptions
  sorry

/-! ## The Gap: We can COMPUTE that obligations are trivial, but can't PROVE it -/

-- The issue: even though native_decide confirms the Bool, we need to bridge to Prop
-- This requires:
-- 1. Decidable (ob.constraint ∈ ob.assumptions) - needs DecidableEq LogicalConstraint
-- 2. Or: a reflection principle

-- LogicalConstraint does NOT have DecidableEq (Term is mutually recursive, no BEq derived)
-- #check (inferInstance : DecidableEq LogicalConstraint)  -- FAILS

/-! ## PROPOSAL: The Evaluation-Based Approach

The key insight: We don't need DecidableEq on the SYMBOLIC constraint.
We need to evaluate the SEMANTIC meaning and check that.

For an obligation `ob`, we want to check:
  ∀ ρ : Valuation, constraintSetToProp ρ ob.assumptions → constraintToProp ρ ob.constraint

For the special case where constraint literally equals an assumption, this is trivially true.
But we can't check syntactic equality.

HOWEVER: We CAN evaluate both sides for a SPECIFIC valuation and compare!

The insight: If the type checker says "constraint should hold given assumptions",
and we can VERIFY this holds for the pure integer case, that's sufficient.

The plan:
1. Define `Obligation.checkPure : Bool` that checks the pure version is valid
2. Prove: `ob.checkPure = true → ob.pureToProp`
3. Use the soundness bridge: `ob.pureToProp → ob.toProp`
4. Chain them together with native_decide
-/

/-! ## Alternative: Explicit Obligation Extraction

Since the list doesn't reduce, but we CAN compute its length and access elements,
we can build the proof by:
1. Compute length with native_decide
2. For each index, extract the element and prove it
-/

-- Can we access elements by index?
#eval prePostResult.obligations[0]?  -- Should work at runtime

-- The question: can we build a proof that accesses obligations by index?
-- This requires: List.get? computes, and we can prove things about computed elements

-- Let's try a different approach: use Fin to index
theorem by_index_test : prePostResult.obligations.allSatisfied := by
  -- We know there's 1 obligation
  have h_len : prePostResult.obligations.length = 1 := by native_decide
  -- allSatisfied for length 1 means: just prove the first element's toProp
  -- Rewrite using the length fact
  rw [ObligationSet.allSatisfied_iff_forall]
  intro ob h_mem
  -- h_mem : ob ∈ prePostResult.obligations
  -- We need to show ob.toProp
  -- The problem: ob is abstract, we don't know which obligation it is
  -- Even though we know there's only 1, we can't extract it
  sorry

/-! ## THE REAL SOLUTION: Store Proofs Alongside Obligations

The fundamental issue: we're trying to prove obligations AFTER computing them,
but the computed structure is opaque.

Better approach: Compute proofs DURING type checking.

Instead of:
  TypeCheckResult { obligations : List Obligation }
  -- then later: prove all obligations

Do:
  TypeCheckResult { obligations : List (Obligation × proof of ob.toProp) }
  -- or: List { ob : Obligation // ob.toProp }

But this requires the type checker to produce proofs...

Actually, the RIGHT solution for CN is:
- Type checker produces SYMBOLIC obligations (what we have)
- We run SMT on the symbolic form to get a certificate
- We check the certificate in Lean

This is exactly what the Smt tactic does, but we need to apply it to SYMBOLIC goals,
not computed goals.
-/

/-! ## CONCRETE PROPOSAL: Pre-compute the proof for each obligation

The type checker knows the obligations at definition time.
We can generate proof obligations as separate theorems.

For the prePostResult, we MANUALLY write:

  def prePostResult_ob0 : Obligation := prePostResult.obligations[0]!

  theorem prePostResult_ob0_holds : prePostResult_ob0.toProp := by
    -- Now SMT can work because prePostResult_ob0 is a definition

  theorem prePostResult_allSatisfied : prePostResult.obligations.allSatisfied := by
    rw [ObligationSet.allSatisfied_iff_forall]
    intro ob h_mem
    -- Case split based on list structure
    have h_len : prePostResult.obligations.length = 1 := by native_decide
    -- ...
-/

-- Let's try the "extract and prove separately" approach
def prePostOb0 : Obligation := prePostResult.obligations[0]!

#check prePostOb0  -- This is now a concrete definition

-- Can we prove this specific obligation?
theorem prePostOb0_holds : prePostOb0.toProp := by
  unfold prePostOb0 Obligation.toProp
  intro ρ h_assumptions
  -- h_assumptions : constraintSetToProp ρ (prePostResult.obligations[0]!).assumptions
  -- goal : constraintToProp ρ (prePostResult.obligations[0]!).constraint
  -- The constraint should equal one of the assumptions (x > 0 is both pre and post)
  -- But we still can't show this without DecidableEq...
  sorry

-- What if we unfold everything?
theorem prePostOb0_holds_v2 : prePostOb0.toProp := by
  unfold prePostOb0
  -- Let's see what the goal looks like now
  sorry

end CerbLean.CN.Verification.SmtTest
