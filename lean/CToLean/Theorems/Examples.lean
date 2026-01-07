/-
  Examples of applying UBFree to simple Core expressions

  This file demonstrates the verification approach by showing how to:
  1. Construct simple Core AST expressions
  2. State that evaluating them is UB-free
  3. (Eventually) prove the UB-freeness
-/

import CToLean.Theorems.UBFree
import CToLean.Semantics.Eval

namespace CToLean.Theorems.Examples

open CToLean.Core
open CToLean.Semantics
open CToLean.Memory

/-! ## Helper: Constructing Core Expressions

These helpers make it easier to construct Core AST nodes for examples.
-/

/-- Create an annotated pure expression with no annotations -/
def mkPexpr (e : Pexpr) : APexpr :=
  { annots := [], ty := none, expr := e }

/-- Create an integer value -/
def intVal (n : Int) : Value :=
  .object (.integer ⟨n, .none⟩)

/-- Create a pure expression that is just an integer literal -/
def intLit (n : Int) : APexpr :=
  mkPexpr (.val (intVal n))

/-- Create an addition expression -/
def addExpr (e1 e2 : APexpr) : APexpr :=
  mkPexpr (.op .add e1.expr e2.expr)

/-! ## Example 1: A Simple Integer Literal

The simplest possible Core expression: just a literal value like `5`.

In Core IR, this looks like:
```
PEval (Vinteger 5)
```

Evaluating a literal should always be UB-free.
-/

/-- The expression `5` as Core AST -/
def expr_five : APexpr := intLit 5

/-- Evaluating a literal in an empty environment -/
def eval_five : InterpM Value := evalPexpr [] expr_five

/-- Theorem: Evaluating the literal `5` is UB-free.

    This is trivially true because evaluating a value literal
    just returns that value - no operations that could cause UB.

    NOTE: evalPexpr is `partial`, so we can't unfold it directly.
    We need either:
    1. A relational semantics (inductive predicate for evaluation)
    2. Axioms about evalPexpr's behavior
    3. A termination proof for evalPexpr

    For now, we state the theorem and mark it sorry.
-/
theorem eval_five_ubfree : UBFree eval_five := by
  unfold UBFree eval_five
  intro env state
  -- evalPexpr is partial, so we can't unfold it in proofs
  -- This would require either:
  -- 1. Relational semantics: `Eval env pe v` instead of `evalPexpr env pe = v`
  -- 2. Axioms: `axiom evalPexpr_val : evalPexpr env (mkPexpr (.val v)) = pure v`
  sorry

/-! ## Example 2: Simple Addition

The expression `5 + 3` in Core IR.

This involves the binary operator, which COULD cause UB if:
- The operands overflow (for signed integers)
- The types are incompatible

But `5 + 3 = 8` is well within Int32 range, so it should be UB-free.
-/

/-- The expression `5 + 3` as Core AST -/
def expr_five_plus_three : APexpr := addExpr (intLit 5) (intLit 3)

/-- Evaluating `5 + 3` -/
def eval_five_plus_three : InterpM Value := evalPexpr [] expr_five_plus_three

/-- The result of `5 + 3` is `8` -/
def expected_eight : Value := intVal 8

/-! ## Example 3: Statement of UB-Freeness for Addition

For more complex expressions, we need to reason about the semantics.
The general pattern is:

1. Construct the Core AST for the expression
2. State that `evalPexpr env expr` is UB-free (possibly with preconditions)
3. Prove by unfolding definitions and applying lemmas
-/

/-- Statement: `5 + 3` is UB-free.

    This should be provable because:
    - 5 and 3 are small integers (well within Int32 range)
    - Their sum 8 is also within range
    - No memory operations involved
-/
theorem eval_five_plus_three_ubfree : UBFree eval_five_plus_three := by
  unfold UBFree eval_five_plus_three
  intro env state
  -- Requires relational semantics or axioms about evalPexpr
  sorry

/-! ## Example 4: Division (Conditional UB-Freeness)

Division `a / b` is UB-free only if `b ≠ 0`.
This demonstrates conditional UB-freeness with preconditions.
-/

/-- Create a division expression -/
def divExpr (e1 e2 : APexpr) : APexpr :=
  mkPexpr (.op .div e1.expr e2.expr)

/-- The expression `10 / 2` -/
def expr_ten_div_two : APexpr := divExpr (intLit 10) (intLit 2)

/-- Evaluating `10 / 2` -/
def eval_ten_div_two : InterpM Value := evalPexpr [] expr_ten_div_two

/-- Statement: `10 / 2` is UB-free because 2 ≠ 0 -/
theorem eval_ten_div_two_ubfree : UBFree eval_ten_div_two := by
  unfold UBFree eval_ten_div_two
  intro env state
  -- Requires relational semantics or axioms about evalPexpr
  sorry

/-! ## The General Pattern

For any Core expression `e`, stating UB-freeness follows this pattern:

```lean
-- 1. Define the expression
def my_expr : APexpr := ...

-- 2. Define the evaluation
def eval_my_expr : InterpM Value := evalPexpr env my_expr

-- 3. State UB-freeness (possibly with preconditions)
theorem my_expr_ubfree (preconditions...) : UBFree eval_my_expr := by
  ...

-- Or with specific env/state:
theorem my_expr_ubfree_in (env : InterpEnv) (state : InterpState)
    (preconditions...) : UBFreeIn eval_my_expr env state := by
  ...
```

The proofs require:
- Lemmas about `evalBinop` for arithmetic operations
- Lemmas about memory operations for loads/stores
- Range checking for integer overflow
- Null/bounds checking for pointer operations
-/

/-! ## What's Needed for Real Proofs

To complete the proofs marked `sorry`, we need:

1. **Lemmas about evalBinop**: e.g., `evalBinop_add_safe` showing that
   addition of in-range integers is UB-free.

2. **Lemmas about evalPexpr cases**: Breaking down how each Pexpr
   constructor evaluates and when it can UB.

3. **Connection to SafeDiv, SafeShift, etc.**: The predicates we defined
   should connect to the actual interpreter operations.

This is the work of Phase 2 (Weakest Precondition calculus) in the
verification plan.
-/

end CToLean.Theorems.Examples
