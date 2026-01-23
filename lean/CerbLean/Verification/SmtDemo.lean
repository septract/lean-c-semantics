/-
  Demonstration of lean-smt integration for symbolic reasoning.

  This shows how SMT solvers can prove properties that native_decide cannot:
  - Universal quantification over inputs
  - Arithmetic reasoning about bounds and overflow
-/

import Smt

namespace CerbLean.Verification.SmtDemo

/-! ## Basic SMT Examples -/

-- SMT can prove universal properties over integers
theorem int_add_comm (x y : Int) : x + y = y + x := by
  smt

-- Proving implications with hypotheses
theorem pos_sum (x y : Int) (hx : x > 0) (hy : y > 0) : x + y > 0 := by
  smt [hx, hy]

-- Bounds reasoning - useful for overflow checking
theorem no_overflow_small (x : Int) (h : 0 ≤ x ∧ x < 100) :
    x + 1 < 2147483647 := by
  smt [h]

/-! ## Arithmetic Reasoning -/

-- Multiple constraints - transitivity
theorem in_range (x y : Int) (hx : 0 ≤ x) (hy : x ≤ y) (hbound : y < 1000) :
    x < 1000 := by
  smt [hx, hy, hbound]

-- Linear arithmetic
theorem triangle_ineq (x y z : Int) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  smt [h1, h2]

theorem tests : 1 < 2 := by
  smt

/-! ## Comparison with native_decide -/

-- native_decide: only works for CONCRETE values
-- This computes 2 + 3 = 5 and checks it equals 5
example : (2 : Int) + 3 = 5 := by native_decide

-- SMT: works for SYMBOLIC values
-- This proves x + 0 = x for ALL integers x
theorem add_zero_right (x : Int) : x + 0 = x := by
  smt

/-! ## Potential Use Cases for C Verification -/

-- Proving array index is in bounds (symbolic)
theorem array_index_safe (i n : Nat) (h : i < n) : i < n := by
  smt [h]

-- Proving a sum is in range given bounds on inputs
theorem sum_in_range (x y : Int)
    (hx : 0 ≤ x ∧ x ≤ 100)
    (hy : 0 ≤ y ∧ y ≤ 100) :
    0 ≤ x + y ∧ x + y ≤ 200 := by
  smt [hx, hy]

-- A more interesting example: if preconditions imply no overflow
theorem add_small_no_overflow (x y : Int)
    (hx : 0 ≤ x ∧ x < 1000000)
    (hy : 0 ≤ y ∧ y < 1000000) :
    x + y < 2147483647 := by
  smt [hx, hy]

end CerbLean.Verification.SmtDemo
