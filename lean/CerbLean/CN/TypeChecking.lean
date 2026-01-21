/-
  CN Type Checking Module

  This module provides CN's type checking algorithm, which verifies that
  C functions satisfy their CN specifications.

  The type checker implements two levels of verification:

  **Level 1 (Traditional Type Checking):**
  - Ensures CN terms are well-typed with respect to base types
  - IndexTerms are well-typed by construction (carry their type in `bt` field)

  **Level 2 (Separation Logic Verification):**
  - Processes preconditions (requires): consumes resources from context
  - Checks function body: tracks resources through execution
  - Processes postconditions (ensures): produces resources
  - Verifies constraints via a proof oracle
  - Detects memory safety violations (use-after-free, double-free, leaks)

  Key components:
  - Context: tracks variables, resources, constraints
  - Monad: state monad with proof oracle interface
  - Inference: resource matching algorithm
  - Pexpr: pure expression to IndexTerm conversion
  - Action: memory action checking (create, kill, store, load)
  - Expr: effectful expression walking with resource tracking
  - Check: top-level function verification

  Reference: CN paper "Verifying Systems C Code with Separation-Logic
  Refinement Types" (POPL 2023)
-/

import CerbLean.CN.TypeChecking.Context
import CerbLean.CN.TypeChecking.Monad
import CerbLean.CN.TypeChecking.Inference
import CerbLean.CN.TypeChecking.Pexpr
import CerbLean.CN.TypeChecking.Action
import CerbLean.CN.TypeChecking.Expr
import CerbLean.CN.TypeChecking.Check
