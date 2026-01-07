import CToLean.Theorems.UBFree
import CToLean.Theorems.WP

/-!
# Verification Theorems for C Programs

This module re-exports the verification infrastructure for proving properties
of C programs translated to Core IR.

## Verification Strategy

The verification approach has two main components:

1. **UB-Freeness (`UBFree`)**: Predicates and theorems for proving that
   programs do not exhibit undefined behavior. This is the foundation -
   a program with UB has no defined semantics.

2. **Weakest Precondition (`WP`)**: A compositional calculus for reasoning
   about program correctness. Given a postcondition Q, compute the weakest
   precondition that ensures Q holds after execution.

## Submodules

- `CToLean.Theorems.UBFree`: UB-freeness predicates (`UBFree`, `UBFreeIn`, etc.)
  and safety conditions (`SafeDiv`, `SafeShift`, `ValidPointer`)

- `CToLean.Theorems.WP`: Weakest precondition calculus with compositional
  rules for if/let/binop expressions

## Usage Example

```lean
-- Prove a simple expression is UB-free
example : wpPureN 10 ⟨[], none, .if_ (.val .true_) (.val v1) (.val v2)⟩
    (fun _ _ => True) [] default default := by
  simp only [wpPureN, evalPexpr, ...]
```

## Related Documentation

- `docs/VERIFICATION_PLAN.md`: Overall verification roadmap
- `CLAUDE.md`: Project conventions and Cerberus correspondence requirements
-/
