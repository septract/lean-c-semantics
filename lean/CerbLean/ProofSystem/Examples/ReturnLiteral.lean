/-
  Example: Typing derivation for `int main() { return 0; }`

  Core IR (simplified):
    proc main [] =
      pure (Specified 0)

  Typing derivation:
    Gamma = empty context
    H_pre = emp
    H_post = emp

    By HasType.pure:
      PureHasType Gamma (APexpr for 0) (bits .signed 32)
    =>
      HasType Gamma emp (AExpr for pure 0) (bits .signed 32) emp

  This file creates concrete terms to validate that the SLProp and type
  definitions are usable in practice. The actual typing derivation proof
  will be added once HasType.lean is integrated.
-/

import CerbLean.ProofSystem.HasType

namespace CerbLean.ProofSystem.Examples

open CerbLean.Core (Sym Ctype Value ObjectValue IntegerValue APexpr Pexpr AExpr Expr Annots)
open CerbLean.CN.Types

/-! ## Return literal: `int main() { return 0; }` -/

/-- The return value 0 as a CN index term.
    Represents the constant `0` with type `i32` (signed 32-bit integer). -/
def zeroTerm : IndexTerm :=
  AnnotTerm.mk (.const (.bits .signed 32 0)) (.bits .signed 32) default

/-- The SLProp precondition for `main`: no resources needed. -/
def mainPre : SLProp := .emp

/-- The SLProp postcondition for `main`: no resources produced. -/
def mainPost : SLProp := .emp

/-- The return type of `main` as a CN base type: signed 32-bit integer. -/
def mainReturnType : BaseType := .bits .signed 32

/-! ## Sanity checks -/

example : mainPre.flatten = [] := rfl
example : mainPost.flatten = [] := rfl
example : zeroTerm.bt = .bits .signed 32 := rfl
example : zeroTerm.term = .const (.bits .signed 32 0) := rfl

/-! ## Typing derivation

    `int main() { return 0; }` compiles to Core roughly as:
      pure (Specified (Ctype int) 0)

    We model this as `Expr.pure pe` where `pe` is an APexpr wrapping the value 0.
    The derivation uses `HasType.pure` + `PureHasType.val`. -/

/-- The Core expression for `return 0`: `pure (Specified 0)`.
    In Core, integer 0 is represented as `Value.loaded (.specified (.integer ⟨0⟩))`. -/
def mainExpr : AExpr :=
  ⟨[], .pure ⟨[], none, .val (.loaded (.specified (.integer ⟨0, .none⟩)))⟩⟩

/-- Typing derivation: `main` has type i32 and preserves empty heap. -/
theorem mainTyped :
    HasType Ctx.empty .emp mainExpr (.bits .signed 32) .emp := by
  exact HasType.pure (PureHasType.val trivial)

end CerbLean.ProofSystem.Examples
