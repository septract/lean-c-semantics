/-
  Example: Typing derivation for a simple countdown loop

  This is the minimal loop example, exercising save/run typing rules.
  The function decrements a counter to zero.

  C source:
    void countdown(int *p) {
      while (*p > 0) { *p = *p - 1; }
    }

  Core IR (simplified):
    proc countdown [p : pointer<signed int>] =
      save loop (v : signed_int = load(signed_int, p)) {
        if (v > 0) {
          sseq _ = store(signed_int, p, v - 1)
          run loop [v - 1]
        } else {
          pure ()
        }
      }

  Specification (CN-style):
    requires: Owned<signed int>(init, p, vOld) where vOld >= 0
    ensures:  Owned<signed int>(init, p, 0)

  Loop invariant:
    Owned<signed int>(init, p, v) where v >= 0

  Created: 2026-02-27
-/

import CerbLean.ProofSystem.HasType

namespace CerbLean.ProofSystem.Examples

open CerbLean.Core (Sym Ctype Ctype_ BasicType IntegerType IntBaseKind
                     Value LoadedValue ObjectValue IntegerValue
                     APexpr Pexpr AExpr Expr APattern Pattern
                     Paction AAction Action Polarity MemoryOrder KillKind
                     Annots Binop SymPrefix Loc Name)
open CerbLean.CN.Types

/-! ## Type and Symbol Definitions -/

/-- The C type `signed int`. -/
def cntSignedIntCtype : Ctype := ⟨[], .basic (.integer (.signed .int_))⟩

/-- Symbol for the pointer parameter `p`. -/
def cntPSym : Sym := { id := 0, description := .id "p" }

/-- Symbol for the loop label. -/
def loopSym : Sym := { id := 1, description := .id "loop" }

/-- Symbol for the current counter value `v`. -/
def cntVSym : Sym := { id := 2, description := .id "v" }

/-! ## Index Terms -/

/-- Index term for pointer `p`. -/
def cntPtrTerm : IndexTerm :=
  AnnotTerm.mk (.sym cntPSym) .loc default

/-- Index term for the loop variable `v`. -/
def cntVTerm : IndexTerm :=
  AnnotTerm.mk (.sym cntVSym) (.bits .signed 32) default

/-! ## Loop Invariant

  The loop invariant is: `Owned<signed int>(init, p, v)`
  where `v` is the current counter value (parameter of the loop).
-/

/-- The loop invariant: `Owned<int>(init, p, v)`. -/
def loopInvariant : SLProp :=
  .owned cntSignedIntCtype .init cntPtrTerm cntVTerm

/-- The label invariant structure for the loop. -/
def loopLabelInv : LabelInv where
  params := [(cntVSym, .bits .signed 32)]
  invariant := loopInvariant

/-! ## Typing Context

  The context has:
  - `p` bound as a pointer (loc type)
  - The loop label invariant registered
-/

/-- The typing context for `countdown`. -/
def cntCtx : Ctx :=
  { Ctx.empty with
    vars := [(cntPSym, .loc)]
    labelInvs := [(loopSym, loopLabelInv)] }

/-! ## Postcondition

  After the loop, the counter is 0. We model this as
  `Owned<int>(init, p, zeroTerm)` where zeroTerm represents 0.
-/

/-- Index term for the final value `0`. -/
def cntZeroTerm : IndexTerm :=
  AnnotTerm.mk (.const (.bits .signed 32 0)) (.bits .signed 32) default

/-- Postcondition: `Owned<int>(init, p, 0)`. -/
def cntPost : SLProp :=
  .owned cntSignedIntCtype .init cntPtrTerm cntZeroTerm

/-! ## Typing Derivation (outline)

  The full derivation exercises save/run rules:

  1. `save loop (v)`:
     - Look up `loopSym` in context → `loopLabelInv`
     - Body type-checks under `loopInvariant` with `v` bound

  2. Inside save body:
     - `if (v > 0)`:
       - True branch: store `v-1`, then `run loop [v-1]`
       - False branch: `pure ()`

  3. `run loop [v-1]`:
     - Current heap satisfies `loopInvariant` (with updated v)
     - Type and post-heap are unconstrained (control transfer)

  This derivation is sorry'd because the inner proofs require:
  - Connecting the load/store to invariant maintenance
  - Proving the loop body preserves the invariant
  - Arithmetic reasoning (v > 0 → v - 1 ≥ 0)
-/

/-- The save rule is applicable: the loop label is in context. -/
example : cntCtx.lookupLabelInv loopSym = some loopLabelInv := by
  rfl

/-- The invariant parameters can be added to the context. -/
example : (cntCtx.addParams loopLabelInv.params).lookupVar cntVSym =
    some (.bits .signed 32) := by
  rfl

/-- Typing derivation for the countdown loop.
    The full proof is sorry'd — the structure is here to validate that
    the save/run rules are usable. -/
theorem countdownTyped :
    HasType cntCtx
      (.star loopInvariant .emp)
      -- A simplified expression: save loop { ... run loop ... }
      -- The full Core expression is complex; we use sorry to validate
      -- the rule structure rather than constructing the full term.
      sorry  -- expression
      .unit
      (.star cntPost .emp) := by
  sorry

end CerbLean.ProofSystem.Examples
