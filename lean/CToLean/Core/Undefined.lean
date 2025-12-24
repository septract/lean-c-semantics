/-
  Undefined behavior kinds
  Based on cerberus/frontend/model/undefined.lem
-/

namespace CToLean.Core

/-- Undefined behavior categories -/
inductive UndefinedBehavior where
  -- Memory errors
  | useAfterFree
  | doubleFree
  | outOfBounds
  | nullDeref
  | uninitializedRead
  | invalidAlignment
  -- Integer errors
  | divisionByZero
  | signedOverflow
  | shiftOutOfRange
  -- Pointer errors
  | invalidPointerArith
  | invalidPointerComparison
  | invalidPointerSubtraction
  -- Type errors
  | invalidCast
  -- Sequence point violations
  | unsequencedModification
  -- Other
  | other (name : String)
  deriving Repr, BEq, Inhabited

end CToLean.Core
