/-
  Undefined behavior kinds
  Corresponds to: cerberus/frontend/model/undefined.lem lines 21-733
  Audited: 2025-12-31
  Deviations: Not all 200+ variants are included; uses `other` catch-all for rare variants
-/

namespace CToLean.Core

/-! ## Unspecified UB Context

Corresponds to: unspecified_ub_context in undefined.lem lines 5-14
-/

/-- Context for unspecified behavior becoming undefined
    Corresponds to: unspecified_ub_context in undefined.lem lines 5-14
    Audited: 2025-12-31
    Deviations: None -/
inductive UnspecifiedUBContext where
  | equalityPtrVsNull
  | equalityBothArithOrPtr
  | pointerAdd
  | pointerSub
  | conditional
  | copyAllocId
  | rvalueMemberof
  | memberofptr
  | do_
  deriving Repr, BEq, Inhabited

/-! ## Undefined Behavior

Corresponds to: undefined_behaviour in undefined.lem lines 21-733
We include the most commonly encountered variants explicitly and use `other` for the rest.
-/

/-- Undefined behavior categories
    Corresponds to: undefined_behaviour in undefined.lem lines 21-733
    Audited: 2025-12-31
    Deviations: Only ~50 key variants included; uses `other(name)` for rare variants -/
inductive UndefinedBehavior where
  -- Dummy/placeholder (undefined.lem:22)
  | dummy (msg : String)

  -- Unspecified lvalue (undefined.lem:26)
  | unspecifiedLvalue

  -- Lifetime errors (§6.2.4)
  | ub009_outsideLifetime               -- Object referred to outside its lifetime
  | ub010_pointerToDeadObject           -- Pointer to object whose lifetime has ended
  | ub011_useIndeterminateAutomatic     -- Use of indeterminate automatic storage object
  | ub_modifyingTemporaryLifetime       -- Attempt to modify object with temporary lifetime

  -- Trap representations (§6.2.6.1)
  | ub012_lvalueReadTrapRepresentation  -- Trap representation read by non-char lvalue
  | ub013_lvalueSideEffectTrap          -- Trap representation produced by side effect

  -- Redeclaration/linkage (§6.2.2, §6.2.7)
  | ub008_multipleLinkage               -- Same identifier has internal and external linkage
  | ub015_incompatibleRedeclaration     -- Two declarations with incompatible types

  -- Type conversion errors (§6.3.1.4, §6.3.2.3)
  | ub017_outOfRangeFloatingIntConversion
  | ub019_lvalueNotAnObject             -- lvalue doesn't designate an object
  | ub024_outOfRangePointerToIntConversion
  | ub025_misalignedPointerConversion

  -- String literals (§6.4.5)
  | ub033_modifyingStringLiteral        -- Attempt to modify string literal

  -- Sequence point violations (§6.5)
  | ub035_unsequencedRace               -- Unsequenced side effects on same object
  | ub036_exceptionalCondition          -- Exceptional condition during evaluation
  | ub037_illtypedLoad                  -- Object accessed with wrong lvalue type

  -- Function calls (§6.5.2.2)
  | ub038_numberOfArgs                  -- Wrong number of arguments
  | ub041_functionNotCompatible         -- Function type not compatible

  -- Atomic struct/union (§6.5.2.3)
  | ub042_accessAtomicStructUnionMember

  -- Indirection (§6.5.3.2)
  | ub043_indirectionInvalidValue       -- Unary * on invalid pointer

  -- Division and modulo (§6.5.5)
  | ub045a_divisionByZero
  | ub045b_moduloByZero
  | ub045c_quotientNotRepresentable

  -- Pointer arithmetic (§6.5.6)
  | ub046_arrayPointerOutside           -- Pointer + int produces out-of-bounds result
  | ub047a_arrayPointerAdditionBeyondIndirection
  | ub047b_arrayPointerSubtractionBeyondIndirection
  | ub048_disjointArrayPointersSubtraction  -- Subtraction of unrelated pointers
  | ub050_pointersSubtractionNotRepresentable

  -- Shift operations (§6.5.7)
  | ub051a_negativeShift
  | ub051b_shiftTooLarge
  | ub052a_negativeLeftShift
  | ub052b_nonRepresentableLeftShift

  -- Pointer comparison (§6.5.8)
  | ub053_distinctAggregateUnionPointerComparison

  -- Assignment (§6.5.16.1)
  | ub054a_inexactlyOverlappingAssignment
  | ub054b_incompatibleOverlappingAssignment

  -- Declarations (§6.7)
  | ub059_incompleteNoLinkageIdentifier
  | ub061_noNamedMembers                -- Struct/union with no named members
  | ub064_modifyingConst                -- Modifying const-qualified object
  | ub070_inlineNotDefined
  | ub071_noreturn                      -- _Noreturn function returns

  -- End of non-void function (§6.9.1)
  | ub088_endOfNonVoidFunction          -- Reaching } of non-void function

  -- CERB extensions (undefined.lem:711-732)
  | ub_cerb001_integerToDeadPointer
  | ub_cerb002a_outOfBoundLoad
  | ub_cerb002b_outOfBoundStore
  | ub_cerb002c_outOfBoundFree
  | ub_cerb002d_outOfBoundRealloc
  | ub_cerb003_invalidFunctionPointer
  | ub_cerb004_unspecified (ctx : UnspecifiedUBContext)
  | ub_cerb005_freeNullptr

  -- Catch-all for other UB variants
  | other (name : String)
  deriving Repr, BEq, Inhabited

instance : ToString UndefinedBehavior where
  toString ub := repr ub |>.pretty

end CToLean.Core
