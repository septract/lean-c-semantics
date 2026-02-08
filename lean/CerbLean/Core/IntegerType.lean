/-
  Integer types representation
  Corresponds to: cerberus/frontend/model/integerType.lem lines 10-35

  Extracted to its own file so both Annot.lean and Ctype.lean can
  reference IntegerType without circular imports. This is needed
  because Annot.value_annot contains Ainteger(integerType).

  This file has NO imports (other than Init) to avoid cycles in:
    Sym.lean → Annot.lean → IntegerType.lean → (must not import Sym.lean)

  Audited: 2025-12-31
  Deviations: enum tag uses Nat (symbol ID) instead of Sym to avoid circular import
-/

namespace CerbLean.Core

/-! ## Integer Types

Corresponds to: cerberus/frontend/model/integerType.lem lines 10-35
-/

/-- Integer base type kinds (used for both signed and unsigned)
    Corresponds to: integerBaseType in integerType.lem lines 10-21
    Audited: 2025-12-31
    Deviations: None -/
inductive IntBaseKind where
  | ichar       -- (signed/unsigned) char
  | short
  | int_
  | long
  | longLong
  | intN (n : Nat)       -- _BitInt(N) / unsigned _BitInt(N)
  | intLeastN (n : Nat)  -- int_leastN_t / uint_leastN_t
  | intFastN (n : Nat)   -- int_fastN_t / uint_fastN_t
  | intmax             -- intmax_t / uintmax_t
  | intptr             -- intptr_t / uintptr_t
  deriving Repr, BEq, Inhabited

/-- Integer types from the C standard (§6.2.5#17)
    Corresponds to: integerType in integerType.lem lines 24-35
    Audited: 2025-12-31
    Deviations: enum tag uses Nat (symbol ID) instead of Sym to break import cycle -/
inductive IntegerType where
  | char                           -- plain char (implementation-defined signedness)
  | bool                           -- _Bool
  | signed (kind : IntBaseKind)    -- signed integer types
  | unsigned (kind : IntBaseKind)  -- unsigned integer types
  | enum (tagId : Nat)             -- enum type (symbol ID)
  | size_t                         -- size_t (unsigned, special)
  | wchar_t                        -- wchar_t (implementation-defined)
  | wint_t                         -- wint_t
  | ptrdiff_t                      -- ptrdiff_t (signed, special)
  | ptraddr_t                      -- ptraddr_t (CHERI)
  deriving Repr, BEq, Inhabited

end CerbLean.Core
