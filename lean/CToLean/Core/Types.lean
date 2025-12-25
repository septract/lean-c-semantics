/-
  Core IR type definitions
  Based on cerberus/frontend/ott/core-ott/core.ott lines 29-125
-/

import CToLean.Core.Sym
import CToLean.Core.Ctype

namespace CToLean.Core

/-! ## Object Types

Types whose inhabitants can be read from and stored to memory (matching C types)
-/

/-- Core object types - types for C objects that can be stored in memory -/
inductive ObjectType where
  | integer
  | floating
  | pointer
  | array (elemTy : ObjectType)
  | struct_ (tag : Sym)
  | union_ (tag : Sym)
  deriving Repr, BEq, Inhabited

/-! ## Base Types

Core base types used in the type system
-/

/-- Core base types -/
inductive BaseType where
  | unit
  | boolean
  | ctype      -- C type as a value
  | list (elemTy : BaseType)
  | tuple (elemTys : List BaseType)
  | object (objTy : ObjectType)
  | loaded (objTy : ObjectType)  -- object type or unspecified value
  | storable   -- top type for storable values (used in type system only)
  deriving Repr, BEq, Inhabited

/-- Core types (pure or effectful) -/
inductive CoreType where
  | base (ty : BaseType)
  | effect (ty : BaseType)  -- effectful computation returning ty
  deriving Repr, BEq, Inhabited

/-! ## Binary Operators -/

/-- Integer operations (for overflow checks) -/
inductive Iop where
  | add
  | sub
  | mul
  | shl   -- shift left
  | shr   -- shift right
  | div
  | rem_t -- truncated remainder
  deriving Repr, BEq, Inhabited

/-- Binary operators -/
inductive Binop where
  -- Arithmetic operators (integer -> integer -> integer)
  | add
  | sub
  | mul
  | div
  | rem_t  -- truncated remainder (C's %)
  | rem_f  -- floored remainder
  | exp    -- exponentiation
  -- Relational operators
  | eq
  | gt
  | lt
  | ge
  | le
  -- Logical connectives
  | and
  | or
  deriving Repr, BEq, Inhabited

/-! ## Polarity -/

/-- Memory action polarity (for sequencing) -/
inductive Polarity where
  | pos  -- sequenced by both letweak and letstrong
  | neg  -- only sequenced by letstrong
  deriving Repr, BEq, Inhabited

/-! ## Memory Operations -/

/-- Memory operations involving memory state -/
inductive Memop where
  | ptrEq           -- pointer equality comparison
  | ptrNe           -- pointer inequality
  | ptrLt           -- pointer relational comparison
  | ptrGt
  | ptrLe
  | ptrGe
  | ptrdiff         -- pointer subtraction
  | intFromPtr      -- cast pointer to integer
  | ptrFromInt      -- cast integer to pointer
  | ptrValidForDeref
  | ptrWellAligned
  | ptrArrayShift
  | ptrMemberShift (tag : Sym) (member : Identifier)
  | memcpy
  | memcmp
  | realloc
  | vaStart
  | vaCopy
  | vaArg
  | vaEnd
  | copyAllocId     -- RefinedC: copy allocation ID between pointers
  | cheriIntrinsic (name : String)  -- CHERI capability operations
  deriving Repr, BEq, Inhabited

/-! ## Kill Kind -/

/-- Storage duration kind for kill() action -/
inductive KillKind where
  | dynamic          -- free()
  | static (ty : Ctype)
  deriving Repr, BEq, Inhabited

/-! ## Memory Order (for atomics) -/

/-- C11 memory ordering -/
inductive MemoryOrder where
  | na        -- Non-atomic (default, omitted in pretty-print)
  | relaxed
  | consume
  | acquire
  | release
  | acqRel
  | seqCst
  deriving Repr, BEq, Inhabited

end CToLean.Core
