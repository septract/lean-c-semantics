/-
  Core IR type definitions
  Corresponds to: cerberus/frontend/ott/core-ott/core.ott lines 29-125
  Audited: 2025-12-31
  Deviations: None
-/

import CToLean.Core.Sym
import CToLean.Core.Ctype

namespace CToLean.Core

/-! ## Object Types

Corresponds to: core.ott lines 30-36
```ott
core_object_type :: 'OTy_' ::=
  | integer
  | floating
  | pointer
  | array ( core_object_type )
  | struct tag
  | union tag
```
-/

/-- Core object types - types for C objects that can be stored in memory
    Corresponds to: core_object_type in core.ott:30-36
    Audited: 2025-12-31
    Deviations: None -/
inductive ObjectType where
  | integer
  | floating
  | pointer
  | array (elemTy : ObjectType)
  | struct_ (tag : Sym)
  | union_ (tag : Sym)
  deriving Repr, BEq, Inhabited

/-! ## Base Types

Corresponds to: core.ott lines 71-79
```ott
core_base_type :: 'BTy_' ::=
  | unit
  | boolean
  | ctype
  | [ core_base_type ]
  | ( </ core_base_typei // , // i /> )
  | core_object_type
  | loaded core_object_type
  | storable
```
-/

/-- Core base types
    Corresponds to: core_base_type in core.ott:71-79
    Audited: 2025-12-31
    Deviations: None -/
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

/-! ## Core Types

Corresponds to: core.ott lines 122-124
```ott
core_type :: 'Ty' ::=
  | core_base_type
  | eff core_base_type
```
-/

/-- Core types (pure or effectful)
    Corresponds to: core_type in core.ott:122-124
    Audited: 2025-12-31
    Deviations: None -/
inductive CoreType where
  | base (ty : BaseType)
  | effect (ty : BaseType)  -- effectful computation returning ty
  deriving Repr, BEq, Inhabited

/-! ## Integer Operations

Corresponds to: core.lem lines 112-120
```lem
type iop =
 | IOpAdd | IOpSub | IOpMul | IOpShl | IOpShr | IOpDiv | IOpRem_t
```
-/

/-- Integer operations (for overflow checks)
    Corresponds to: iop in core.lem:112-120
    Audited: 2025-12-31
    Deviations: None -/
inductive Iop where
  | add
  | sub
  | mul
  | shl   -- shift left
  | shr   -- shift right
  | div
  | rem_t -- truncated remainder
  deriving Repr, BEq, Inhabited

/-! ## Binary Operators

Corresponds to: core.ott lines 127-144
```ott
binop :: 'Op' ::=
  | + | - | * | / | rem_t | rem_f | ^
  | = | > | < | >= | <=
  | /\ | \/
```
-/

/-- Binary operators
    Corresponds to: binop in core.ott:127-144
    Audited: 2025-12-31
    Deviations: None -/
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

/-! ## Polarity

Corresponds to: core.ott lines 175-177
```ott
polarity :: '' ::=
  | Pos
  | Neg
```
-/

/-- Memory action polarity (for sequencing)
    Corresponds to: polarity in core.ott:175-177
    Audited: 2025-12-31
    Deviations: None -/
inductive Polarity where
  | pos  -- sequenced by both letweak and letstrong
  | neg  -- only sequenced by letstrong
  deriving Repr, BEq, Inhabited

/-! ## Memory Operations

Corresponds to: mem_common.lem lines 371-402
```lem
type generic_memop 'sym =
  | PtrEq | PtrNe | PtrLt | PtrGt | PtrLe | PtrGe
  | Ptrdiff | IntFromPtr | PtrFromInt | PtrValidForDeref
  | PtrWellAligned | PtrArrayShift
  | PtrMemberShift of 'sym * Symbol.identifier
  | Memcpy | Memcmp | Realloc
  | Va_start | Va_copy | Va_arg | Va_end
  | Copy_alloc_id
  | CHERI_intrinsic of string * (Ctype.ctype * list Ctype.ctype)
```
-/

/-- Memory operations involving memory state
    Corresponds to: generic_memop in mem_common.lem:371-402
    Audited: 2025-12-31
    Deviations: None -/
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

/-! ## Kill Kind

Corresponds to: core.ott lines 351-353
```ott
kill_kind :: '' ::=
  | dyn
  | static ty
```
-/

/-- Storage duration kind for kill() action
    Corresponds to: kill_kind in core.ott:351-353
    Audited: 2025-12-31
    Deviations: None -/
inductive KillKind where
  | dynamic          -- free()
  | static (ty : Ctype)
  deriving Repr, BEq, Inhabited

/-! ## Memory Order (for atomics)

Corresponds to: cmm_csem.lem lines 198-205
```lem
type memory_order =
  | NA | Seq_cst | Relaxed | Release | Acquire | Consume | Acq_rel
```
-/

/-- C11 memory ordering
    Corresponds to: memory_order in cmm_csem.lem:198-205
    Audited: 2025-12-31
    Deviations: None -/
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
