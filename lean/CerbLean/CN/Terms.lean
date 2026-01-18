/-
  CN Index Terms (Specification Expression Language)
  Corresponds to: cn/lib/terms.ml

  Index terms are the expression language used in CN specifications.
  They represent symbolic values used in preconditions, postconditions,
  assertions, and resource predicates.

  Audited: 2025-01-17 against cn/lib/terms.ml
  Deviations: None significant
-/

import CerbLean.CN.BaseTypes
import CerbLean.Core.Ctype
import CerbLean.Core.Annot

namespace CerbLean.CN

open CerbLean.Core (Sym Identifier Loc Ctype IntegerType)

/-! ## Constants

Corresponds to: cn/lib/terms.ml lines 1-21
```ocaml
type const =
  | Z of Z.t
  | Bits of (BaseTypes.sign * int) * Z.t
  | Q of Q.t
  | MemByte of { alloc_id : Z.t option; value : Z.t }
  | Pointer of { alloc_id : Z.t; addr : Z.t }
  | Alloc_id of Z.t
  | Bool of bool
  | Unit
  | Null
  | CType_const of Sctypes.ctype
  | Default of BaseTypes.t
```
-/

/-- Memory byte value with optional allocation ID
    Corresponds to: MemByte in terms.ml lines 5-8
    Audited: 2025-01-17 -/
structure MemByteConst where
  allocId : Option Int
  value : Int
  deriving Repr, BEq, Inhabited

/-- Pointer value with allocation ID and address
    Corresponds to: Pointer in terms.ml lines 9-12
    Audited: 2025-01-17 -/
structure PointerConst where
  allocId : Int
  addr : Int
  deriving Repr, BEq, Inhabited

/-- Constants in CN index terms
    Corresponds to: const in terms.ml lines 1-21
    Audited: 2025-01-17
    Deviations: None -/
inductive Const where
  /-- Unbounded integer -/
  | z (value : Int)
  /-- Fixed-width bitvector: ((sign, width), value) -/
  | bits (sign : Sign) (width : Nat) (value : Int)
  /-- Rational number (represented as pair of integers) -/
  | q (num : Int) (denom : Int)
  /-- Memory byte -/
  | memByte (mb : MemByteConst)
  /-- Pointer value -/
  | pointer (ptr : PointerConst)
  /-- Allocation ID -/
  | allocId (id : Int)
  /-- Boolean -/
  | bool (b : Bool)
  /-- Unit value -/
  | unit
  /-- Null pointer -/
  | null
  /-- C type constant -/
  | ctypeConst (ct : Ctype)
  /-- Default value of a type (unknown but consistent) -/
  | default (bt : BaseType)
  deriving Repr, Inhabited

/-! ## Unary Operators

Corresponds to: cn/lib/terms.ml lines 24-32
```ocaml
type unop =
  | Not
  | Negate
  | BW_CLZ_NoSMT
  | BW_CTZ_NoSMT
  | BW_FFS_NoSMT
  | BW_FLS_NoSMT
  | BW_Compl
```
-/

/-- Unary operators for index terms
    Corresponds to: unop in terms.ml lines 24-32
    Audited: 2025-01-17
    Deviations: None -/
inductive UnOp where
  /-- Logical negation -/
  | not
  /-- Arithmetic negation -/
  | negate
  /-- Count leading zeros (uninterpreted for SMT) -/
  | bwClzNoSMT
  /-- Count trailing zeros (uninterpreted for SMT) -/
  | bwCtzNoSMT
  /-- Find first set bit (uninterpreted for SMT) -/
  | bwFfsNoSMT
  /-- Find last set bit (uninterpreted for SMT) -/
  | bwFlsNoSMT
  /-- Bitwise complement -/
  | bwCompl
  deriving Repr, BEq, Inhabited

/-! ## Binary Operators

Corresponds to: cn/lib/terms.ml lines 34-67
```ocaml
type binop =
  | And | Or | Implies
  | Add | Sub | Mul | MulNoSMT | Div | DivNoSMT
  | Exp | ExpNoSMT | Rem | RemNoSMT | Mod | ModNoSMT
  | BW_Xor | BW_And | BW_Or | ShiftLeft | ShiftRight
  | LT | LE | Min | Max | EQ
  | LTPointer | LEPointer
  | SetUnion | SetIntersection | SetDifference | SetMember | Subset
```
-/

/-- Binary operators for index terms
    Corresponds to: binop in terms.ml lines 34-67
    Audited: 2025-01-17
    Deviations: None -/
inductive BinOp where
  -- Logical operators
  | and_ | or_ | implies
  -- Arithmetic operators
  | add | sub | mul | mulNoSMT | div | divNoSMT
  | exp | expNoSMT | rem | remNoSMT | mod_ | modNoSMT
  -- Bitwise operators
  | bwXor | bwAnd | bwOr | shiftLeft | shiftRight
  -- Comparison operators
  | lt | le | min | max | eq
  -- Pointer comparison operators
  | ltPointer | lePointer
  -- Set operators
  | setUnion | setIntersection | setDifference | setMember | subset
  deriving Repr, BEq, Inhabited

/-! ## Terms, Patterns, and Annotated Terms

These types are mutually recursive:
- Term contains AnnotTerm
- AnnotTerm contains Term
- Pattern_ contains Pattern
- Pattern contains Pattern_
- Term's match_ case contains Pattern

We define them using mutual recursion.

Corresponds to: cn/lib/terms.ml lines 69-136
-/

mutual

/-- Pattern in match expressions (inner structure)
    Corresponds to: pattern_ in terms.ml lines 69-72
    Audited: 2025-01-17
    Deviations: None -/
inductive Pattern_ where
  /-- Variable binding -/
  | sym (s : Sym)
  /-- Wildcard (matches anything) -/
  | wild
  /-- Datatype constructor pattern -/
  | constructor (constr : Sym) (args : List (Identifier × Pattern))

/-- Pattern with type annotation and location
    Corresponds to: pattern in terms.ml lines 74-76
    Audited: 2025-01-17
    Deviations: None -/
inductive Pattern where
  | mk (pat : Pattern_) (bt : BaseType) (loc : Loc)

/-- Index terms - the expression language for CN specifications
    Corresponds to: term in terms.ml lines 80-132
    Audited: 2025-01-17
    Deviations: None significant -/
inductive Term where
  /-- Constant value -/
  | const (c : Const)
  /-- Variable reference -/
  | sym (s : Sym)
  /-- Unary operation -/
  | unop (op : UnOp) (arg : AnnotTerm)
  /-- Binary operation -/
  | binop (op : BinOp) (left : AnnotTerm) (right : AnnotTerm)
  /-- If-then-else -/
  | ite (cond : AnnotTerm) (thenBranch : AnnotTerm) (elseBranch : AnnotTerm)
  /-- Bounded universal quantification: each i in [lo..hi]. body -/
  | eachI (lo : Int) (var : Sym × BaseType) (hi : Int) (body : AnnotTerm)
  /-- Tuple construction -/
  | tuple (elems : List AnnotTerm)
  /-- Tuple projection -/
  | nthTuple (n : Nat) (tup : AnnotTerm)
  /-- Struct construction -/
  | struct_ (tag : Sym) (members : List (Identifier × AnnotTerm))
  /-- Struct member access -/
  | structMember (obj : AnnotTerm) (member : Identifier)
  /-- Struct member update -/
  | structUpdate (obj : AnnotTerm) (member : Identifier) (value : AnnotTerm)
  /-- Record construction -/
  | record (members : List (Identifier × AnnotTerm))
  /-- Record member access -/
  | recordMember (obj : AnnotTerm) (member : Identifier)
  /-- Record member update -/
  | recordUpdate (obj : AnnotTerm) (member : Identifier) (value : AnnotTerm)
  /-- Datatype constructor -/
  | constructor (constr : Sym) (args : List (Identifier × AnnotTerm))
  /-- Member shift: &ptr->member -/
  | memberShift (ptr : AnnotTerm) (tag : Sym) (member : Identifier)
  /-- Array shift: &ptr[index] -/
  | arrayShift (base : AnnotTerm) (ct : Ctype) (index : AnnotTerm)
  /-- Copy allocation ID from one pointer to another -/
  | copyAllocId (addr : AnnotTerm) (loc : AnnotTerm)
  /-- Check if pointer has allocation ID -/
  | hasAllocId (ptr : AnnotTerm)
  /-- Size of a C type -/
  | sizeOf (ct : Ctype)
  /-- Offset of a struct member -/
  | offsetOf (tag : Sym) (member : Identifier)
  /-- Empty list -/
  | nil (elemType : BaseType)
  /-- List cons -/
  | cons (head : AnnotTerm) (tail : AnnotTerm)
  /-- List head -/
  | head (list : AnnotTerm)
  /-- List tail -/
  | tail (list : AnnotTerm)
  /-- Check if value is representable in C type -/
  | representable (ct : Ctype) (value : AnnotTerm)
  /-- Check if value is a "good" (valid) value of C type -/
  | good (ct : Ctype) (value : AnnotTerm)
  /-- Check alignment -/
  | aligned (ptr : AnnotTerm) (align : AnnotTerm)
  /-- Wrap integer to type range -/
  | wrapI (intType : IntegerType) (value : AnnotTerm)
  /-- Constant map: all keys map to same value -/
  | mapConst (keyType : BaseType) (value : AnnotTerm)
  /-- Map update: m[k := v] -/
  | mapSet (map : AnnotTerm) (key : AnnotTerm) (value : AnnotTerm)
  /-- Map lookup: m[k] -/
  | mapGet (map : AnnotTerm) (key : AnnotTerm)
  /-- Map comprehension: [k -> body] -/
  | mapDef (var : Sym × BaseType) (body : AnnotTerm)
  /-- Function/predicate application -/
  | apply (fn : Sym) (args : List AnnotTerm)
  /-- Let binding -/
  | let_ (var : Sym) (binding : AnnotTerm) (body : AnnotTerm)
  /-- Pattern matching -/
  | match_ (scrutinee : AnnotTerm) (cases : List (Pattern × AnnotTerm))
  /-- Type cast -/
  | cast (targetType : BaseType) (value : AnnotTerm)
  /-- Option.None -/
  | cnNone (innerType : BaseType)
  /-- Option.Some -/
  | cnSome (value : AnnotTerm)
  /-- Check if option is Some -/
  | isSome (opt : AnnotTerm)
  /-- Extract value from Some -/
  | getOpt (opt : AnnotTerm)

/-- Annotated index term with type and location
    Corresponds to: annot in terms.ml lines 134-135
    ```ocaml
    and 'bt annot =
      | IT of 'bt term * 'bt * Locations.t
    ```
    Audited: 2025-01-17
    Deviations: None -/
inductive AnnotTerm where
  | mk (term : Term) (bt : BaseType) (loc : Loc)

end

-- Provide accessor functions for Pattern
namespace Pattern
def pat : Pattern → Pattern_
  | .mk p _ _ => p
def bt : Pattern → BaseType
  | .mk _ b _ => b
def loc : Pattern → Loc
  | .mk _ _ l => l
end Pattern

-- Provide accessor functions for AnnotTerm
namespace AnnotTerm
def term : AnnotTerm → Term
  | .mk t _ _ => t
def bt : AnnotTerm → BaseType
  | .mk _ b _ => b
def loc : AnnotTerm → Loc
  | .mk _ _ l => l
end AnnotTerm

-- Inhabited instances
instance : Inhabited Pattern_ where
  default := .wild

instance : Inhabited Pattern where
  default := .mk .wild .unit default

instance : Inhabited Term where
  default := .const .unit

instance : Inhabited AnnotTerm where
  default := .mk (.const .unit) .unit default

/-! ## Index Term Aliases

Following CN convention, IndexTerms.t is the annotated term type.
-/

/-- Index term type alias (matching CN's IndexTerms.t)
    Corresponds to: IndexTerms.t in indexTerms.ml line 11 -/
abbrev IndexTerm := AnnotTerm

end CerbLean.CN
