/-
  CN Index Terms (Specification Expression Language)
  Corresponds to: cn/lib/terms.ml

  Index terms are the expression language used in CN specifications.
  They represent symbolic values used in preconditions, postconditions,
  assertions, and resource predicates.

  Audited: 2025-01-17 against cn/lib/terms.ml
  Deviations: None significant
-/

import CerbLean.CN.Types.Base
import CerbLean.Core.Ctype
import CerbLean.Core.Annot

namespace CerbLean.CN.Types

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

/-! ## Free Variable Collection

Collect free variable symbol IDs from terms.
Corresponds to: IT.free_vars in cn/lib/indexTerms.ml
-/

mutual

/-- Collect free variable symbol IDs from a term.
    Corresponds to: IT.free_vars in indexTerms.ml -/
partial def Term.freeVarIds (t : Term) : List Nat :=
  match t with
  | .const _ => []
  | .sym s => [s.id]
  | .unop _ arg => arg.freeVarIds
  | .binop _ l r => l.freeVarIds ++ r.freeVarIds
  | .ite c t e => c.freeVarIds ++ t.freeVarIds ++ e.freeVarIds
  | .eachI _ (s, _) _ body =>
    body.freeVarIds.filter (· != s.id)
  | .tuple elems => elems.flatMap (·.freeVarIds)
  | .nthTuple _ tup => tup.freeVarIds
  | .struct_ _ members => members.flatMap fun (_, t) => t.freeVarIds
  | .structMember obj _ => obj.freeVarIds
  | .structUpdate obj _ value => obj.freeVarIds ++ value.freeVarIds
  | .record members => members.flatMap fun (_, t) => t.freeVarIds
  | .recordMember obj _ => obj.freeVarIds
  | .recordUpdate obj _ value => obj.freeVarIds ++ value.freeVarIds
  | .constructor _ args => args.flatMap fun (_, t) => t.freeVarIds
  | .memberShift ptr _ _ => ptr.freeVarIds
  | .arrayShift base _ idx => base.freeVarIds ++ idx.freeVarIds
  | .copyAllocId addr loc => addr.freeVarIds ++ loc.freeVarIds
  | .hasAllocId ptr => ptr.freeVarIds
  | .sizeOf _ => []
  | .offsetOf _ _ => []
  | .nil _ => []
  | .cons head tail => head.freeVarIds ++ tail.freeVarIds
  | .head list => list.freeVarIds
  | .tail list => list.freeVarIds
  | .representable _ value => value.freeVarIds
  | .good _ value => value.freeVarIds
  | .aligned ptr align => ptr.freeVarIds ++ align.freeVarIds
  | .wrapI _ value => value.freeVarIds
  | .mapConst _ value => value.freeVarIds
  | .mapSet m k v => m.freeVarIds ++ k.freeVarIds ++ v.freeVarIds
  | .mapGet m k => m.freeVarIds ++ k.freeVarIds
  | .mapDef (s, _) body =>
    body.freeVarIds.filter (· != s.id)
  | .apply _ args => args.flatMap (·.freeVarIds)
  | .let_ var binding body =>
    binding.freeVarIds ++ body.freeVarIds.filter (· != var.id)
  | .match_ scrutinee cases =>
    scrutinee.freeVarIds ++ cases.flatMap fun (_, t) => t.freeVarIds
  | .cast _ value => value.freeVarIds
  | .cnNone _ => []
  | .cnSome value => value.freeVarIds
  | .isSome opt => opt.freeVarIds
  | .getOpt opt => opt.freeVarIds

/-- Collect free variable symbol IDs from an annotated term.
    Corresponds to: IT.free_vars on annot in indexTerms.ml -/
partial def AnnotTerm.freeVarIds (at_ : AnnotTerm) : List Nat :=
  match at_ with
  | .mk t _ _ => t.freeVarIds

end

/-! ## Term Substitution

Substitution replaces occurrences of a symbol with a term.
Corresponds to: IT.subst and IT.make_subst in cn/lib/indexTerms.ml

Audited: 2026-01-27 against cn/lib/indexTerms.ml
Updated: 2026-02-18 — added alpha-renaming for binding forms
-/

/-- Substitution: maps symbols to replacement terms.
    Corresponds to: Subst.t in indexTerms.ml
    The `relevant` field contains all symbol IDs that appear in the substitution
    (domain symbol IDs ∪ free variable IDs of range terms), used for
    capture-avoidance during alpha-renaming.
    Corresponds to: Subst.relevant in cn/lib/subst.ml -/
structure Subst where
  /-- Mapping from symbol IDs to replacement terms -/
  mapping : List (Nat × IndexTerm)
  /-- All relevant symbol IDs (domain ∪ free vars of range terms).
      Corresponds to: Subst.relevant in cn/lib/subst.ml lines 17-23 -/
  relevant : List Nat
  deriving Inhabited

namespace Subst

/-- Compute the relevant symbol IDs for a substitution mapping.
    Corresponds to: Subst.make in cn/lib/subst.ml lines 16-23 -/
private def computeRelevant (mapping : List (Nat × IndexTerm)) : List Nat :=
  mapping.flatMap fun (id, term) => id :: term.freeVarIds

/-- Create a substitution from a single symbol → term mapping -/
def single (s : Sym) (t : IndexTerm) : Subst :=
  let mapping := [(s.id, t)]
  { mapping, relevant := computeRelevant mapping }

/-- Create a substitution from a list of (symbol ID, term) pairs -/
def fromMapping (mapping : List (Nat × IndexTerm)) : Subst :=
  { mapping, relevant := computeRelevant mapping }

/-- Look up a symbol in the substitution -/
def lookup (subst : Subst) (s : Sym) : Option IndexTerm :=
  subst.mapping.lookup s.id

end Subst

/-! ## Alpha-Renaming

Capture-avoiding substitution requires alpha-renaming bound variables
that conflict with the substitution.
Corresponds to: IT.suitably_alpha_rename in cn/lib/indexTerms.ml lines 351-355
-/

/-- Create a fresh symbol based on an existing one, with an ID not in the given set.
    Corresponds to: Sym.fresh_same in cn/lib/sym.ml line 50 -/
def freshSymFor (s : Sym) (relevantIds : List Nat) : Sym :=
  let maxId := relevantIds.foldl (fun acc id => max acc id) s.id
  { s with id := maxId + 1 }

/-- Create a rename-only substitution: replaces `from` with `to_` (as a variable).
    Corresponds to: IT.make_rename in cn/lib/indexTerms.ml line 271 -/
private def makeRename (from_ to_ : Sym) (loc : Loc) (bt : BaseType) : Subst :=
  Subst.single from_ (AnnotTerm.mk (.sym to_) bt loc)

mutual

/-- Alpha-rename a bound variable if it conflicts with the substitution.
    Returns (possibly-renamed symbol, possibly-renamed body).
    Corresponds to: IT.suitably_alpha_rename in indexTerms.ml lines 351-355 -/
partial def suitablyAlphaRename (relevant : List Nat) (s : Sym) (body : AnnotTerm)
    : Sym × AnnotTerm :=
  if relevant.contains s.id then
    -- Bound variable conflicts with substitution — alpha-rename
    -- Corresponds to: IT.alpha_rename in indexTerms.ml lines 346-348
    let s' := freshSymFor s relevant
    let renameSubst := makeRename s s' body.loc body.bt
    (s', body.subst renameSubst)
  else
    (s, body)

/-- Alpha-rename pattern-bound variables that conflict with the substitution.
    Corresponds to: IT.suitably_alpha_rename_pattern in indexTerms.ml lines 363-378 -/
partial def suitablyAlphaRenamePattern (relevant : List Nat) (pat : Pattern) (body : AnnotTerm)
    : Pattern × AnnotTerm :=
  match pat with
  | .mk (.sym s) bt loc =>
    let (s', body') := suitablyAlphaRename relevant s body
    (.mk (.sym s') bt loc, body')
  | .mk .wild _ _ => (pat, body)
  | .mk (.constructor constr args) bt loc =>
    let (body', args') := args.foldl (fun (body, acc) (id, pat') =>
      let (pat'', body') := suitablyAlphaRenamePattern relevant pat' body
      (body', acc ++ [(id, pat'')])
    ) (body, [])
    (.mk (.constructor constr args') bt loc, body')

/-- Substitute in a term.
    Corresponds to: IT.subst in indexTerms.ml -/
partial def Term.subst (σ : Subst) (t : Term) : Term :=
  match t with
  | .const c => .const c
  | .sym s =>
    match σ.lookup s with
    | some replacement => replacement.term
    | none => .sym s
  | .unop op arg => .unop op (arg.subst σ)
  | .binop op l r => .binop op (l.subst σ) (r.subst σ)
  | .ite c t e => .ite (c.subst σ) (t.subst σ) (e.subst σ)
  | .eachI lo (s, sBt) hi body =>
    -- Corresponds to: indexTerms.ml lines 295-297
    let (s', body') := suitablyAlphaRename σ.relevant s body
    .eachI lo (s', sBt) hi (body'.subst σ)
  | .tuple elems => .tuple (elems.map (·.subst σ))
  | .nthTuple n tup => .nthTuple n (tup.subst σ)
  | .struct_ tag members => .struct_ tag (members.map fun (id, t) => (id, t.subst σ))
  | .structMember obj member => .structMember (obj.subst σ) member
  | .structUpdate obj member value => .structUpdate (obj.subst σ) member (value.subst σ)
  | .record members => .record (members.map fun (id, t) => (id, t.subst σ))
  | .recordMember obj member => .recordMember (obj.subst σ) member
  | .recordUpdate obj member value => .recordUpdate (obj.subst σ) member (value.subst σ)
  | .constructor constr args => .constructor constr (args.map fun (id, t) => (id, t.subst σ))
  | .memberShift ptr tag member => .memberShift (ptr.subst σ) tag member
  | .arrayShift base ct idx => .arrayShift (base.subst σ) ct (idx.subst σ)
  | .copyAllocId addr loc => .copyAllocId (addr.subst σ) (loc.subst σ)
  | .hasAllocId ptr => .hasAllocId (ptr.subst σ)
  | .sizeOf ct => .sizeOf ct
  | .offsetOf tag member => .offsetOf tag member
  | .nil bt => .nil bt
  | .cons head tail => .cons (head.subst σ) (tail.subst σ)
  | .head list => .head (list.subst σ)
  | .tail list => .tail (list.subst σ)
  | .representable ct value => .representable ct (value.subst σ)
  | .good ct value => .good ct (value.subst σ)
  | .aligned ptr align => .aligned (ptr.subst σ) (align.subst σ)
  | .wrapI intTy value => .wrapI intTy (value.subst σ)
  | .mapConst keyTy value => .mapConst keyTy (value.subst σ)
  | .mapSet m k v => .mapSet (m.subst σ) (k.subst σ) (v.subst σ)
  | .mapGet m k => .mapGet (m.subst σ) (k.subst σ)
  | .mapDef (s, abt) body =>
    -- Corresponds to: indexTerms.ml lines 326-328
    let (s', body') := suitablyAlphaRename σ.relevant s body
    .mapDef (s', abt) (body'.subst σ)
  | .apply fn args => .apply fn (args.map (·.subst σ))
  | .let_ var binding body =>
    -- Corresponds to: indexTerms.ml lines 330-332
    let (var', body') := suitablyAlphaRename σ.relevant var body
    .let_ var' (binding.subst σ) (body'.subst σ)
  | .match_ scrutinee cases =>
    -- Corresponds to: indexTerms.ml lines 333-336
    .match_ (scrutinee.subst σ) (cases.map fun (p, t) =>
      let (p', t') := suitablyAlphaRenamePattern σ.relevant p t
      (p', t'.subst σ))
  | .cast targetTy value => .cast targetTy (value.subst σ)
  | .cnNone bt => .cnNone bt
  | .cnSome value => .cnSome (value.subst σ)
  | .isSome opt => .isSome (opt.subst σ)
  | .getOpt opt => .getOpt (opt.subst σ)

/-- Substitute in an annotated term.
    Corresponds to: IT.subst on annot in indexTerms.ml -/
partial def AnnotTerm.subst (σ : Subst) (at_ : AnnotTerm) : AnnotTerm :=
  match at_ with
  | .mk t bt loc => .mk (t.subst σ) bt loc

end

end CerbLean.CN.Types
