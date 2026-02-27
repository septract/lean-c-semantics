/-
  CN Constraint Simplification
  Corresponds to: cn/lib/simplify.ml

  Simplifies index terms before sending them to the SMT solver.
  Performs constant folding, boolean simplification, equality
  simplification, and accessor reduction (struct member, tuple nth).

  Audited: 2026-02-20 against cn/lib/simplify.ml
-/

import CerbLean.CN.Types
import CerbLean.Memory.Layout
import Std.Data.HashMap

namespace CerbLean.CN.TypeChecking.Simplify

open CerbLean.Core (Sym Identifier Loc Ctype Ctype_ IntegerType)
open CerbLean.CN.Types
open CerbLean.Memory (TypeEnv sizeof_)

/-! ## Simplification Context

Corresponds to: simp_ctxt in cn/lib/simplify.ml:31-36
CN builds a simplification context from sym_eqs (typing.ml:112-114,
make_simp_ctxt) and the memory model (for sizeof evaluation).
-/

/-- Simplification context, threaded through the simplifier.
    Corresponds to: simp_ctxt in cn/lib/simplify.ml:31-36.
    - `symEqs`: maps symbol IDs to their known constant values
      (from constraints of the form `sym == value`).
      CN ref: simp_ctxt.sym_eqs, built by make_simp_ctxt (typing.ml:112-114)
    - `typeEnv`: tag definitions for sizeof/offsetof evaluation.
      CN ref: Memory.size_of_ctype used in simplify.ml:585 -/
structure SimCtxt where
  symEqs : Std.HashMap Nat IndexTerm := {}
  typeEnv : Option TypeEnv := none
  deriving Inhabited

/-- Empty simplification context (no symbol bindings, no type env). -/
def SimCtxt.empty : SimCtxt := {}

/-! ## Syntactic Equality

Term, AnnotTerm, Const, and BaseType are recursive types that don't derive BEq.
We need syntactic equality for simplifications like `Eq(x, x) -> true`
and `And(x, x) -> x`.
-/

/-- Syntactic equality for Const (Const doesn't derive BEq because it
    contains BaseType which is recursive). We compare all fields except
    BaseType (only used in the `.default` case, which we approximate). -/
def Const.synEq : Const → Const → Bool
  | .z v1, .z v2 => v1 == v2
  | .bits s1 w1 v1, .bits s2 w2 v2 => s1 == s2 && w1 == w2 && v1 == v2
  | .q n1 d1, .q n2 d2 => n1 == n2 && d1 == d2
  | .memByte m1, .memByte m2 => m1 == m2
  | .pointer p1, .pointer p2 => p1 == p2
  | .allocId i1, .allocId i2 => i1 == i2
  | .bool b1, .bool b2 => b1 == b2
  | .unit, .unit => true
  | .null, .null => true
  | .ctypeConst ct1, .ctypeConst ct2 => ct1 == ct2
  | .default bt1, .default bt2 => BaseType.beq bt1 bt2
  | _, _ => false

mutual

/-- Syntactic equality for Term (structural comparison).
    Ignores locations, compares structure only. -/
partial def Term.synEq : Term → Term → Bool
  | .const c1, .const c2 => Const.synEq c1 c2
  | .sym s1, .sym s2 => s1 == s2
  | .unop op1 a1, .unop op2 a2 => op1 == op2 && AnnotTerm.synEq a1 a2
  | .binop op1 l1 r1, .binop op2 l2 r2 =>
    op1 == op2 && AnnotTerm.synEq l1 l2 && AnnotTerm.synEq r1 r2
  | .ite c1 t1 e1, .ite c2 t2 e2 =>
    AnnotTerm.synEq c1 c2 && AnnotTerm.synEq t1 t2 && AnnotTerm.synEq e1 e2
  | .eachI lo1 (s1, _) hi1 body1, .eachI lo2 (s2, _) hi2 body2 =>
    lo1 == lo2 && hi1 == hi2 && s1 == s2 && AnnotTerm.synEq body1 body2
  | .tuple es1, .tuple es2 => listSynEq es1 es2
  | .nthTuple n1 t1, .nthTuple n2 t2 => n1 == n2 && AnnotTerm.synEq t1 t2
  | .struct_ tag1 ms1, .struct_ tag2 ms2 =>
    tag1 == tag2 && membersSynEq ms1 ms2
  | .structMember o1 m1, .structMember o2 m2 =>
    m1 == m2 && AnnotTerm.synEq o1 o2
  | .structUpdate o1 m1 v1, .structUpdate o2 m2 v2 =>
    m1 == m2 && AnnotTerm.synEq o1 o2 && AnnotTerm.synEq v1 v2
  | .record ms1, .record ms2 => membersSynEq ms1 ms2
  | .recordMember o1 m1, .recordMember o2 m2 =>
    m1 == m2 && AnnotTerm.synEq o1 o2
  | .recordUpdate o1 m1 v1, .recordUpdate o2 m2 v2 =>
    m1 == m2 && AnnotTerm.synEq o1 o2 && AnnotTerm.synEq v1 v2
  | .constructor c1 args1, .constructor c2 args2 =>
    c1 == c2 && membersSynEq args1 args2
  | .memberShift p1 tag1 m1, .memberShift p2 tag2 m2 =>
    tag1 == tag2 && m1 == m2 && AnnotTerm.synEq p1 p2
  | .arrayShift b1 ct1 i1, .arrayShift b2 ct2 i2 =>
    ct1 == ct2 && AnnotTerm.synEq b1 b2 && AnnotTerm.synEq i1 i2
  | .copyAllocId a1 l1, .copyAllocId a2 l2 =>
    AnnotTerm.synEq a1 a2 && AnnotTerm.synEq l1 l2
  | .hasAllocId p1, .hasAllocId p2 => AnnotTerm.synEq p1 p2
  | .sizeOf ct1, .sizeOf ct2 => ct1 == ct2
  | .offsetOf tag1 m1, .offsetOf tag2 m2 => tag1 == tag2 && m1 == m2
  -- BaseType doesn't have BEq, so we skip type comparison for these cases.
  -- Structural term equality is sufficient for simplification purposes.
  | .nil _, .nil _ => true
  | .cons h1 t1, .cons h2 t2 => AnnotTerm.synEq h1 h2 && AnnotTerm.synEq t1 t2
  | .head l1, .head l2 => AnnotTerm.synEq l1 l2
  | .tail l1, .tail l2 => AnnotTerm.synEq l1 l2
  | .representable ct1 v1, .representable ct2 v2 =>
    ct1 == ct2 && AnnotTerm.synEq v1 v2
  | .good ct1 v1, .good ct2 v2 =>
    ct1 == ct2 && AnnotTerm.synEq v1 v2
  | .aligned p1 a1, .aligned p2 a2 =>
    AnnotTerm.synEq p1 p2 && AnnotTerm.synEq a1 a2
  | .wrapI it1 v1, .wrapI it2 v2 =>
    it1 == it2 && AnnotTerm.synEq v1 v2
  | .mapConst _ v1, .mapConst _ v2 =>
    AnnotTerm.synEq v1 v2
  | .mapSet m1 k1 v1, .mapSet m2 k2 v2 =>
    AnnotTerm.synEq m1 m2 && AnnotTerm.synEq k1 k2 && AnnotTerm.synEq v1 v2
  | .mapGet m1 k1, .mapGet m2 k2 =>
    AnnotTerm.synEq m1 m2 && AnnotTerm.synEq k1 k2
  | .mapDef (s1, _) b1, .mapDef (s2, _) b2 =>
    s1 == s2 && AnnotTerm.synEq b1 b2
  | .apply f1 args1, .apply f2 args2 =>
    f1 == f2 && listSynEq args1 args2
  | .let_ v1 bind1 body1, .let_ v2 bind2 body2 =>
    v1 == v2 && AnnotTerm.synEq bind1 bind2 && AnnotTerm.synEq body1 body2
  | .match_ scr1 cases1, .match_ scr2 cases2 =>
    AnnotTerm.synEq scr1 scr2 && casesSynEq cases1 cases2
  | .cast _ v1, .cast _ v2 =>
    AnnotTerm.synEq v1 v2
  | .cnNone _, .cnNone _ => true
  | .cnSome v1, .cnSome v2 => AnnotTerm.synEq v1 v2
  | .isSome o1, .isSome o2 => AnnotTerm.synEq o1 o2
  | .getOpt o1, .getOpt o2 => AnnotTerm.synEq o1 o2
  | _, _ => false

/-- Syntactic equality for AnnotTerm (ignores location, compares term structure).
    Note: BaseType doesn't have BEq, so we only compare term structure.
    This is sufficient for simplification since well-typed terms with equal
    structure necessarily have equal types. -/
partial def AnnotTerm.synEq : AnnotTerm → AnnotTerm → Bool
  | .mk t1 _ _, .mk t2 _ _ => Term.synEq t1 t2

/-- List equality helper -/
partial def listSynEq : List AnnotTerm → List AnnotTerm → Bool
  | [], [] => true
  | a :: as_, b :: bs => AnnotTerm.synEq a b && listSynEq as_ bs
  | _, _ => false

/-- Named member list equality helper -/
partial def membersSynEq : List (Identifier × AnnotTerm) → List (Identifier × AnnotTerm) → Bool
  | [], [] => true
  | (id1, t1) :: as_, (id2, t2) :: bs => id1 == id2 && AnnotTerm.synEq t1 t2 && membersSynEq as_ bs
  | _, _ => false

/-- Case list equality helper -/
partial def casesSynEq : List (Pattern × AnnotTerm) → List (Pattern × AnnotTerm) → Bool
  | [], [] => true
  | (_, t1) :: as_, (_, t2) :: bs =>
    -- Pattern equality is approximate (we skip it since patterns don't affect simplification much)
    AnnotTerm.synEq t1 t2 && casesSynEq as_ bs
  | _, _ => false

end

/-! ## Bitvector Normalization

Normalize a value to the representable range for a given bitvector type.
Corresponds to: BT.normalise_to_range in cn/lib/baseTypes.ml
-/

/-- Normalize an integer to the range of a bitvector type.
    For unsigned: value mod 2^width
    For signed: ((value + 2^(width-1)) mod 2^width) - 2^(width-1) -/
def normaliseToRange (sign : Sign) (width : Nat) (z : Int) : Int :=
  let card := bitsCardinality width
  match sign with
  | .unsigned =>
    z % card
  | .signed =>
    let halfCard := bitsCardinality (width - 1)
    ((z + halfCard) % card) - halfCard

/-! ## Helper: Extract numeric value from term

Corresponds to: IT.get_num_z in cn/lib/indexTerms.ml
Gets the numeric value from a constant term (Z or Bits).
-/

/-- Extract integer value from a constant term (Z or Bits).
    Returns none for non-numeric terms.
    For Bits values, normalizes to the representable range first.
    CN ref: IT.get_num_z in indexTerms.ml -/
def getNumZ (t : Term) : Option Int :=
  match t with
  | .const (.z v) => some v
  | .const (.bits sign width v) => some (normaliseToRange sign width v)
  | _ => none

/-! ## Term Simplification

Recursive bottom-up simplification.
Corresponds to: IndexTerms.simp in cn/lib/simplify.ml lines 215-637
Audited: 2026-02-20
-/

mutual

/-- Simplify an index term (recursive, bottom-up).
    CN ref: simplify.ml, IndexTerms.simp
    Audited: 2026-02-20 -/
partial def simplifyTerm (ctx : SimCtxt) (at_ : AnnotTerm) : AnnotTerm :=
  match at_ with
  | .mk t bt loc =>
    let result := simplifyTerm' ctx t bt loc
    result

/-- Inner simplification on Term, given the annotation context.
    Corresponds to: the big match in IndexTerms.simp (simplify.ml:220-637) -/
partial def simplifyTerm' (ctx : SimCtxt) (t : Term) (bt : BaseType) (loc : Loc) : AnnotTerm :=
  match t with
  -- Constants pass through unchanged
  -- CN ref: simplify.ml:226
  | .const _ => .mk t bt loc

  -- Symbols: replace with known constant value from context, then simplify
  -- CN ref: simplify.ml:221-225 (Sym.Map.find_opt sym simp_ctxt.sym_eqs)
  | .sym s =>
    match ctx.symEqs.get? s.id with
    | some value => simplifyTerm ctx value
    | none => .mk t bt loc

  -- Binary operations: simplify children first, then fold
  -- CN ref: simplify.ml:227-556
  | .binop op l r =>
    let l' := simplifyTerm ctx l
    let r' := simplifyTerm ctx r
    simplifyBinop op l' r' bt loc

  -- Unary operations
  -- CN ref: simplify.ml:409-438
  | .unop op arg =>
    let arg' := simplifyTerm ctx arg
    simplifyUnop op arg' bt loc

  -- If-then-else
  -- CN ref: simplify.ml:439-447
  | .ite cond thenBr elseBr =>
    let cond' := simplifyTerm ctx cond
    let then' := simplifyTerm ctx thenBr
    let else' := simplifyTerm ctx elseBr
    match cond'.term with
    | .const (.bool true) => then'
    | .const (.bool false) => else'
    | _ =>
      if AnnotTerm.synEq then' else' then then'
      else .mk (.ite cond' then' else') bt loc

  -- Tuple construction: simplify elements
  -- CN ref: simplify.ml:489-491
  | .tuple elems =>
    let elems' := elems.map (simplifyTerm ctx)
    .mk (.tuple elems') bt loc

  -- Tuple projection: simplify then reduce
  -- CN ref: simplify.ml:492-494
  | .nthTuple n tup =>
    let tup' := simplifyTerm ctx tup
    simplifyNthTuple n tup' bt loc

  -- Struct construction: simplify members + identity detection
  -- CN ref: simplify.ml:495-508
  | .struct_ tag members =>
    let members' := members.map fun (id, t) => (id, simplifyTerm ctx t)
    -- Check for struct identity: {.a = s.a, .b = s.b, ...} => s
    -- CN ref: simplify.ml:498-506
    match members'.head? with
    | some (_, firstTerm) =>
      match firstTerm.term with
      | .structMember srcObj _ =>
        if members'.all fun (memName, memTerm) =>
          match memTerm.term with
          | .structMember obj name => AnnotTerm.synEq obj srcObj && name == memName
          | _ => false
        then srcObj
        else .mk (.struct_ tag members') bt loc
      | _ => .mk (.struct_ tag members') bt loc
    | none => .mk (.struct_ tag members') bt loc

  -- Struct member access: simplify then reduce
  -- CN ref: simplify.ml:509-520
  | .structMember obj member =>
    let obj' := simplifyTerm ctx obj
    simplifyStructMember obj' member bt loc

  -- Struct update: simplify children
  -- CN ref: simplify.ml:521-524
  | .structUpdate obj member value =>
    let obj' := simplifyTerm ctx obj
    let val' := simplifyTerm ctx value
    .mk (.structUpdate obj' member val') bt loc

  -- Record construction: simplify members
  -- CN ref: simplify.ml:525-527
  | .record members =>
    let members' := members.map fun (id, t) => (id, simplifyTerm ctx t)
    .mk (.record members') bt loc

  -- Record member access: simplify then reduce
  -- CN ref: simplify.ml:528-530
  | .recordMember obj member =>
    let obj' := simplifyTerm ctx obj
    simplifyRecordMember obj' member bt loc

  -- Record update: simplify children
  -- CN ref: simplify.ml:531-534
  | .recordUpdate obj member value =>
    let obj' := simplifyTerm ctx obj
    let val' := simplifyTerm ctx value
    .mk (.recordUpdate obj' member val') bt loc

  -- EachI: simplify body
  -- CN ref: simplify.ml:484-488
  | .eachI lo var hi body =>
    let body' := simplifyTerm ctx body
    .mk (.eachI lo var hi body') bt loc

  -- Constructor: simplify args
  -- CN ref: simplify.ml:557-558
  | .constructor constr args =>
    let args' := args.map fun (id, t) => (id, simplifyTerm ctx t)
    .mk (.constructor constr args') bt loc

  -- MemberShift: simplify pointer
  -- CN ref: simplify.ml:570-571
  | .memberShift ptr tag member =>
    let ptr' := simplifyTerm ctx ptr
    .mk (.memberShift ptr' tag member) bt loc

  -- ArrayShift: simplify children
  -- CN ref: simplify.ml:572-584
  | .arrayShift base ct index =>
    let base' := simplifyTerm ctx base
    let index' := simplifyTerm ctx index
    -- If index is 0, just return the base
    match getNumZ index'.term with
    | some z => if z == 0 then base' else .mk (.arrayShift base' ct index') bt loc
    | none => .mk (.arrayShift base' ct index') bt loc

  -- SizeOf: evaluate to a concrete integer using memory layout
  -- CN ref: simplify.ml:585 (Memory.size_of_ctype ct)
  | .sizeOf ct =>
    match ctx.typeEnv with
    | some env =>
      match sizeof_ env ct.ty with
      | .ok n => .mk (.const (.z n)) bt loc
      | .error e => panic! s!"simplifyTerm: sizeof_ failed for {repr ct.ty}: {e}"
    | none => panic! s!"simplifyTerm: sizeOf encountered without typeEnv"

  -- OffsetOf: leave as-is
  | .offsetOf tag member => .mk (.offsetOf tag member) bt loc

  -- WrapI: simplify child, fold constant
  -- CN ref: simplify.ml:559-566
  | .wrapI ity value =>
    let val' := simplifyTerm ctx value
    match getNumZ val'.term with
    | some z => numLitNorm bt z loc
    | none => .mk (.wrapI ity val') bt loc

  -- Cast: simplify child, eliminate identity casts
  -- CN ref: simplify.ml:199-206 (cast_reduce)
  | .cast targetBt value =>
    let val' := simplifyTerm ctx value
    if BaseType.beq targetBt val'.bt then val'
    else .mk (.cast targetBt val') bt loc

  -- Nil, cons, head, tail: simplify children
  | .nil elemBt => .mk (.nil elemBt) bt loc
  | .cons head tail =>
    let h' := simplifyTerm ctx head
    let t' := simplifyTerm ctx tail
    .mk (.cons h' t') bt loc
  | .head list =>
    let list' := simplifyTerm ctx list
    .mk (.head list') bt loc
  | .tail list =>
    let list' := simplifyTerm ctx list
    .mk (.tail list') bt loc

  -- Representable, good, aligned: simplify children
  -- CN ref: simplify.ml:586-588
  | .representable ct value =>
    let val' := simplifyTerm ctx value
    .mk (.representable ct val') bt loc
  | .good ct value =>
    let val' := simplifyTerm ctx value
    .mk (.good ct val') bt loc
  | .aligned ptr align =>
    let ptr' := simplifyTerm ctx ptr
    let align' := simplifyTerm ctx align
    .mk (.aligned ptr' align') bt loc

  -- Map operations: simplify children
  -- CN ref: simplify.ml:589-624
  | .mapConst keyBt value =>
    let val' := simplifyTerm ctx value
    .mk (.mapConst keyBt val') bt loc
  | .mapSet map key value =>
    let map' := simplifyTerm ctx map
    let key' := simplifyTerm ctx key
    let val' := simplifyTerm ctx value
    .mk (.mapSet map' key' val') bt loc
  | .mapGet map key =>
    let map' := simplifyTerm ctx map
    let key' := simplifyTerm ctx key
    simplifyMapGet ctx map' key' bt loc
  | .mapDef var body =>
    let body' := simplifyTerm ctx body
    .mk (.mapDef var body') bt loc

  -- Apply: simplify args
  -- CN ref: simplify.ml:625-634
  | .apply fn args =>
    let args' := args.map (simplifyTerm ctx)
    .mk (.apply fn args') bt loc

  -- Let: simplify children
  | .let_ var binding body =>
    let bind' := simplifyTerm ctx binding
    let body' := simplifyTerm ctx body
    .mk (.let_ var bind' body') bt loc

  -- Match: simplify children
  | .match_ scrutinee cases =>
    let scr' := simplifyTerm ctx scrutinee
    let cases' := cases.map fun (p, t) => (p, simplifyTerm ctx t)
    .mk (.match_ scr' cases') bt loc

  -- CopyAllocId, hasAllocId: simplify children
  | .copyAllocId addr loc_ =>
    let addr' := simplifyTerm ctx addr
    let loc_' := simplifyTerm ctx loc_
    .mk (.copyAllocId addr' loc_') bt loc
  | .hasAllocId ptr =>
    let ptr' := simplifyTerm ctx ptr
    .mk (.hasAllocId ptr') bt loc

  -- Option operations: simplify children
  | .cnNone innerBt => .mk (.cnNone innerBt) bt loc
  | .cnSome value =>
    let val' := simplifyTerm ctx value
    .mk (.cnSome val') bt loc
  | .isSome opt =>
    let opt' := simplifyTerm ctx opt
    .mk (.isSome opt') bt loc
  | .getOpt opt =>
    let opt' := simplifyTerm ctx opt
    .mk (.getOpt opt') bt loc

/-- Simplify a binary operation (children already simplified).
    CN ref: simplify.ml:227-556 -/
partial def simplifyBinop (op : BinOp) (l r : AnnotTerm) (bt : BaseType) (loc : Loc) : AnnotTerm :=
  match op with
  -- Addition: constant folding and identity
  -- CN ref: simplify.ml:227-241
  | .add =>
    -- Q constant folding: Q(q1) + Q(q2) → Q(q1 + q2)
    -- CN ref: simplify.ml:232-233
    if let (.const (.q n1 d1), .const (.q n2 d2)) := (l.term, r.term) then
      .mk (.const (.q (n1 * d2 + n2 * d1) (d1 * d2))) bt loc
    else
    match getNumZ l.term, getNumZ r.term with
    | some i1, some i2 => numLitNorm bt (i1 + i2) loc
    | _, some z => if z == 0 then l else
      -- (c + i1) + i2 => c + (i1 + i2)
      -- CN ref: simplify.ml:236-240
      match l.term with
      | .binop .add c (.mk (.const (.z i1)) _ _) =>
        match r.term with
        | .const (.z i2) => .mk (.binop .add c (.mk (.const (.z (i1 + i2))) .integer loc)) bt loc
        | _ => .mk (.binop .add l r) bt loc
      | _ => .mk (.binop .add l r) bt loc
    | some z, _ => if z == 0 then r else .mk (.binop .add l r) bt loc
    | none, none => .mk (.binop .add l r) bt loc

  -- Subtraction: constant folding, identity, and self-cancellation
  -- CN ref: simplify.ml:242-255
  | .sub =>
    if AnnotTerm.synEq l r then
      match bt with
      | .integer => .mk (.const (.z 0)) bt loc
      | .real => .mk (.const (.q 0 1)) bt loc  -- CN ref: simplify.ml:247
      | _ => .mk (.binop .sub l r) bt loc
    else
      -- Q constant folding: Q(q1) - Q(q2) → Q(q1 - q2)
      -- CN ref: simplify.ml:249-250
      if let (.const (.q n1 d1), .const (.q n2 d2)) := (l.term, r.term) then
        .mk (.const (.q (n1 * d2 - n2 * d1) (d1 * d2))) bt loc
      else
      match getNumZ l.term, getNumZ r.term with
      | some i1, some i2 => numLitNorm bt (i1 - i2) loc
      | _, some z => if z == 0 then l else
        -- (c + d) - b when c = b => d
        -- CN ref: simplify.ml:252-254
        match l.term with
        | .binop .add c d =>
          if AnnotTerm.synEq c r then d
          else .mk (.binop .sub l r) bt loc
        | _ => .mk (.binop .sub l r) bt loc
      | _, _ => .mk (.binop .sub l r) bt loc

  -- Multiplication: constant folding, identity, and zero
  -- CN ref: simplify.ml:256-266
  | .mul =>
    match getNumZ l.term, getNumZ r.term with
    | some i1, some i2 => numLitNorm bt (i1 * i2) loc
    | some z, _ =>
      if z == 0 then .mk (.const (.z 0)) .integer loc
      else if z == 1 then r
      else .mk (.binop .mul l r) bt loc
    | _, some z =>
      if z == 0 then .mk (.const (.z 0)) .integer loc
      else if z == 1 then l
      else .mk (.binop .mul l r) bt loc
    | none, none => .mk (.binop .mul l r) bt loc

  -- Division: constant folding, identity
  -- CN ref: simplify.ml:267-277
  | .div =>
    match getNumZ l.term, getNumZ r.term with
    | some a, some b =>
      if b != 0 then .mk (.const (.z (a / b))) bt loc
      else .mk (.binop .div l r) bt loc
    | some z, _ =>
      if z == 0 then .mk (.const (.z 0)) .integer loc
      else .mk (.binop .div l r) bt loc
    | _, some z =>
      if z == 1 then l
      else .mk (.binop .div l r) bt loc
    | none, none => .mk (.binop .div l r) bt loc

  -- Exponentiation: constant folding
  -- CN ref: simplify.ml:278-286
  | .exp =>
    match getNumZ l.term, getNumZ r.term with
    | some a, some b =>
      if b >= 0 then numLitNorm bt (a ^ b.toNat) loc
      else .mk (.binop .exp l r) bt loc
    | _, _ => .mk (.binop .exp l r) bt loc

  -- Remainder: constant folding
  -- CN ref: simplify.ml:287-299
  | .rem =>
    match getNumZ l.term, getNumZ r.term with
    | some a, some b =>
      if a >= 0 && b > 0 then .mk (.const (.z (a % b))) bt loc
      else .mk (.binop .rem l r) bt loc
    | some z, _ =>
      if z == 0 then .mk (.const (.z 0)) .integer loc
      else .mk (.binop .rem l r) bt loc
    | _, some z =>
      if z == 1 then .mk (.const (.z 0)) .integer loc
      else .mk (.binop .rem l r) bt loc
    | none, none => .mk (.binop .rem l r) bt loc

  -- Modulo: constant folding
  -- CN ref: simplify.ml:300-314
  | .mod_ =>
    match getNumZ l.term, getNumZ r.term with
    | some a, some b =>
      if a >= 0 && b > 0 then numLitNorm bt (a % b) loc
      else .mk (.binop .mod_ l r) bt loc
    | some z, _ =>
      if z == 0 then numLitNorm bt 0 loc
      else .mk (.binop .mod_ l r) bt loc
    | _, some z =>
      if z == 1 then numLitNorm bt 0 loc
      else .mk (.binop .mod_ l r) bt loc
    | none, none => .mk (.binop .mod_ l r) bt loc

  -- Less-than: constant folding
  -- CN ref: simplify.ml:315-324
  | .lt =>
    match getNumZ l.term, getNumZ r.term with
    | some i1, some i2 => .mk (.const (.bool (i1 < i2))) bt loc
    | _, _ => .mk (.binop .lt l r) bt loc

  -- Less-or-equal: constant folding, self-equality, and Rem/Mod special case
  -- CN ref: simplify.ml:325-344
  | .le =>
    match getNumZ l.term, getNumZ r.term with
    | some i1, some i2 => .mk (.const (.bool (decide (i1 ≤ i2)))) bt loc
    | _, _ =>
      if AnnotTerm.synEq l r then .mk (.const (.bool true)) bt loc
      else
        -- Rem/Mod special case: (x % n) <= (n-1) → true when n > 0
        -- CN ref: simplify.ml:334-343
        let isRemMod := match l.term with
          | .binop .rem _ (.mk (.const (.z z1)) _ _) => some z1
          | .binop .mod_ _ (.mk (.const (.z z1)) _ _) => some z1
          | _ => none
        match isRemMod, r.term with
        | some z1, .const (.z z2) =>
          if z1 > 0 && z2 > 0 && z1 == z2 + 1 then .mk (.const (.bool true)) bt loc
          else .mk (.binop .le l r) bt loc
        | _, _ => .mk (.binop .le l r) bt loc

  -- Min: constant folding and self-equality
  -- CN ref: simplify.ml:345-360
  | .min =>
    if AnnotTerm.synEq l r then l
    else match getNumZ l.term, getNumZ r.term with
    | some i1, some i2 => numLitNorm bt (if i1 ≤ i2 then i1 else i2) loc
    | _, _ => .mk (.binop .min l r) bt loc

  -- Max: constant folding and self-equality
  -- CN ref: simplify.ml:361-376
  | .max =>
    if AnnotTerm.synEq l r then l
    else match getNumZ l.term, getNumZ r.term with
    | some i1, some i2 => numLitNorm bt (if i1 ≥ i2 then i1 else i2) loc
    | _, _ => .mk (.binop .max l r) bt loc

  -- Logical AND: short-circuit and identity
  -- CN ref: simplify.ml:377-386
  | .and_ =>
    match l.term, r.term with
    | .const (.bool true), _ => r
    | _, .const (.bool true) => l
    | .const (.bool false), _ => .mk (.const (.bool false)) bt loc
    | _, .const (.bool false) => .mk (.const (.bool false)) bt loc
    | _, _ =>
      if AnnotTerm.synEq l r then l
      else .mk (.binop .and_ l r) bt loc

  -- Logical OR: short-circuit and identity
  -- CN ref: simplify.ml:387-396
  | .or_ =>
    match l.term, r.term with
    | .const (.bool true), _ => .mk (.const (.bool true)) bt loc
    | _, .const (.bool true) => .mk (.const (.bool true)) bt loc
    | .const (.bool false), _ => r
    | _, .const (.bool false) => l
    | _, _ =>
      if AnnotTerm.synEq l r then l
      else .mk (.binop .or_ l r) bt loc

  -- Implies: simplification
  -- CN ref: simplify.ml:397-408
  | .implies =>
    if AnnotTerm.synEq l r then .mk (.const (.bool true)) bt loc
    else match l.term, r.term with
    | .const (.bool false), _ => .mk (.const (.bool true)) bt loc
    | _, .const (.bool true) => .mk (.const (.bool true)) bt loc
    | .const (.bool true), _ => r
    | _, .const (.bool false) =>
      -- implies(a, false) => not(a)
      .mk (.unop .not l) bt loc
    | _, _ => .mk (.binop .implies l r) bt loc

  -- Equality: constant folding, syntactic equality
  -- CN ref: simplify.ml:448-483
  | .eq =>
    if AnnotTerm.synEq l r then .mk (.const (.bool true)) bt loc
    else match l.term, r.term with
    | .const (.z z1), .const (.z z2) =>
      .mk (.const (.bool (z1 == z2))) bt loc
    | .const (.bits s1 w1 z1), .const (.bits s2 w2 z2) =>
      let v1 := normaliseToRange s1 w1 z1
      let v2 := normaliseToRange s2 w2 z2
      .mk (.const (.bool (v1 == v2))) bt loc
    | .const (.bool b1), .const (.bool b2) =>
      .mk (.const (.bool (b1 == b2))) bt loc
    | .const (.pointer p1), .const (.pointer p2) =>
      .mk (.const (.bool (p1 == p2))) bt loc
    | .const .null, .const .null =>
      .mk (.const (.bool true)) bt loc
    | .const .unit, .const .unit =>
      .mk (.const (.bool true)) bt loc
    | _, _ => .mk (.binop .eq l r) bt loc

  -- Pointer comparisons: self-equality
  -- CN ref: simplify.ml:536-555
  | .ltPointer =>
    if AnnotTerm.synEq l r then .mk (.const (.bool false)) bt loc
    else .mk (.binop .ltPointer l r) bt loc
  | .lePointer =>
    if AnnotTerm.synEq l r then .mk (.const (.bool true)) bt loc
    else .mk (.binop .lePointer l r) bt loc

  -- All other binops: just simplify children (already done)
  -- CN ref: simplify.ml:556
  | _ => .mk (.binop op l r) bt loc

/-- Simplify a unary operation (child already simplified).
    CN ref: simplify.ml:409-438 -/
partial def simplifyUnop (op : UnOp) (arg : AnnotTerm) (bt : BaseType) (loc : Loc) : AnnotTerm :=
  match op, arg.term with
  -- Not(true) => false, Not(false) => true
  | .not, .const (.bool b) => .mk (.const (.bool (!b))) bt loc
  -- Not(Not(x)) => x
  | .not, .unop .not inner => inner
  -- Negate(Negate(x)) => x
  | .negate, .unop .negate inner => inner
  -- Negate(Z z) => Z (-z)
  | .negate, .const (.z z) => .mk (.const (.z (-z))) bt loc
  -- Negate(Bits(sign, width, z)) => normalized Bits
  | .negate, .const (.bits _sign _width z) =>
    numLitNorm bt (-z) loc
  -- Negate(Q(n, d)) => Q(-n, d)
  -- CN ref: simplify.ml:418
  | .negate, .const (.q n d) =>
    .mk (.const (.q (-n) d)) bt loc
  | _, _ => .mk (.unop op arg) bt loc

/-- Simplify NthTuple: reduce Tuple projection.
    CN ref: simplify.ml:174-180, 492-494 -/
partial def simplifyNthTuple (n : Nat) (tup : AnnotTerm) (bt : BaseType) (loc : Loc) : AnnotTerm :=
  match tup.term with
  | .tuple items =>
    match items[n]? with
    | some item => item
    | none => .mk (.nthTuple n tup) bt loc
  -- (if cond then t1 else t2).n => if cond then t1.n else t2.n
  -- CN ref: simplify.ml:178-179
  | .ite cond t1 t2 =>
    let branch1 := simplifyNthTuple n t1 bt loc
    let branch2 := simplifyNthTuple n t2 bt loc
    .mk (.ite cond branch1 branch2) bt loc
  | _ => .mk (.nthTuple n tup) bt loc

/-- Simplify StructMember: reduce Struct member access.
    CN ref: simplify.ml:509-520 -/
partial def simplifyStructMember (obj : AnnotTerm) (member : Identifier) (bt : BaseType) (loc : Loc) : AnnotTerm :=
  match obj.term with
  | .struct_ _ members =>
    match members.find? fun (id, _) => id == member with
    | some (_, value) => value
    | none => .mk (.structMember obj member) bt loc
  -- (if cond then s1 else s2).member => if cond then s1.member else s2.member
  -- CN ref: simplify.ml:515-517
  | .ite cond t1 t2 =>
    let branch1 := simplifyStructMember t1 member bt loc
    let branch2 := simplifyStructMember t2 member bt loc
    .mk (.ite cond branch1 branch2) bt loc
  | _ => .mk (.structMember obj member) bt loc

/-- Simplify RecordMember: reduce Record member access.
    CN ref: simplify.ml:145-159, 528-530 -/
partial def simplifyRecordMember (obj : AnnotTerm) (member : Identifier) (bt : BaseType) (loc : Loc) : AnnotTerm :=
  match obj.term with
  | .record members =>
    match members.find? fun (id, _) => id == member with
    | some (_, value) => value
    | none => .mk (.recordMember obj member) bt loc
  -- RecordUpdate: if updating this member, return the value; otherwise look deeper
  -- CN ref: simplify.ml:149-153
  | .recordUpdate inner m value =>
    if m == member then value
    else simplifyRecordMember inner member bt loc
  -- (if cond then r1 else r2).member => if cond then r1.member else r2.member
  -- CN ref: simplify.ml:154-155
  | .ite cond t1 t2 =>
    let branch1 := simplifyRecordMember t1 member bt loc
    let branch2 := simplifyRecordMember t2 member bt loc
    .mk (.ite cond branch1 branch2) bt loc
  | _ => .mk (.recordMember obj member) bt loc

/-- Simplify MapGet: reduce map lookups through MapDef and MapSet.
    CN ref: simplify.ml:598-618 -/
partial def simplifyMapGet (ctx : SimCtxt) (map : AnnotTerm) (index : AnnotTerm) (bt : BaseType) (loc : Loc) : AnnotTerm :=
  match map.term with
  -- MapDef: substitute the index for the variable
  -- CN ref: simplify.ml:602-604
  | .mapDef (s, _) body =>
    let substituted := body.subst (Subst.single s index)
    simplifyTerm ctx substituted
  -- MapSet: check if index matches
  -- CN ref: simplify.ml:605-610
  | .mapSet innerMap index' value =>
    if AnnotTerm.synEq index index' then value
    else
      -- If both are distinct integer constants, look deeper
      match getNumZ index.term, getNumZ index'.term with
      | some z1, some z2 =>
        if z1 != z2 then simplifyMapGet ctx innerMap index bt loc
        else .mk (.mapGet map index) bt loc
      | _, _ => .mk (.mapGet map index) bt loc
  | _ => .mk (.mapGet map index) bt loc

/-- Create a numeric literal with normalization for bitvector types.
    CN ref: simplify.ml:209-212 (num_lit_norm) -/
partial def numLitNorm (bt : BaseType) (z : Int) (loc : Loc) : AnnotTerm :=
  match bt with
  | .bits sign width =>
    let normalized := normaliseToRange sign width z
    .mk (.const (.bits sign width normalized)) bt loc
  | _ => .mk (.const (.z z)) bt loc

end

/-! ## Logical Constraint Simplification

Corresponds to: LogicalConstraints.simp in cn/lib/simplify.ml:650-661
Audited: 2026-02-20
-/

/-- Simplify a logical constraint.
    CN ref: simplify.ml, LogicalConstraints.simp
    Audited: 2026-02-20 -/
def simplifyConstraint (ctx : SimCtxt) (lc : LogicalConstraint) : LogicalConstraint :=
  match lc with
  | .t term => .t (simplifyTerm ctx term)
  | .forall_ (q, qbt) body =>
    let body' := simplifyTerm ctx body
    -- If body simplifies to true, the forall is trivially satisfied
    -- CN ref: simplify.ml:659-661
    match body'.term with
    | .const (.bool true) => .t (.mk (.const (.bool true)) .bool body'.loc)
    | _ => .forall_ (q, qbt) body'

end CerbLean.CN.TypeChecking.Simplify
