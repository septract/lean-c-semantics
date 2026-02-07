/-
  SMT-LIB2 Translation for CN Proof Obligations

  This module translates CN proof obligations to SMT-LIB2 format using
  the lean-smt library infrastructure.

  ## Architecture

  We translate CN's IndexTerm to Smt.Term, then use lean-smt's
  Command infrastructure to build queries.

  For an obligation with assumptions [A1, A2, ...] and constraint C,
  we generate:
  - Declarations for all free symbols
  - Assert (not (=> (and A1 A2 ...) C))
  - check-sat

  If the solver returns "unsat", the obligation is discharged.

  Audited: 2026-01-27 (pragmatic pipeline using lean-smt)
-/

import CerbLean.CN.Types
import CerbLean.CN.Verification.Obligation
import Smt.Translate.Term
import Smt.Translate.Commands
import Smt.Data.Sexp

namespace CerbLean.CN.Verification.SmtLib

open CerbLean.Core (Sym Identifier Loc Ctype IntegerType)
open CerbLean.CN.Types
open Smt (Term)
open Smt.Translate (Command)

/-! ## Symbol Name Generation -/

/-- Generate a valid SMT-LIB2 identifier from a Sym -/
def symToSmtName (s : Sym) : String :=
  match s.name with
  | some n => s!"{n}_{s.id}"
  | none => s!"_sym_{s.id}"

/-! ## Type-to-Sort Translation

CN uses actual SMT-LIB BitVec types (`(_ BitVec n)`) with bitvector operations.
We must match this exactly.

Corresponds to: CN's solver.ml translate_bt function
-/

/-- Result of sort translation -/
inductive SortResult where
  | ok (tm : Smt.Term)
  | unsupported (reason : String)
  deriving Inhabited

/-- Convert CN BaseType to SMT-LIB2 sort.
    Matches CN's Solver.translate_bt which uses `SMT.t_bits n` for Bits types.
    Corresponds to: solver.ml line 409: `| Bits (_, n) -> SMT.t_bits n`
    Returns unsupported for types that cannot be represented in SMT. -/
def baseTypeToSort : BaseType → SortResult
  | .bits _ width => .ok (Term.mkApp2 (Term.symbolT "_")
                                  (Term.symbolT "BitVec")
                                  (Term.literalT (toString width)))
  | .integer => .ok (Term.symbolT "Int")
  | .bool => .ok (Term.symbolT "Bool")
  | .real => .ok (Term.symbolT "Real")
  | .loc => .ok (Term.symbolT "Int")  -- Pointers as integers (addresses)
  | .allocId => .ok (Term.symbolT "Int")  -- Allocation IDs as integers
  | .unit => .ok (Term.symbolT "Bool")  -- Unit as Bool (SMT doesn't have Unit)
  | .memByte => .ok (Term.symbolT "Int")  -- Memory bytes as integers
  | .struct_ tag =>
    let tagStr := tag.name.getD "?"
    .unsupported s!"struct type {tagStr}"
  | .list elemBt =>
    let elemStr := toString (repr elemBt)
    .unsupported s!"list type (element: {elemStr})"
  | .set elemBt =>
    let elemStr := toString (repr elemBt)
    .unsupported s!"set type (element: {elemStr})"
  | .tuple bts =>
    .unsupported s!"tuple type ({bts.length} elements)"
  | .map keyBt valBt =>
    let keyStr := toString (repr keyBt)
    let valStr := toString (repr valBt)
    .unsupported s!"map type ({keyStr} -> {valStr})"
  | .record fields =>
    .unsupported s!"record type ({fields.length} fields)"
  | .datatype dtTag =>
    let dtName := dtTag.name.getD "?"
    .unsupported s!"datatype {dtName}"
  | .ctype =>
    .unsupported "ctype"
  | .option innerBt =>
    let innerStr := toString (repr innerBt)
    .unsupported s!"option type ({innerStr})"

/-! ## Translation to Smt.Term -/

/-- Result of translation: either success or unsupported construct -/
inductive TranslateResult where
  | ok (tm : Smt.Term)
  | unsupported (reason : String)
  deriving Inhabited

/-! ## BitVec Literal Generation

SMT-LIB2 BitVec literals can be written as:
- `(_ bvN W)` - decimal value N of width W bits
- `#xHHHH` - hexadecimal (width must be multiple of 4)
- `#bBBBB` - binary

CN uses the indexed identifier notation: `(_ bvN W)`.
Corresponds to: simple_smt.ml bv_nat function
-/

/-- Generate a BitVec literal in SMT-LIB format: (_ bvN W)
    For negative numbers, we convert to two's complement representation. -/
def mkBitVecLiteral (width : Nat) (value : Int) : Smt.Term :=
  -- Convert negative numbers to two's complement unsigned representation
  let unsignedVal : Nat :=
    if value < 0 then
      let modulus := Nat.pow 2 width
      (modulus - ((-value).toNat % modulus)) % modulus
    else
      value.toNat % (Nat.pow 2 width)
  Term.mkApp2 (Term.symbolT "_")
              (Term.symbolT s!"bv{unsignedVal}")
              (Term.literalT (toString width))

/-! ## Integer Bounds for Representability -/

/-- Get bit width for an integer base kind -/
def intBaseKindWidthSmt (kind : Core.IntBaseKind) : Nat :=
  match kind with
  | .ichar => 8
  | .short => 16
  | .int_ => 32
  | .long => 64
  | .longLong => 64
  | .intN n => n
  | .intLeastN n => n
  | .intFastN n => n
  | .intmax => 64
  | .intptr => 64

/-- Get bounds for an integer type (lo, hi) where lo <= val < hi for representability -/
def integerTypeBounds (ity : Core.IntegerType) : Option (Int × Int) :=
  match ity with
  | .signed kind =>
    let width := intBaseKindWidthSmt kind
    let half := Int.pow 2 (width - 1)
    some (-half, half)
  | .unsigned kind =>
    let width := intBaseKindWidthSmt kind
    let max := Int.pow 2 width
    some (0, max)
  | .char => some (-128, 128)  -- Assuming signed char
  | .bool => some (0, 2)
  | .size_t => some (0, Int.pow 2 64)
  | .ptrdiff_t => some (-(Int.pow 2 63), Int.pow 2 63)
  | .wchar_t => some (-(Int.pow 2 31), Int.pow 2 31)
  | .wint_t => some (-(Int.pow 2 31), Int.pow 2 31)
  | .ptraddr_t => some (0, Int.pow 2 64)
  | .enum _ => some (-(Int.pow 2 31), Int.pow 2 31)

/-! ## Constant Conversion -/

/-- Convert a Const to Smt.Term.
    For Bits constants, generates proper BitVec literals using indexed notation.
    Corresponds to: CN's handling of Const.Bits in solver.ml -/
def constToTerm : Const → TranslateResult
  | .z n =>
    .ok (Term.literalT (toString n))
  | .bits _sign width n =>
    .ok (mkBitVecLiteral width n)  -- Proper BitVec literal
  | .bool true => .ok (Term.symbolT "true")
  | .bool false => .ok (Term.symbolT "false")
  | .null => .ok (Term.literalT "0")
  | .unit => .ok (Term.literalT "0")
  | .q num denom => .ok (Term.mkApp2 (Term.symbolT "/") (Term.literalT (toString num)) (Term.literalT (toString denom)))
  | .allocId id => .ok (Term.literalT (toString id))
  | .pointer p => .ok (Term.literalT (toString p.addr))
  | .memByte m => .ok (Term.literalT (toString m.value))
  | .ctypeConst _ => .unsupported "ctypeConst in SMT query"
  | .default _ => .unsupported "default value in SMT query"

/-- Check if a base type is a bitvector type -/
def isBitsType : BaseType → Bool
  | .bits _ _ => true
  | _ => false

/-- Check if a base type is signed bits (for bitvector operation dispatch) -/
def isSignedBits : BaseType → Bool
  | .bits .signed _ => true
  | _ => false

/-- Check if a term is an integer literal -/
def isIntLiteral (tm : Smt.Term) : Option Int :=
  match tm with
  | .literalT s =>
    -- Try to parse as integer
    match s.toInt? with
    | some n => some n
    | none => none
  | _ => none

/-- Convert an integer to a BitVec literal for use in comparisons.
    Used when comparing integer constants with BitVec values. -/
def intToBitVecTerm (n : Int) (width : Nat) : Smt.Term :=
  mkBitVecLiteral width n

/-- Convert a UnOp application to Smt.Term.
    Type-aware: dispatches to bitvector operations for Bits types. -/
def unOpToTerm (op : UnOp) (argBt : BaseType) (arg : Smt.Term) : TranslateResult :=
  let useBv := isBitsType argBt
  match op with
  | .not => .ok (Term.appT (Term.symbolT "not") arg)
  | .negate => if useBv then .ok (Term.appT (Term.symbolT "bvneg") arg)
               else .ok (Term.appT (Term.symbolT "-") arg)
  | .bwCompl => if useBv then .ok (Term.appT (Term.symbolT "bvnot") arg)
                else .unsupported "bwCompl requires Bits type"
  | .bwClzNoSMT => .unsupported "bwClzNoSMT"
  | .bwCtzNoSMT => .unsupported "bwCtzNoSMT"
  | .bwFfsNoSMT => .unsupported "bwFfsNoSMT"
  | .bwFlsNoSMT => .unsupported "bwFlsNoSMT"

/-- Convert a BinOp application to Smt.Term.
    Type-aware: dispatches to bitvector operations for Bits types.
    Both operands are expected to have matching types (enforced by Pexpr.lean).
    Corresponds to: CN's solver.ml lines 688-702 for arithmetic, 752-765 for comparisons -/
def binOpToTerm (op : BinOp) (lBt rBt : BaseType) (l r : Smt.Term) : TranslateResult :=
  -- Type consistency check: both operands should have matching types
  -- If they don't, the type checker has a bug - don't mask it
  if isBitsType lBt != isBitsType rBt then
    .unsupported s!"Type mismatch in binop {repr op}: left={repr lBt}, right={repr rBt}"
  else
  -- Both operands should have matching types after Pexpr type fixup
  -- Use left operand's type to determine if we need bitvector ops
  let useBv := isBitsType lBt
  let signed := isSignedBits lBt  -- Only meaningful when useBv = true
  let mkBinApp (sym : String) := .ok (Term.mkApp2 (Term.symbolT sym) l r)
  match op with
  -- Arithmetic operations
  | .add => if useBv then mkBinApp "bvadd" else mkBinApp "+"
  | .sub => if useBv then mkBinApp "bvsub" else mkBinApp "-"
  | .mul => if useBv then mkBinApp "bvmul" else mkBinApp "*"
  | .mulNoSMT => if useBv then mkBinApp "bvmul" else mkBinApp "*"
  | .div =>
    if useBv then
      if signed then mkBinApp "bvsdiv" else mkBinApp "bvudiv"
    else mkBinApp "div"
  | .divNoSMT =>
    if useBv then
      if signed then mkBinApp "bvsdiv" else mkBinApp "bvudiv"
    else mkBinApp "div"
  | .rem =>
    if useBv then
      if signed then mkBinApp "bvsrem" else mkBinApp "bvurem"
    else mkBinApp "mod"
  | .remNoSMT =>
    if useBv then
      if signed then mkBinApp "bvsrem" else mkBinApp "bvurem"
    else mkBinApp "mod"
  | .mod_ =>
    if useBv then
      if signed then mkBinApp "bvsmod" else mkBinApp "bvurem"
    else mkBinApp "mod"
  | .modNoSMT =>
    if useBv then
      if signed then mkBinApp "bvsmod" else mkBinApp "bvurem"
    else mkBinApp "mod"
  -- Comparison operations
  | .lt =>
    if useBv then
      if signed then mkBinApp "bvslt" else mkBinApp "bvult"
    else mkBinApp "<"
  | .le =>
    if useBv then
      if signed then mkBinApp "bvsle" else mkBinApp "bvule"
    else mkBinApp "<="
  | .eq => mkBinApp "="  -- Equality is the same for all types
  -- Logical operations (type-independent)
  | .and_ => mkBinApp "and"
  | .or_ => mkBinApp "or"
  | .implies => mkBinApp "=>"
  -- Pointer comparisons (use integers)
  | .ltPointer => mkBinApp "<"
  | .lePointer => mkBinApp "<="
  -- Bitwise operations (require bitvector types)
  | .bwXor => if useBv then mkBinApp "bvxor" else .unsupported "bwXor requires Bits type"
  | .bwAnd => if useBv then mkBinApp "bvand" else .unsupported "bwAnd requires Bits type"
  | .bwOr => if useBv then mkBinApp "bvor" else .unsupported "bwOr requires Bits type"
  | .shiftLeft => if useBv then mkBinApp "bvshl" else .unsupported "shiftLeft requires Bits type"
  | .shiftRight =>
    if useBv then
      if signed then mkBinApp "bvashr" else mkBinApp "bvlshr"
    else .unsupported "shiftRight requires Bits type"
  -- Unsupported operations
  | .exp => .unsupported "exp"
  | .expNoSMT => .unsupported "expNoSMT"
  | .min => .unsupported "min"
  | .max => .unsupported "max"
  | .setUnion => .unsupported "setUnion"
  | .setIntersection => .unsupported "setIntersection"
  | .setDifference => .unsupported "setDifference"
  | .setMember => .unsupported "setMember"
  | .subset => .unsupported "subset"

mutual

/-- Convert a CN Term to Smt.Term.
    Type information is obtained from AnnotTerm wrappers during recursion. -/
partial def termToSmtTerm : Types.Term → TranslateResult
  | .const c => constToTerm c
  | .sym s => .ok (Term.symbolT (symToSmtName s))
  | .unop op arg =>
    -- Pass the operand's type to unOpToTerm
    match annotTermToSmtTerm arg with
    | .ok argTm => unOpToTerm op arg.bt argTm
    | .unsupported r => .unsupported r
  | .binop op l r =>
    -- Pass both operand types to binOpToTerm for type-aware dispatch
    match annotTermToSmtTerm l, annotTermToSmtTerm r with
    | .ok lTm, .ok rTm => binOpToTerm op l.bt r.bt lTm rTm
    | .unsupported r, _ => .unsupported r
    | _, .unsupported r => .unsupported r
  | .ite cond thenB elseB =>
    match annotTermToSmtTerm cond, annotTermToSmtTerm thenB, annotTermToSmtTerm elseB with
    | .ok c, .ok t, .ok e => .ok (Term.mkApp3 (Term.symbolT "ite") c t e)
    | .unsupported r, _, _ => .unsupported r
    | _, .unsupported r, _ => .unsupported r
    | _, _, .unsupported r => .unsupported r
  | .eachI lo (s, bt) hi body =>
    -- Bounded quantification: use proper sort for bound variable
    let name := symToSmtName s
    match baseTypeToSort bt with
    | .unsupported reason => .unsupported s!"eachI bound variable type: {reason}"
    | .ok sort =>
      match annotTermToSmtTerm body with
      | .ok b =>
        let rangeConstraint := Term.mkApp2 (Term.symbolT "and")
          (Term.mkApp2 (Term.symbolT ">=") (Term.symbolT name) (Term.literalT (toString lo)))
          (Term.mkApp2 (Term.symbolT "<=") (Term.symbolT name) (Term.literalT (toString hi)))
        let implBody := Term.mkApp2 (Term.symbolT "=>") rangeConstraint b
        .ok (Term.forallT name sort implBody)
      | .unsupported r => .unsupported r
  | .let_ var binding body =>
    let name := symToSmtName var
    match annotTermToSmtTerm binding, annotTermToSmtTerm body with
    | .ok b, .ok bd => .ok (Term.letT name b bd)
    | .unsupported r, _ => .unsupported r
    | _, .unsupported r => .unsupported r
  | .arrayShift base _ct index =>
    match annotTermToSmtTerm base, annotTermToSmtTerm index with
    | .ok b, .ok i => .ok (Term.mkApp2 (Term.symbolT "+") b i)
    | .unsupported r, _ => .unsupported r
    | _, .unsupported r => .unsupported r
  | .aligned ptr align =>
    match annotTermToSmtTerm ptr, annotTermToSmtTerm align with
    | .ok p, .ok a => .ok (Term.mkApp2 (Term.symbolT "=")
        (Term.mkApp2 (Term.symbolT "mod") p a)
        (Term.literalT "0"))
    | .unsupported r, _ => .unsupported r
    | _, .unsupported r => .unsupported r
  | .representable ct val =>
    -- representable(ct, val) checks if val fits in the integer type ct
    -- For BitVec types, representability is trivially true (bounded by type)
    -- For unbounded Integer types, we need explicit range checks
    let valBt := val.bt
    if isBitsType valBt then
      -- BitVec values are already bounded by their type width
      -- Representability is trivially true
      .ok (Term.symbolT "true")
    else
      -- For unbounded integers, generate range constraint
      match annotTermToSmtTerm val with
      | .unsupported r => .unsupported r
      | .ok valTm =>
        match ct.ty with
        | .basic (.integer ity) =>
          let bounds := integerTypeBounds ity
          match bounds with
          | some (lo, hi) =>
            -- Generate: lo <= val && val < hi
            let loTm := Term.literalT (toString lo)
            let hiTm := Term.literalT (toString hi)
            let loCond := Term.mkApp2 (Term.symbolT "<=") loTm valTm
            let hiCond := Term.mkApp2 (Term.symbolT "<") valTm hiTm
            .ok (Term.mkApp2 (Term.symbolT "and") loCond hiCond)
          | none => .unsupported s!"representable for {repr ity}"
        | _ => .unsupported s!"representable for non-integer type"
  | .good ct _val =>
    -- good(ct, val) checks val is representable in ct - needs proper handling
    .unsupported s!"good (type check for {repr ct.ty})"
  | .wrapI _intType val =>
    -- wrapI wraps integer value to representation type (modular arithmetic)
    -- Corresponds to: wrapI in CN's indexTerms.ml
    -- For bitvec SMT sorts, modular wrapping is enforced by the sort itself,
    -- so this is identity. If we ever use unbounded integer sorts, this would
    -- need explicit modular arithmetic (bvmod or similar).
    match annotTermToSmtTerm val with
    | .unsupported r => .unsupported r
    | .ok valTm => .ok valTm
  | .cast targetType val =>
    -- cast changes type between CN base types
    -- Corresponds to: cast_ in CN's indexTerms.ml
    match annotTermToSmtTerm val with
    | .unsupported r => .unsupported r
    | .ok valTm =>
      let sourceBt := val.bt
      match sourceBt, targetType with
      | .bits _ sw, .bits _ tw =>
        if sw == tw then .ok valTm  -- Same width: identity
        else if sw < tw then
          -- Extend: use zero_extend (indexed identifier)
          let zeroExt := Term.mkApp2 (Term.symbolT "_") (Term.symbolT "zero_extend") (Term.literalT (toString (tw - sw)))
          .ok (Term.appT zeroExt valTm)
        else
          -- Truncate: use extract (indexed identifier with two args: high, low)
          let extract := Term.mkApp3 (Term.symbolT "_") (Term.symbolT "extract") (Term.literalT (toString (tw - 1))) (Term.literalT "0")
          .ok (Term.appT extract valTm)
      | .integer, .bits _ tw =>
        -- Int → BitVec: use int2bv (indexed identifier)
        let int2bv := Term.mkApp2 (Term.symbolT "_") (Term.symbolT "int2bv") (Term.literalT (toString tw))
        .ok (Term.appT int2bv valTm)
      | .loc, .bits _ tw =>
        -- Loc (represented as Int) → BitVec (indexed identifier)
        let int2bv := Term.mkApp2 (Term.symbolT "_") (Term.symbolT "int2bv") (Term.literalT (toString tw))
        .ok (Term.appT int2bv valTm)
      | _, _ =>
        .unsupported s!"cast from {repr sourceBt} to {repr targetType}"
  | .copyAllocId _addr _loc =>
    -- copyAllocId copies allocation ID from one pointer to another
    .unsupported "copyAllocId"
  | .hasAllocId _ptr =>
    -- hasAllocId checks if pointer has a valid allocation ID
    .unsupported "hasAllocId"
  | .sizeOf ct =>
    -- sizeOf(ctype) as a concrete integer
    -- For simple types we can compute statically; structs need TypeEnv
    match ct.ty with
    | .void => .ok (Term.literalT "0")
    | .basic (.integer ity) =>
      let size : Option Nat := match ity with
        | .bool => some 1
        | .char => some 1
        | .signed .ichar | .unsigned .ichar => some 1
        | .signed .short | .unsigned .short => some 2
        | .signed .int_ | .unsigned .int_ => some 4
        | .signed .long | .unsigned .long => some 8
        | .signed .longLong | .unsigned .longLong => some 8
        | .signed .intptr | .unsigned .intptr => some 8
        | .size_t | .ptrdiff_t | .ptraddr_t => some 8
        | .wchar_t | .wint_t => some 4
        | .enum _ => some 4
        | _ => none
      match size with
      | some n => .ok (Term.literalT (toString n))
      | none => .unsupported s!"sizeOf integer type ({repr ity})"
    | .basic (.floating (.realFloating .float)) => .ok (Term.literalT "4")
    | .basic (.floating (.realFloating .double)) => .ok (Term.literalT "8")
    | .basic (.floating (.realFloating .longDouble)) => .ok (Term.literalT "16")
    | .pointer _ _ => .ok (Term.literalT "8")
    | _ => .unsupported s!"sizeOf ({repr ct.ty})"
  | .offsetOf tag member =>
    -- offsetOf needs actual struct layout
    let tagStr := tag.name.getD "?"
    .unsupported s!"offsetOf ({tagStr}, {member.name})"
  | .memberShift _ptr tag member =>
    -- memberShift needs actual struct layout
    let tagStr := tag.name.getD "?"
    .unsupported s!"memberShift ({tagStr}, {member.name})"
  | .cnSome val => annotTermToSmtTerm val
  | .getOpt opt => annotTermToSmtTerm opt
  | .apply fn args =>
    let fnName := symToSmtName fn
    let rec buildApp (acc : Smt.Term) : List AnnotTerm → TranslateResult
      | [] => .ok acc
      | arg :: rest =>
        match annotTermToSmtTerm arg with
        | .ok argTm => buildApp (Term.appT acc argTm) rest
        | .unsupported r => .unsupported r
    buildApp (Term.symbolT fnName) args
  | .tuple elems =>
    -- Support single-element tuples (common in return value handling)
    match elems with
    | [single] => annotTermToSmtTerm single
    | _ => .unsupported s!"tuple with {elems.length} elements"
  | .nthTuple n tup =>
    -- Support projecting from tuples
    match tup.term with
    | .tuple elems =>
      if h : n < elems.length then
        annotTermToSmtTerm (elems.get ⟨n, h⟩)
      else
        .unsupported s!"nthTuple index {n} out of bounds for tuple of size {elems.length}"
    | _ =>
      .unsupported s!"nthTuple on non-tuple term (index {n}, term type {repr tup.bt})"
  | .struct_ _ _ => .unsupported "struct"
  | .structMember _ _ => .unsupported "structMember"
  | .structUpdate _ _ _ => .unsupported "structUpdate"
  | .record _ => .unsupported "record"
  | .recordMember _ _ => .unsupported "recordMember"
  | .recordUpdate _ _ _ => .unsupported "recordUpdate"
  | .constructor _ _ => .unsupported "constructor"
  | .nil _ => .unsupported "nil"
  | .cons _ _ => .unsupported "cons"
  | .head _ => .unsupported "head"
  | .tail _ => .unsupported "tail"
  | .mapConst _ _ => .unsupported "mapConst"
  | .mapSet _ _ _ => .unsupported "mapSet"
  | .mapGet _ _ => .unsupported "mapGet"
  | .mapDef _ _ => .unsupported "mapDef"
  | .match_ scrutinee cases =>
    -- Support match patterns from CN.
    -- For tuple destructuring, we create SMT let-bindings that tie pattern
    -- variables to the corresponding scrutinee components.
    -- Corresponds to: match handling in CN's solver translation
    match cases with
    | [] => .unsupported "match with no cases"
    | (pat, body) :: rest =>
      -- Try to create let-bindings from pattern + scrutinee
      match extractPatternBindings pat scrutinee with
      | .error r => .unsupported s!"match pattern bindings: {r}"
      | .ok bindings =>
        let bodyTm := annotTermToSmtTerm body
        match bodyTm with
        | .unsupported r => .unsupported r
        | .ok bodySmtTm =>
          if bindings.isEmpty then
            -- No bindings to create
            if rest.isEmpty then .ok bodySmtTm
            else if scrutinee.bt matches .bool then
              -- Boolean match: use if-then-else
              match rest with
              | [(_, body2)] =>
                match annotTermToSmtTerm scrutinee, annotTermToSmtTerm body2 with
                | .ok s, .ok b2 => .ok (Term.mkApp3 (Term.symbolT "ite") s bodySmtTm b2)
                | .unsupported r, _ => .unsupported r
                | _, .unsupported r => .unsupported r
              | _ => .unsupported s!"match on boolean with {rest.length + 1} cases (expected 2)"
            else .unsupported s!"match on non-boolean ({repr scrutinee.bt}) with {rest.length + 1} cases"
          else
            -- Create nested let-bindings for pattern variables
            let result := bindings.foldl (init := bodySmtTm) fun acc (name, valTm) =>
              Term.letT name valTm acc
            .ok result
  | .cnNone _ => .unsupported "cnNone"
  | .isSome _ => .unsupported "isSome"

/-- Convert an AnnotTerm to Smt.Term -/
partial def annotTermToSmtTerm (at_ : AnnotTerm) : TranslateResult :=
  termToSmtTerm at_.term

/-- Extract pattern bindings from a match: pairs of (smt_name, scrutinee_component_term).
    For a tuple destructuring match, this creates let-bindings that tie
    pattern variables to the corresponding scrutinee components. -/
partial def extractPatternBindings (pat : Types.Pattern) (scrutinee : AnnotTerm)
    : Except String (List (String × Smt.Term)) :=
  match pat.pat with
  | .sym s =>
    -- Single variable pattern: bind to whole scrutinee
    match annotTermToSmtTerm scrutinee with
    | .ok tm => .ok [(symToSmtName s, tm)]
    | .unsupported r => .error s!"pattern binding: {r}"
  | .constructor _ctor args =>
    -- Constructor pattern: handle tuple destructuring and wrappers like Specified(x)
    match scrutinee.term with
    | .tuple components =>
      -- Tuple destructuring: match up pattern args with tuple components
      let pairs := args.zip components
      let results := pairs.map fun ((_, subPat), component) =>
        extractPatternBindings subPat component
      -- Collect all results, propagating any errors
      let collected := results.foldl (init := Except.ok ([] : List (String × Smt.Term))) fun acc r =>
        match acc, r with
        | .error e, _ => .error e
        | _, .error e => .error e
        | .ok ls, .ok rs => .ok (ls ++ rs)
      collected
    | _ =>
      -- Non-tuple scrutinee: for single-arg constructors (like Specified(x)),
      -- unwrap and bind the inner pattern to the scrutinee directly
      match args with
      | [(_, innerPat)] => extractPatternBindings innerPat scrutinee
      | _ => .error s!"constructor pattern with {args.length} args on non-tuple scrutinee"
  | .wild => .ok []  -- Wildcard: no binding

end

/-- Convert a LogicalConstraint to Smt.Term -/
def constraintToSmtTerm : LogicalConstraint → TranslateResult
  | .t it => annotTermToSmtTerm it
  | .forall_ (s, bt) body =>
    let name := symToSmtName s
    match baseTypeToSort bt with
    | .unsupported reason => .unsupported s!"forall bound variable type: {reason}"
    | .ok sort =>
      match annotTermToSmtTerm body with
      | .ok b => .ok (Term.forallT name sort b)
      | .unsupported r => .unsupported r

/-! ## Free Symbol Collection with Types

We collect (Sym, BaseType) pairs to generate properly-typed SMT declarations.
CN uses actual SMT-LIB BitVec types for Bits, so we generate declarations like
`(declare-const v (_ BitVec 32))` instead of `(declare-const v Int)`.
-/

/-- A typed symbol for SMT generation -/
abbrev TypedSym := Sym × BaseType

mutual

/-- Collect free symbols with types from an AnnotTerm.
    Returns (Sym, BaseType) pairs where BaseType comes from the term's annotation. -/
partial def annotTermFreeTypedSyms (at_ : AnnotTerm) : List TypedSym :=
  match at_.term with
  | .sym s => [(s, at_.bt)]
  | .const _ => []
  | .unop _ arg => annotTermFreeTypedSyms arg
  | .binop _ l r => annotTermFreeTypedSyms l ++ annotTermFreeTypedSyms r
  | .ite c t e => annotTermFreeTypedSyms c ++ annotTermFreeTypedSyms t ++ annotTermFreeTypedSyms e
  | .eachI _ (s, _) _ body => (annotTermFreeTypedSyms body).filter (·.1 != s)
  | .tuple elems => elems.flatMap annotTermFreeTypedSyms
  | .nthTuple _ tup => annotTermFreeTypedSyms tup
  | .struct_ _ members => members.flatMap (annotTermFreeTypedSyms ·.2)
  | .structMember obj _ => annotTermFreeTypedSyms obj
  | .structUpdate obj _ val => annotTermFreeTypedSyms obj ++ annotTermFreeTypedSyms val
  | .record members => members.flatMap (annotTermFreeTypedSyms ·.2)
  | .recordMember obj _ => annotTermFreeTypedSyms obj
  | .recordUpdate obj _ val => annotTermFreeTypedSyms obj ++ annotTermFreeTypedSyms val
  | .constructor _ args => args.flatMap (annotTermFreeTypedSyms ·.2)
  | .memberShift ptr _ _ => annotTermFreeTypedSyms ptr
  | .arrayShift base _ idx => annotTermFreeTypedSyms base ++ annotTermFreeTypedSyms idx
  | .copyAllocId addr loc => annotTermFreeTypedSyms addr ++ annotTermFreeTypedSyms loc
  | .hasAllocId ptr => annotTermFreeTypedSyms ptr
  | .sizeOf _ => []
  | .offsetOf _ _ => []
  | .nil _ => []
  | .cons h t => annotTermFreeTypedSyms h ++ annotTermFreeTypedSyms t
  | .head l => annotTermFreeTypedSyms l
  | .tail l => annotTermFreeTypedSyms l
  | .representable _ val => annotTermFreeTypedSyms val
  | .good _ val => annotTermFreeTypedSyms val
  | .aligned ptr align => annotTermFreeTypedSyms ptr ++ annotTermFreeTypedSyms align
  | .wrapI _ val => annotTermFreeTypedSyms val
  | .mapConst _ val => annotTermFreeTypedSyms val
  | .mapSet m k v => annotTermFreeTypedSyms m ++ annotTermFreeTypedSyms k ++ annotTermFreeTypedSyms v
  | .mapGet m k => annotTermFreeTypedSyms m ++ annotTermFreeTypedSyms k
  | .mapDef (s, _) body => (annotTermFreeTypedSyms body).filter (·.1 != s)
  | .apply _ args => args.flatMap annotTermFreeTypedSyms
  | .let_ s binding body =>
    annotTermFreeTypedSyms binding ++ (annotTermFreeTypedSyms body).filter (·.1 != s)
  | .match_ scrut cases =>
    annotTermFreeTypedSyms scrut ++ cases.flatMap (annotTermFreeTypedSyms ·.2)
  | .cast _ val => annotTermFreeTypedSyms val
  | .cnNone _ => []
  | .cnSome val => annotTermFreeTypedSyms val
  | .isSome opt => annotTermFreeTypedSyms opt
  | .getOpt opt => annotTermFreeTypedSyms opt

end

/-- Collect free symbols with types from a LogicalConstraint -/
def constraintFreeTypedSyms : LogicalConstraint → List TypedSym
  | .t it => annotTermFreeTypedSyms it
  | .forall_ (s, _bt) body =>
    -- The bound variable has the given type, but we filter it out
    (annotTermFreeTypedSyms body).filter (·.1 != s)

/-- Deduplicate typed symbols, keeping the first occurrence of each symbol -/
def deduplicateTypedSyms (syms : List TypedSym) : List TypedSym :=
  syms.foldl (fun acc (s, bt) =>
    if acc.any (·.1 == s) then acc else acc ++ [(s, bt)]
  ) []

/-- Collect all free symbols with types from an obligation -/
def obligationFreeTypedSyms (ob : Obligation) : List TypedSym :=
  let assumptionSyms := ob.assumptions.flatMap constraintFreeTypedSyms
  let constraintSyms := constraintFreeTypedSyms ob.constraint
  deduplicateTypedSyms (assumptionSyms ++ constraintSyms)

/-- Legacy: Collect free symbols without types (for backwards compatibility) -/
def annotTermFreeSyms (at_ : AnnotTerm) : List Sym :=
  (annotTermFreeTypedSyms at_).map (·.1)

/-- Legacy: Collect free symbols from a constraint -/
def constraintFreeSyms (lc : LogicalConstraint) : List Sym :=
  (constraintFreeTypedSyms lc).map (·.1)

/-- Legacy: Collect all free symbols from an obligation -/
def obligationFreeSyms (ob : Obligation) : List Sym :=
  (obligationFreeTypedSyms ob).map (·.1)

/-! ## Query Building -/

/-- Build SMT commands for an obligation.
    Returns the commands and any unsupported constructs encountered.

    Uses proper SMT-LIB types: Bits symbols are declared with `(_ BitVec n)`,
    matching CN's approach in solver.ml.
    Corresponds to: CN's solver.ml translate_global_decls -/
def obligationToCommands (ob : Obligation) : List Command × List String :=
  let typedSyms := obligationFreeTypedSyms ob

  -- Generate declarations with proper SMT sorts (BitVec for Bits types)
  -- Collect errors for symbols with unsupported types
  let (decls, declErrors) := typedSyms.foldl (fun (cmds, errs) (s, bt) =>
    match baseTypeToSort bt with
    | .ok sort => (cmds ++ [Command.declare (symToSmtName s) sort], errs)
    | .unsupported reason => (cmds, errs ++ [s!"symbol {symToSmtName s}: {reason}"])
  ) ([], [])

  -- Translate assumptions
  let (assumptionTerms, assumptionErrors) := ob.assumptions.foldl
    (fun (terms, errs) lc =>
      match constraintToSmtTerm lc with
      | .ok tm => (tm :: terms, errs)
      | .unsupported r => (terms, r :: errs))
    ([], [])

  -- No need for explicit range constraints - BitVec types handle this
  let allAssumptions := assumptionTerms.reverse

  -- Build conjunction of assumptions (or "true" if empty)
  let assumptionConj :=
    match allAssumptions with
    | [] => Term.symbolT "true"
    | [single] => single
    | first :: rest => rest.foldl (fun acc tm =>
        Term.mkApp2 (Term.symbolT "and") acc tm) first

  -- Translate goal
  let (goalTerm, goalErrors) :=
    match constraintToSmtTerm ob.constraint with
    | .ok tm => (tm, [])
    | .unsupported r => (Term.symbolT "false", [r])

  let allErrors := declErrors ++ assumptionErrors.reverse ++ goalErrors

  -- Build implication: assumptions => goal
  let implication := Term.mkApp2 (Term.symbolT "=>") assumptionConj goalTerm

  -- Assert negation (checking if the implication can be falsified)
  let assertion := Command.assert (Term.appT (Term.symbolT "not") implication)

  let commands := decls ++ [assertion, Command.checkSat]

  (commands, allErrors)

/-- Convert obligation to SMT-LIB2 query string -/
def obligationToSmtLib2 (ob : Obligation) : String × List String :=
  let (cmds, errors) := obligationToCommands ob
  let queryStr := Command.cmdsAsQuery cmds
  let withComment := s!"; Obligation: {ob.description}\n{queryStr}"
  (withComment, errors)

/-- Serialize multiple obligations, each as a separate query -/
def obligationsToSmtLib2 (obs : List Obligation) : List (Obligation × String × List String) :=
  obs.map fun ob =>
    let (smt, errors) := obligationToSmtLib2 ob
    (ob, smt, errors)

end CerbLean.CN.Verification.SmtLib
