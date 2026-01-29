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

/-! ## Translation to Smt.Term -/

/-- Result of translation: either success or unsupported construct -/
inductive TranslateResult where
  | ok (tm : Smt.Term)
  | unsupported (reason : String)
  deriving Inhabited

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

/-- Convert a Const to Smt.Term -/
def constToTerm : Const → TranslateResult
  | .z n => .ok (Term.literalT (toString n))
  | .bits _sign _width n => .ok (Term.literalT (toString n))
  | .bool true => .ok (Term.symbolT "true")
  | .bool false => .ok (Term.symbolT "false")
  | .null => .ok (Term.literalT "0")
  | .unit => .ok (Term.literalT "0")
  | .q num denom => .ok (Term.mkApp2 (Term.symbolT "/") (Term.literalT (toString num)) (Term.literalT (toString denom)))
  | .allocId id => .ok (Term.literalT (toString id))
  | .pointer p => .ok (Term.literalT (toString p.addr))
  | .memByte m => .ok (Term.literalT (toString m.value))
  | .ctypeConst _ => .ok (Term.literalT "0")
  | .default _ => .ok (Term.literalT "0")

/-- Convert a UnOp application to Smt.Term -/
def unOpToTerm (op : UnOp) (arg : Smt.Term) : TranslateResult :=
  match op with
  | .not => .ok (Term.appT (Term.symbolT "not") arg)
  | .negate => .ok (Term.appT (Term.symbolT "-") arg)
  | .bwCompl => .unsupported "bwCompl"
  | .bwClzNoSMT => .unsupported "bwClzNoSMT"
  | .bwCtzNoSMT => .unsupported "bwCtzNoSMT"
  | .bwFfsNoSMT => .unsupported "bwFfsNoSMT"
  | .bwFlsNoSMT => .unsupported "bwFlsNoSMT"

/-- Convert a BinOp application to Smt.Term -/
def binOpToTerm (op : BinOp) (l r : Smt.Term) : TranslateResult :=
  let mkBinApp (sym : String) := .ok (Term.mkApp2 (Term.symbolT sym) l r)
  match op with
  | .add => mkBinApp "+"
  | .sub => mkBinApp "-"
  | .mul => mkBinApp "*"
  | .mulNoSMT => mkBinApp "*"
  | .div => mkBinApp "div"
  | .divNoSMT => mkBinApp "div"
  | .rem => mkBinApp "mod"
  | .remNoSMT => mkBinApp "mod"
  | .mod_ => mkBinApp "mod"
  | .modNoSMT => mkBinApp "mod"
  | .lt => mkBinApp "<"
  | .le => mkBinApp "<="
  | .eq => mkBinApp "="
  | .and_ => mkBinApp "and"
  | .or_ => mkBinApp "or"
  | .implies => mkBinApp "=>"
  | .ltPointer => mkBinApp "<"
  | .lePointer => mkBinApp "<="
  | .exp => .unsupported "exp"
  | .expNoSMT => .unsupported "expNoSMT"
  | .min => .unsupported "min"
  | .max => .unsupported "max"
  | .bwXor => .unsupported "bwXor"
  | .bwAnd => .unsupported "bwAnd"
  | .bwOr => .unsupported "bwOr"
  | .shiftLeft => .unsupported "shiftLeft"
  | .shiftRight => .unsupported "shiftRight"
  | .setUnion => .unsupported "setUnion"
  | .setIntersection => .unsupported "setIntersection"
  | .setDifference => .unsupported "setDifference"
  | .setMember => .unsupported "setMember"
  | .subset => .unsupported "subset"

mutual

/-- Convert a CN Term to Smt.Term -/
partial def termToSmtTerm : Types.Term → TranslateResult
  | .const c => constToTerm c
  | .sym s => .ok (Term.symbolT (symToSmtName s))
  | .unop op arg =>
    match annotTermToSmtTerm arg with
    | .ok argTm => unOpToTerm op argTm
    | .unsupported r => .unsupported r
  | .binop op l r =>
    match annotTermToSmtTerm l, annotTermToSmtTerm r with
    | .ok lTm, .ok rTm => binOpToTerm op lTm rTm
    | .unsupported r, _ => .unsupported r
    | _, .unsupported r => .unsupported r
  | .ite cond thenB elseB =>
    match annotTermToSmtTerm cond, annotTermToSmtTerm thenB, annotTermToSmtTerm elseB with
    | .ok c, .ok t, .ok e => .ok (Term.mkApp3 (Term.symbolT "ite") c t e)
    | .unsupported r, _, _ => .unsupported r
    | _, .unsupported r, _ => .unsupported r
    | _, _, .unsupported r => .unsupported r
  | .eachI lo (s, _bt) hi body =>
    -- Bounded quantification as forall with range constraint
    let name := symToSmtName s
    match annotTermToSmtTerm body with
    | .ok b =>
      let rangeConstraint := Term.mkApp2 (Term.symbolT "and")
        (Term.mkApp2 (Term.symbolT ">=") (Term.symbolT name) (Term.literalT (toString lo)))
        (Term.mkApp2 (Term.symbolT "<=") (Term.symbolT name) (Term.literalT (toString hi)))
      let implBody := Term.mkApp2 (Term.symbolT "=>") rangeConstraint b
      .ok (Term.forallT name (Term.symbolT "Int") implBody)
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
    -- For signed integers: -2^(W-1) <= val < 2^(W-1)
    -- For unsigned integers: 0 <= val < 2^W
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
  | .good _ val => annotTermToSmtTerm val
  | .wrapI _ val => annotTermToSmtTerm val
  | .cast _ val => annotTermToSmtTerm val
  | .copyAllocId _ loc => annotTermToSmtTerm loc
  | .hasAllocId _ => .ok (Term.symbolT "true")
  | .sizeOf _ => .ok (Term.literalT "1")
  | .offsetOf _ _ => .ok (Term.literalT "0")
  | .memberShift ptr _ _ => annotTermToSmtTerm ptr
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
  -- Unsupported constructs
  | .tuple _ => .unsupported "tuple"
  | .nthTuple _ _ => .unsupported "nthTuple"
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
  | .match_ _ _ => .unsupported "match"
  | .cnNone _ => .unsupported "cnNone"
  | .isSome _ => .unsupported "isSome"

/-- Convert an AnnotTerm to Smt.Term -/
partial def annotTermToSmtTerm (at_ : AnnotTerm) : TranslateResult :=
  termToSmtTerm at_.term

end

/-- Convert a LogicalConstraint to Smt.Term -/
def constraintToSmtTerm : LogicalConstraint → TranslateResult
  | .t it => annotTermToSmtTerm it
  | .forall_ (s, _bt) body =>
    let name := symToSmtName s
    match annotTermToSmtTerm body with
    | .ok b => .ok (Term.forallT name (Term.symbolT "Int") b)
    | .unsupported r => .unsupported r

/-! ## Free Symbol Collection -/

mutual

/-- Collect free symbols from a Term -/
partial def termFreeSyms : Types.Term → List Sym
  | .const _ => []
  | .sym s => [s]
  | .unop _ arg => annotTermFreeSyms arg
  | .binop _ l r => annotTermFreeSyms l ++ annotTermFreeSyms r
  | .ite c t e => annotTermFreeSyms c ++ annotTermFreeSyms t ++ annotTermFreeSyms e
  | .eachI _ (s, _) _ body => (annotTermFreeSyms body).filter (· != s)
  | .tuple elems => elems.flatMap annotTermFreeSyms
  | .nthTuple _ tup => annotTermFreeSyms tup
  | .struct_ _ members => members.flatMap (annotTermFreeSyms ·.2)
  | .structMember obj _ => annotTermFreeSyms obj
  | .structUpdate obj _ val => annotTermFreeSyms obj ++ annotTermFreeSyms val
  | .record members => members.flatMap (annotTermFreeSyms ·.2)
  | .recordMember obj _ => annotTermFreeSyms obj
  | .recordUpdate obj _ val => annotTermFreeSyms obj ++ annotTermFreeSyms val
  | .constructor _ args => args.flatMap (annotTermFreeSyms ·.2)
  | .memberShift ptr _ _ => annotTermFreeSyms ptr
  | .arrayShift base _ idx => annotTermFreeSyms base ++ annotTermFreeSyms idx
  | .copyAllocId addr loc => annotTermFreeSyms addr ++ annotTermFreeSyms loc
  | .hasAllocId ptr => annotTermFreeSyms ptr
  | .sizeOf _ => []
  | .offsetOf _ _ => []
  | .nil _ => []
  | .cons h t => annotTermFreeSyms h ++ annotTermFreeSyms t
  | .head l => annotTermFreeSyms l
  | .tail l => annotTermFreeSyms l
  | .representable _ val => annotTermFreeSyms val
  | .good _ val => annotTermFreeSyms val
  | .aligned ptr align => annotTermFreeSyms ptr ++ annotTermFreeSyms align
  | .wrapI _ val => annotTermFreeSyms val
  | .mapConst _ val => annotTermFreeSyms val
  | .mapSet m k v => annotTermFreeSyms m ++ annotTermFreeSyms k ++ annotTermFreeSyms v
  | .mapGet m k => annotTermFreeSyms m ++ annotTermFreeSyms k
  | .mapDef (s, _) body => (annotTermFreeSyms body).filter (· != s)
  | .apply _ args => args.flatMap annotTermFreeSyms
  | .let_ s binding body =>
    annotTermFreeSyms binding ++ (annotTermFreeSyms body).filter (· != s)
  | .match_ scrut cases =>
    annotTermFreeSyms scrut ++ cases.flatMap (annotTermFreeSyms ·.2)
  | .cast _ val => annotTermFreeSyms val
  | .cnNone _ => []
  | .cnSome val => annotTermFreeSyms val
  | .isSome opt => annotTermFreeSyms opt
  | .getOpt opt => annotTermFreeSyms opt

/-- Collect free symbols from an AnnotTerm -/
partial def annotTermFreeSyms (at_ : AnnotTerm) : List Sym :=
  termFreeSyms at_.term

end

/-- Collect free symbols from a LogicalConstraint -/
def constraintFreeSyms : LogicalConstraint → List Sym
  | .t it => annotTermFreeSyms it
  | .forall_ (s, _) body => (annotTermFreeSyms body).filter (· != s)

/-- Collect all free symbols from an obligation -/
def obligationFreeSyms (ob : Obligation) : List Sym :=
  let assumptionSyms := ob.assumptions.flatMap constraintFreeSyms
  let constraintSyms := constraintFreeSyms ob.constraint
  (assumptionSyms ++ constraintSyms).eraseDups

/-! ## Query Building -/

/-- Build SMT commands for an obligation.
    Returns the commands and any unsupported constructs encountered. -/
def obligationToCommands (ob : Obligation) : List Command × List String :=
  let syms := obligationFreeSyms ob

  -- Generate declarations for all free symbols (as Int)
  let decls := syms.map fun s =>
    Command.declare (symToSmtName s) (Term.symbolT "Int")

  -- Translate assumptions
  let (assumptionTerms, assumptionErrors) := ob.assumptions.foldl
    (fun (terms, errs) lc =>
      match constraintToSmtTerm lc with
      | .ok tm => (tm :: terms, errs)
      | .unsupported r => (terms, r :: errs))
    ([], [])

  -- Build conjunction of assumptions (or "true" if empty)
  let assumptionConj :=
    match assumptionTerms.reverse with
    | [] => Term.symbolT "true"
    | [single] => single
    | first :: rest => rest.foldl (fun acc tm =>
        Term.mkApp2 (Term.symbolT "and") acc tm) first

  -- Translate goal
  let (goalTerm, goalErrors) :=
    match constraintToSmtTerm ob.constraint with
    | .ok tm => (tm, [])
    | .unsupported r => (Term.symbolT "false", [r])

  let allErrors := assumptionErrors.reverse ++ goalErrors

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
