/-
  Pretty-printer for CN Specifications

  Outputs CN specifications in the standard CN syntax:
  ```
  requires take v = Owned<int>(p);
           v >= 0;
  ensures take v2 = Owned<int>(p);
          v2 == v + 1;
  ```

  This is used for displaying parsed CN specs in a human-readable format.
-/

import CerbLean.CN.Spec
import CerbLean.CN.Terms
import CerbLean.CN.Request
import CerbLean.PrettyPrint

namespace CerbLean.CN.PrettyPrint

open CerbLean.Core (Sym Identifier Ctype)
open CerbLean.PrettyPrint (ppSym ppCtype)

/-! ## Basic Utilities -/

/-- Join strings with separator -/
def joinWith (sep : String) (xs : List String) : String :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: rest => x ++ sep ++ joinWith sep rest

/-- Parenthesize a string -/
def parens (s : String) : String := s!"({s})"

/-! ## Base Type Printing -/

/-- Pretty-print a CN base type -/
def ppBaseType : BaseType → String
  | .unit => "void"
  | .bool => "bool"
  | .integer => "integer"
  | .memByte => "membyte"
  | .bits .signed w => s!"i{w}"
  | .bits .unsigned w => s!"u{w}"
  | .real => "real"
  | .loc => "pointer"
  | .allocId => "alloc_id"
  | .ctype => "ctype"
  | .struct_ s => ppSym s
  | .record _ => "<record>"
  | .datatype s => s!"datatype {ppSym s}"
  | .map k v => s!"map<{ppBaseType k}, {ppBaseType v}>"
  | .list t => s!"list<{ppBaseType t}>"
  | .tuple ts => s!"({joinWith ", " (ts.map ppBaseType)})"
  | .set t => s!"set<{ppBaseType t}>"
  | .option t => s!"option<{ppBaseType t}>"

/-! ## Constant Printing -/

/-- Pretty-print a constant -/
def ppConst : Const → String
  | .z n => toString n
  | .bits sign w n =>
    let suffix := match sign with | .signed => "i" | .unsigned => "u"
    s!"{n}{suffix}{w}"
  | .q num denom => s!"{num}/{denom}"
  | .memByte mb => s!"membyte({mb.value})"
  | .pointer ptr => s!"ptr({ptr.addr})"
  | .allocId id => s!"alloc_id({id})"
  | .bool b => if b then "true" else "false"
  | .unit => "()"
  | .null => "NULL"
  | .ctypeConst ct => s!"ctype({ppCtype ct})"
  | .default bt => s!"default<{ppBaseType bt}>"

/-! ## Operator Printing -/

/-- Pretty-print a unary operator -/
def ppUnOp : UnOp → String
  | .not => "!"
  | .negate => "-"
  | .bwCompl => "~"
  | .bwClzNoSMT => "__builtin_clz"
  | .bwCtzNoSMT => "__builtin_ctz"
  | .bwFfsNoSMT => "__builtin_ffs"
  | .bwFlsNoSMT => "__builtin_fls"

/-- Pretty-print a binary operator -/
def ppBinOp : BinOp → String
  | .and_ => "&&"
  | .or_ => "||"
  | .implies => "==>"
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .mulNoSMT => "*"
  | .div => "/"
  | .divNoSMT => "/"
  | .exp => "^"
  | .expNoSMT => "^"
  | .rem => "%"
  | .remNoSMT => "%"
  | .mod_ => "mod"
  | .modNoSMT => "mod"
  | .bwXor => "^"
  | .bwAnd => "&"
  | .bwOr => "|"
  | .shiftLeft => "<<"
  | .shiftRight => ">>"
  | .lt => "<"
  | .le => "<="
  | .min => "min"
  | .max => "max"
  | .eq => "=="
  | .ltPointer => "<"
  | .lePointer => "<="
  | .setUnion => "∪"
  | .setIntersection => "∩"
  | .setDifference => "\\"
  | .setMember => "∈"
  | .subset => "⊆"

/-! ## Term Printing -/

mutual

/-- Pretty-print an annotated term -/
partial def ppAnnotTerm (t : AnnotTerm) : String :=
  ppTerm t.term

/-- Pretty-print a term -/
partial def ppTerm : Term → String
  | .const c => ppConst c
  | .sym s => ppSym s
  | .unop op arg =>
    let opStr := ppUnOp op
    if opStr.length > 1 then s!"{opStr}({ppAnnotTerm arg})"
    else s!"{opStr}{ppAnnotTerm arg}"
  | .binop op l r => s!"({ppAnnotTerm l} {ppBinOp op} {ppAnnotTerm r})"
  | .ite c t e => s!"(if {ppAnnotTerm c} then {ppAnnotTerm t} else {ppAnnotTerm e})"
  | .eachI lo (v, bt) hi body =>
    "each (" ++ ppBaseType bt ++ " " ++ ppSym v ++ "; " ++ toString lo ++ " <= " ++ ppSym v ++ " && " ++ ppSym v ++ " < " ++ toString hi ++ ") { " ++ ppAnnotTerm body ++ " }"
  | .tuple es => s!"({joinWith ", " (es.map ppAnnotTerm)})"
  | .nthTuple n t => s!"{ppAnnotTerm t}.{n}"
  | .struct_ tag members =>
    let memStrs := members.map fun (id, v) => s!".{id.name} = {ppAnnotTerm v}"
    "struct " ++ ppSym tag ++ " { " ++ joinWith ", " memStrs ++ " }"
  | .structMember obj mem => s!"{ppAnnotTerm obj}.{mem.name}"
  | .structUpdate obj mem val => s!"{ppAnnotTerm obj} with .{mem.name} = {ppAnnotTerm val}"
  | .record members =>
    let memStrs := members.map fun (id, v) => s!".{id.name} = {ppAnnotTerm v}"
    "{ " ++ joinWith ", " memStrs ++ " }"
  | .recordMember obj mem => s!"{ppAnnotTerm obj}.{mem.name}"
  | .recordUpdate obj mem val => s!"{ppAnnotTerm obj} with .{mem.name} = {ppAnnotTerm val}"
  | .constructor constr args =>
    let argStrs := args.map fun (id, v) => s!".{id.name} = {ppAnnotTerm v}"
    ppSym constr ++ " { " ++ joinWith ", " argStrs ++ " }"
  | .memberShift ptr _tag mem => s!"&{ppAnnotTerm ptr}->{mem.name}"
  | .arrayShift base ct idx => s!"array_shift<{ppCtype ct}>({ppAnnotTerm base}, {ppAnnotTerm idx})"
  | .copyAllocId addr loc => s!"copy_alloc_id({ppAnnotTerm addr}, {ppAnnotTerm loc})"
  | .hasAllocId ptr => s!"has_alloc_id({ppAnnotTerm ptr})"
  | .sizeOf ct => s!"sizeof({ppCtype ct})"
  | .offsetOf tag mem => s!"offsetof({ppSym tag}, {mem.name})"
  | .nil _ => "[]"
  | .cons h t => s!"({ppAnnotTerm h} :: {ppAnnotTerm t})"
  | .head l => s!"hd({ppAnnotTerm l})"
  | .tail l => s!"tl({ppAnnotTerm l})"
  | .representable ct v => s!"representable<{ppCtype ct}>({ppAnnotTerm v})"
  | .good ct v => s!"good<{ppCtype ct}>({ppAnnotTerm v})"
  | .aligned ptr align => s!"aligned({ppAnnotTerm ptr}, {ppAnnotTerm align})"
  | .wrapI _it v => s!"wrap({ppAnnotTerm v})"
  | .mapConst _ v => s!"[_ -> {ppAnnotTerm v}]"
  | .mapSet m k v => s!"{ppAnnotTerm m}[{ppAnnotTerm k} := {ppAnnotTerm v}]"
  | .mapGet m k => s!"{ppAnnotTerm m}[{ppAnnotTerm k}]"
  | .mapDef (v, bt) body => s!"[{ppBaseType bt} {ppSym v} -> {ppAnnotTerm body}]"
  | .apply fn args => s!"{ppSym fn}({joinWith ", " (args.map ppAnnotTerm)})"
  | .let_ v binding body => s!"let {ppSym v} = {ppAnnotTerm binding} in {ppAnnotTerm body}"
  | .match_ scrut cases =>
    let caseStrs := cases.map fun (pat, body) => s!"{ppPattern pat} => {ppAnnotTerm body}"
    "match " ++ ppAnnotTerm scrut ++ " { " ++ joinWith "; " caseStrs ++ " }"
  | .cast bt v => s!"({ppBaseType bt}){ppAnnotTerm v}"
  | .cnNone _ => "None"
  | .cnSome v => s!"Some({ppAnnotTerm v})"
  | .isSome opt => s!"is_some({ppAnnotTerm opt})"
  | .getOpt opt => s!"get({ppAnnotTerm opt})"

/-- Pretty-print a pattern -/
partial def ppPattern (p : Pattern) : String :=
  ppPattern_ p.pat
where
  ppPattern_ : Pattern_ → String
    | .sym s => ppSym s
    | .wild => "_"
    | .constructor constr args =>
      let argStrs := args.map fun (id, p) => s!".{id.name} = {ppPattern p}"
      ppSym constr ++ " { " ++ joinWith ", " argStrs ++ " }"

end

/-! ## Resource Printing -/

/-- Pretty-print initialization state -/
def ppInit : Init → String
  | .init => ""  -- Owned is the default
  | .uninit => "Block"  -- Block is uninit Owned

/-- Pretty-print a resource name -/
def ppResourceName : ResourceName → String
  | .owned ct .init => s!"Owned<{ppCtype ct}>"
  | .owned ct .uninit => s!"Block<{ppCtype ct}>"
  | .pname name => ppSym name

/-- Pretty-print a predicate -/
def ppPredicate (p : Predicate) : String :=
  let args := p.pointer :: p.iargs
  s!"{ppResourceName p.name}({joinWith ", " (args.map ppAnnotTerm)})"

/-- Pretty-print a quantified predicate -/
def ppQPredicate (qp : QPredicate) : String :=
  let (v, bt) := qp.q
  "each (" ++ ppBaseType bt ++ " " ++ ppSym v ++ "; " ++ ppAnnotTerm qp.permission ++ ") { " ++ ppResourceName qp.name ++ "(" ++ ppAnnotTerm qp.pointer ++ ") }"

/-- Pretty-print a request -/
def ppRequest : Request → String
  | .p pred => ppPredicate pred
  | .q qpred => ppQPredicate qpred

/-- Pretty-print a resource (request + output) -/
def ppResource (res : Resource) : String :=
  ppRequest res.request

/-! ## Clause Printing -/

/-- Pretty-print a clause -/
def ppClause : Clause → String
  | .resource name res => s!"take {ppSym name} = {ppResource res};"
  | .constraint assertion => s!"{ppAnnotTerm assertion};"

/-! ## Specification Printing -/

/-- Pretty-print a precondition -/
def ppPrecondition (pre : Precondition) : String :=
  if pre.clauses.isEmpty then ""
  else
    let clauseStrs := pre.clauses.map ppClause
    "requires " ++ joinWith "\n         " clauseStrs

/-- Pretty-print a postcondition -/
def ppPostcondition (post : Postcondition) : String :=
  if post.clauses.isEmpty then ""
  else
    let clauseStrs := post.clauses.map ppClause
    "ensures " ++ joinWith "\n        " clauseStrs

/-- Pretty-print a function specification -/
def ppFunctionSpec (spec : FunctionSpec) : String :=
  let parts := []
  let parts := if spec.trusted then parts ++ ["trusted;"] else parts
  let parts := if !spec.requires.clauses.isEmpty
               then parts ++ [ppPrecondition spec.requires]
               else parts
  let parts := if !spec.ensures.clauses.isEmpty
               then parts ++ [ppPostcondition spec.ensures]
               else parts
  joinWith "\n" parts

/-- Pretty-print a function specification as a CN comment block -/
def ppFunctionSpecComment (spec : FunctionSpec) : String :=
  let inner := ppFunctionSpec spec
  if inner.isEmpty then ""
  else s!"/*@ {inner} @*/"

end CerbLean.CN.PrettyPrint
