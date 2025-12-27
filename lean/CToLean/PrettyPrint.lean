/-
  Pretty-printer for Core IR matching Cerberus output format
  Based on cerberus/ocaml_frontend/pprinters/pp_core.ml
-/

import CToLean.Core

namespace CToLean.PrettyPrint

open CToLean.Core

/-! ## Basic Utilities -/

/-- Indentation level -/
abbrev Indent := Nat

/-- Join strings with separator -/
def joinWith (sep : String) (xs : List String) : String :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: rest => x ++ sep ++ joinWith sep rest

/-- Parenthesize if needed -/
def parens (s : String) : String := s!"({s})"

/-- Indent a string -/
def indent (n : Indent) (s : String) : String :=
  String.ofList (List.replicate (n * 2) ' ') ++ s

/-- Simple inline formatting for keyword(arg) - no line breaking -/
def withGroupedArg (keyword : String) (arg : String) (_ind : Indent) : String :=
  s!"{keyword}({arg})"

/-! ## Symbol and Identifier Printing -/

/-- Pretty-print a symbol (Cerberus style: just name, or a_ID if no name) -/
def ppSym (s : Sym) : String :=
  match s.name with
  | some n => n
  | none => s!"a_{s.id}"

/-- Pretty-print an identifier -/
def ppIdentifier (id : Identifier) : String := id.name

/-! ## Type Printing -/

/-- Pretty-print signed integer base kind -/
def ppSignedIntKind : IntBaseKind → String
  | .ichar => "signed ichar"
  | .short => "signed short"
  | .int_ => "signed int"
  | .long => "signed long"
  | .longLong => "signed long_long"
  | .intN n => s!"int{n}_t"
  | .intLeastN n => s!"int_least{n}_t"
  | .intFastN n => s!"int_fast{n}_t"
  | .intmax => "intmax_t"
  | .intptr => "intptr_t"

/-- Pretty-print unsigned integer base kind -/
def ppUnsignedIntKind : IntBaseKind → String
  | .ichar => "unsigned ichar"
  | .short => "unsigned short"
  | .int_ => "unsigned int"
  | .long => "unsigned long"
  | .longLong => "unsigned long_long"
  | .intN n => s!"uint{n}_t"
  | .intLeastN n => s!"uint_least{n}_t"
  | .intFastN n => s!"uint_fast{n}_t"
  | .intmax => "uintmax_t"
  | .intptr => "uintptr_t"

/-- Pretty-print integer type -/
def ppIntegerType : IntegerType → String
  | .char => "char"
  | .bool => "_Bool"
  | .signed k => ppSignedIntKind k
  | .unsigned k => ppUnsignedIntKind k
  | .enum s => s!"enum {ppSym s}"
  | .size_t => "size_t"
  | .wchar_t => "wchar_t"
  | .wint_t => "wint_t"
  | .ptrdiff_t => "ptrdiff_t"
  | .ptraddr_t => "ptraddr_t"

/-- Pretty-print floating type -/
def ppFloatingType : FloatingType → String
  | .float => "float"
  | .double => "double"
  | .longDouble => "long_double"

/-- Pretty-print basic type -/
def ppBasicType : BasicType → String
  | .integer ty => ppIntegerType ty
  | .floating ty => ppFloatingType ty

/-- Pretty-print qualifiers -/
def ppQualifiers (q : Qualifiers) : String :=
  let parts := []
  let parts := if q.const then parts ++ ["const"] else parts
  let parts := if q.volatile then parts ++ ["volatile"] else parts
  let parts := if q.restrict then parts ++ ["restrict"] else parts
  joinWith " " parts

/-- Pretty-print C type -/
partial def ppCtype : Ctype → String
  | .void => "void"
  | .basic ty => ppBasicType ty
  | .array elemTy size =>
    let sizeStr := match size with | some n => s!"{n}" | none => ""
    s!"{ppCtype elemTy}[{sizeStr}]"
  | .function _retQuals retTy params variadic =>
    -- pp_core_ctype.ml ignores qualifiers on function params (has TODO comment)
    let paramsStr := joinWith ", " (params.map fun (_q, t) => ppCtype t)
    let varStr := if variadic then ", ..." else ""
    -- pp_core_ctype uses ^^^ which adds space before parens
    s!"{ppCtype retTy} ({paramsStr}{varStr})"
  | .functionNoParams _retQuals retTy =>
    s!"{ppCtype retTy} ()"
  | .pointer _quals pointeeTy =>
    -- pp_core_ctype.ml ignores qualifiers on pointers (has TODO comment)
    -- Function pointers become: ret (args)* not ret (*) (args)
    s!"{ppCtype pointeeTy}*"
  | .atomic ty => s!"_Atomic ({ppCtype ty})"  -- space before paren (pp_core_ctype.ml uses ^^^)
  | .struct_ tag => s!"struct {ppSym tag}"
  | .union_ tag => s!"union {ppSym tag}"
  | .byte => "byte"

/-- Pretty-print C type in quotes (as Cerberus does) -/
def ppCtypeQuoted (ty : Ctype) : String := s!"'{ppCtype ty}'"

/-! ## Object Type Printing -/

/-- Pretty-print object type -/
def ppObjectType : ObjectType → String
  | .integer => "integer"
  | .floating => "floating"
  | .pointer => "pointer"
  | .array elemTy => s!"array({ppObjectType elemTy})"
  | .struct_ tag => s!"struct {ppSym tag}"
  | .union_ tag => s!"union {ppSym tag}"

/-! ## Base Type Printing -/

/-- Pretty-print base type -/
def ppBaseType : BaseType → String
  | .unit => "unit"
  | .boolean => "boolean"
  | .ctype => "ctype"
  | .list elemTy => s!"[{ppBaseType elemTy}]"
  | .tuple elemTys => s!"({joinWith "," (elemTys.map ppBaseType)})"
  | .object objTy => ppObjectType objTy
  | .loaded objTy => s!"loaded {ppObjectType objTy}"
  | .storable => "storable"

/-! ## Binary Operator Printing -/

/-- Pretty-print binary operator -/
def ppBinop : Binop → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .rem_t => "rem_t"
  | .rem_f => "rem_f"
  | .exp => "^"
  | .eq => "="
  | .gt => ">"
  | .lt => "<"
  | .ge => ">="
  | .le => "<="
  | .and => "/\\"
  | .or => "\\/"

/-- Operator precedence (lower number = higher precedence, matching Cerberus pp_core.ml)
    None means no parens needed (atoms, constructors, etc.)
    Some n means binary op at precedence level n -/
def binopPrecedence : Binop → Nat
  | .exp => 1
  | .mul | .div | .rem_t | .rem_f => 2
  | .add | .sub => 3
  | .lt | .le | .gt | .ge => 4
  | .eq => 5
  | .and => 6
  | .or => 7

/-- Pretty-print integer operation -/
def ppIop : Iop → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .shl => "<<"
  | .shr => ">>"
  | .div => "/"
  | .rem_t => "rem_t"

/-! ## Memory Order Printing -/

/-- Pretty-print memory order -/
def ppMemoryOrder : MemoryOrder → String
  | .na => ""  -- NA is omitted in pretty-print
  | .relaxed => "relaxed"
  | .consume => "consume"
  | .acquire => "acquire"
  | .release => "release"
  | .acqRel => "acq_rel"
  | .seqCst => "seq_cst"

/-- Check if memory order should be omitted (NA) -/
def isNaOrder : MemoryOrder → Bool
  | .na => true
  | _ => false

/-! ## Constructor Printing -/

/-- Pretty-print constructor name -/
def ppCtor : Ctor → String
  | .nil _ => "Nil"
  | .cons => "Cons"
  | .tuple => "Tuple"
  | .array => "Array"
  | .ivmax => "Ivmax"
  | .ivmin => "Ivmin"
  | .ivsizeof => "Ivsizeof"
  | .ivalignof => "Ivalignof"
  | .ivCOMPL => "IvCOMPL"
  | .ivAND => "IvAND"
  | .ivOR => "IvOR"
  | .ivXOR => "IvXOR"
  | .specified => "Specified"
  | .unspecified => "Unspecified"
  | .fvfromint => "Cfvfromint"
  | .ivfromfloat => "Civfromfloat"

/-! ## Implementation Constant Printing -/

/-- Pretty-print implementation constant -/
def ppImplConst : ImplConst → String
  | .intMax ty => s!"Ivmax({ppIntegerType ty})"
  | .intMin ty => s!"Ivmin({ppIntegerType ty})"
  | .sizeof_ ty => s!"Ivsizeof({ppCtypeQuoted ty})"
  | .alignof_ ty => s!"Ivalignof({ppCtypeQuoted ty})"
  | .other name => s!"<{name}>"  -- Cerberus wraps impl constants in angle brackets

/-! ## Name Printing -/

/-- Pretty-print name -/
def ppName : Name → String
  | .sym s => ppSym s
  | .impl c => ppImplConst c

/-! ## Memop Printing -/

/-- Pretty-print undefined behavior -/
def ppUndefinedBehavior : UndefinedBehavior → String
  | .useAfterFree => "use_after_free"
  | .doubleFree => "double_free"
  | .outOfBounds => "out_of_bounds"
  | .nullDeref => "null_deref"
  | .uninitializedRead => "uninitialized_read"
  | .invalidAlignment => "invalid_alignment"
  | .divisionByZero => "division_by_zero"
  | .signedOverflow => "signed_overflow"
  | .shiftOutOfRange => "shift_out_of_range"
  | .invalidPointerArith => "invalid_pointer_arith"
  | .invalidPointerComparison => "invalid_pointer_comparison"
  | .invalidPointerSubtraction => "invalid_pointer_subtraction"
  | .invalidCast => "invalid_cast"
  | .unsequencedModification => "unsequenced_modification"
  | .other name => name

/-- Pretty-print memory operation -/
def ppMemop : Memop → String
  | .ptrEq => "PtrEq"
  | .ptrNe => "PtrNe"
  | .ptrLt => "PtrLt"
  | .ptrGt => "PtrGt"
  | .ptrLe => "PtrLe"
  | .ptrGe => "PtrGe"
  | .ptrdiff => "Ptrdiff"
  | .intFromPtr => "IntFromPtr"
  | .ptrFromInt => "PtrFromInt"
  | .ptrValidForDeref => "PtrValidForDeref"
  | .ptrWellAligned => "PtrWellAligned"
  | .ptrArrayShift => "PtrArrayShift"
  | .ptrMemberShift tag member => s!"PtrMemberShift[{ppSym tag}, {ppIdentifier member}]"
  | .memcpy => "Memcpy"
  | .memcmp => "Memcmp"
  | .realloc => "Realloc"
  | .vaStart => "Va_start"
  | .vaCopy => "Va_copy"
  | .vaArg => "Va_arg"
  | .vaEnd => "Va_end"
  | .copyAllocId => "Copy_alloc_id"
  | .cheriIntrinsic name => name

/-! ## Value Printing -/

mutual
  /-- Pretty-print integer value -/
  partial def ppIntegerValue (v : IntegerValue) : String := s!"{v.val}"

  /-- Pretty-print floating value -/
  partial def ppFloatingValue : FloatingValue → String
    | .finite f => s!"{f}"
    | .nan => "NaN"
    | .posInf => "inf"      -- Cerberus uses "inf" not "Infinity"
    | .negInf => "-inf"     -- Cerberus uses "-inf" not "-Infinity"
    | .unspecified => "unspecified"

  /-- Pretty-print provenance -/
  partial def ppProvenance : Provenance → String
    | .none => ""
    | .some id => s!"@{id}"
    | .symbolic iota => s!"ι{iota}"
    | .device => "@device"

  /-- Pretty-print pointer value base -/
  partial def ppPointerValueBase : PointerValueBase → String
    | .null ty => s!"NULL({ppCtype ty})"
    | .function sym => s!"Cfunction({ppSym sym})"
    | .concrete _member addr => s!"0x{String.ofList (Nat.toDigits 16 addr)}"

  /-- Pretty-print pointer value -/
  partial def ppPointerValue (pv : PointerValue) : String :=
    let base := ppPointerValueBase pv.base
    let prov := ppProvenance pv.prov
    if prov.isEmpty then base else s!"({prov}, {base})"

  /-- Pretty-print object value -/
  partial def ppObjectValue : ObjectValue → String
    | .integer v => ppIntegerValue v
    | .floating v => ppFloatingValue v
    | .pointer v => ppPointerValue v
    | .array elems =>
      let elemsStr := joinWith ", " (elems.map ppLoadedValue)
      s!"Array({elemsStr})"
    | .struct_ tag members =>
      let membersStr := joinWith ", " (members.map fun m =>
        s!".{m.name.name}: ...")
      s!"(struct {ppSym tag}) \{ {membersStr} }"
    | .union_ tag member _ =>
      s!"(union {ppSym tag}) \{ .{member.name}: ... }"

  /-- Pretty-print loaded value -/
  partial def ppLoadedValue : LoadedValue → String
    | .specified v => s!"Specified({ppObjectValue v})"
    | .unspecified ty => s!"Unspecified({ppCtypeQuoted ty})"

  /-- Pretty-print core value -/
  partial def ppValue : Value → String
    | .object v => ppObjectValue v
    | .loaded v => ppLoadedValue v
    | .unit => "Unit"
    | .true_ => "True"
    | .false_ => "False"
    | .ctype ty => ppCtypeQuoted ty
    | .list _ elems =>
      let elemsStr := joinWith ", " (elems.map ppValue)
      s!"[{elemsStr}]"
    | .tuple elems =>
      let elemsStr := joinWith ", " (elems.map ppValue)
      s!"({elemsStr})"
end

/-! ## Pattern Printing -/

mutual
  /-- Pretty-print pattern -/
  partial def ppPattern : Pattern → String
    | .base sym ty =>
      match sym with
      | some s => s!"{ppSym s}: {ppBaseType ty}"
      | none => s!"_: {ppBaseType ty}"
    | .ctor c args =>
      match c with
      | .tuple =>
        -- Tuples use (a, b) syntax, not Tuple(a, b)
        s!"({joinWith ", " (args.map ppPattern)})"
      | _ =>
        if args.isEmpty then ppCtor c
        else s!"{ppCtor c}({joinWith ", " (args.map ppPattern)})"

  /-- Pretty-print annotated pattern -/
  partial def ppAPattern (p : APattern) : String := ppPattern p.pat
end

/-! ## List Expression Helpers -/

/-- Try to extract list elements from a Cons/Nil chain.
    Returns Some [e1, e2, ...] if successful, None otherwise.
    This mirrors Cerberus pp_core.ml:465-481 which prints lists as [...] -/
partial def tryExtractList (e : Pexpr) : Option (List Pexpr) :=
  match e with
  | .ctor (.nil _) [] => some []
  | .ctor .cons [head, tail] =>
    match tryExtractList tail with
    | some rest => some (head :: rest)
    | none => none
  | _ => none

/-! ## Expression Printing -/

mutual
  /-- Pretty-print pure expression -/
  partial def ppPexpr (ind : Indent) : Pexpr → String
    | .sym s => ppSym s
    | .impl c => ppImplConst c
    | .val v => ppValue v
    | .undef _ ub => s!"undef(<<{ppUndefinedBehavior ub}>>)"
    | .error msg e => s!"error(\"{msg}\", {ppPexpr ind e})"
    | .ctor c args =>
      match c with
      | .tuple =>
        -- Tuples use (a, b) syntax, not Tuple(a, b)
        s!"({joinWith ", " (args.map (ppPexpr ind))})"
      | .cons =>
        -- Try to extract a proper list (Cons/Nil chain) and print as [...]
        -- This mirrors Cerberus pp_core.ml:465-481
        match args with
        | [head, tail] =>
          match tryExtractList tail with
          | some rest =>
            let allElems := head :: rest
            s!"[{joinWith ", " (allElems.map (ppPexpr ind))}]"
          | none =>
            -- Fallback to :: syntax if not a proper list
            s!"{ppPexpr ind head} :: {ppPexpr ind tail}"
        | _ =>
          -- Malformed Cons
          s!"{ppCtor c}({joinWith ", " (args.map (ppPexpr ind))})"
      | .nil bTy =>
        -- Empty list with type annotation: []: bTy (pp_core.ml:469)
        if args.isEmpty then s!"[]: {ppBaseType bTy}"
        else s!"{ppCtor c}({joinWith ", " (args.map (ppPexpr ind))})"
      | _ =>
        if args.isEmpty then ppCtor c
        else s!"{ppCtor c}({joinWith ", " (args.map (ppPexpr ind))})"
    | .case_ scrut branches =>
      let branchesStr := branches.map fun (pat, e) =>
        s!"\n{indent (ind + 1) ""}| {ppAPattern pat} =>\n{indent (ind + 2) ""}{ppPexpr (ind + 2) e}"
      s!"case {ppPexpr ind scrut} of{joinWith "" branchesStr}\n{indent ind ""}end"
    | .arrayShift ptr ty idx =>
      s!"array_shift({ppPexpr ind ptr}, {ppCtypeQuoted ty}, {ppPexpr ind idx})"
    | .memberShift ptr tag member =>
      s!"member_shift({ppPexpr ind ptr}, {ppSym tag}, .{ppIdentifier member})"
    | .not_ e => s!"not({ppPexpr ind e})"
    | .op op e1 e2 =>
      -- Always wrap binary ops in parens (matches Cerberus compact mode)
      s!"({ppPexpr ind e1} {ppBinop op} {ppPexpr ind e2})"
    | .struct_ tag members =>
      let membersStr := joinWith ", " (members.map fun (id, e) =>
        s!".{ppIdentifier id}= {ppPexpr ind e}")
      s!"(struct {ppSym tag})\{{membersStr}}"
    | .union_ tag member value =>
      s!"(union {ppSym tag})\{.{ppIdentifier member}= {ppPexpr ind value}}"
    | .cfunction e => s!"cfunction({ppPexpr ind e})"
    | .memberof tag member e =>
      -- Cerberus uses pp_identifier without dot prefix
      s!"memberof({ppSym tag}, {ppIdentifier member}, {ppPexpr ind e})"
    | .call name args =>
      s!"{ppName name}({joinWith ", " (args.map (ppPexpr ind))})"
    | .let_ pat e1 e2 =>
      s!"let {ppAPattern pat} = {ppPexpr ind e1} in\n{indent ind ""}{ppPexpr ind e2}"
    | .if_ cond then_ else_ =>
      s!"if {ppPexpr ind cond} then\n{indent (ind + 1) ""}{ppPexpr (ind + 1) then_}\n{indent ind ""}else\n{indent (ind + 1) ""}{ppPexpr (ind + 1) else_}"
    | .isScalar e => s!"is_scalar({ppPexpr ind e})"
    | .isInteger e => s!"is_integer({ppPexpr ind e})"
    | .isSigned e => s!"is_signed({ppPexpr ind e})"
    | .isUnsigned e => s!"is_unsigned({ppPexpr ind e})"
    | .areCompatible e1 e2 => s!"are_compatible ({ppPexpr ind e1}, {ppPexpr ind e2})"
    | .convInt ty e => s!"__conv_int__('{ppIntegerType ty}', {ppPexpr ind e})"
    | .wrapI ty op e1 e2 =>
      let opSuffix := match op with
        | .add => "_add"
        | .sub => "_sub"
        | .mul => "_mul"
        | _ => s!"_{ppIop op}"
      s!"wrapI{opSuffix}('{ppIntegerType ty}', {ppPexpr ind e1}, {ppPexpr ind e2})"
    | .catchExceptionalCondition ty op e1 e2 =>
      let opSuffix := match op with
        | .add => "_add"
        | .sub => "_sub"
        | .mul => "_mul"
        | .div => "_div"
        | _ => s!"_{ppIop op}"
      s!"catch_exceptional_condition{opSuffix}('{ppIntegerType ty}', {ppPexpr ind e1}, {ppPexpr ind e2})"
    | .bmcAssume e => s!"__bmc_assume ({ppPexpr ind e})"  -- double underscore, space before paren
    | .pureMemop op args =>
      -- Cerberus uses memop(OpName, args...) format (pp_core.ml:501-502)
      s!"memop({op}, {joinWith ", " (args.map (ppPexpr ind))})"
    | .constrained constraints =>
      let constraintsStr := joinWith ", " (constraints.map fun (name, e) =>
        s!"{name}: {ppPexpr ind e}")
      s!"constrained({constraintsStr})"

  /-- Pretty-print annotated pure expression -/
  partial def ppAPexpr (ind : Indent) (e : APexpr) : String := ppPexpr ind e.expr
end

/-! ## Kill Kind Printing -/

/-- Pretty-print kill kind (returns the type argument for kill) -/
def ppKillKind : KillKind → String
  | .dynamic => "free"
  | .static ty => ppCtypeQuoted ty

/-! ## Action Printing -/

/-- Pretty-print action -/
partial def ppAction (ind : Indent) : Action → String
  | .create align size _ =>
    s!"create({ppAPexpr ind align}, {ppAPexpr ind size})"
  | .createReadonly align size init _ =>
    s!"create_readonly({ppAPexpr ind align}, {ppAPexpr ind size}, {ppAPexpr ind init})"
  | .alloc align size _ =>
    s!"alloc({ppAPexpr ind align}, {ppAPexpr ind size})"
  | .kill kind ptr =>
    s!"kill({ppKillKind kind}, {ppAPexpr ind ptr})"
  | .store locking ty ptr val order =>
    -- Cerberus uses store_lock for const globals (pp_core.ml:702)
    let kw := if locking then "store_lock" else "store"
    if isNaOrder order then
      s!"{kw}({ppAPexpr ind ty}, {ppAPexpr ind ptr}, {ppAPexpr ind val})"
    else
      s!"{kw}({ppAPexpr ind ty}, {ppAPexpr ind ptr}, {ppAPexpr ind val}, {ppMemoryOrder order})"
  | .load ty ptr order =>
    if isNaOrder order then
      s!"load({ppAPexpr ind ty}, {ppAPexpr ind ptr})"
    else
      s!"load({ppAPexpr ind ty}, {ppAPexpr ind ptr}, {ppMemoryOrder order})"
  | .rmw ty ptr expected desired successOrd failOrd =>
    s!"rmw({ppAPexpr ind ty}, {ppAPexpr ind ptr}, {ppAPexpr ind expected}, {ppAPexpr ind desired}, {ppMemoryOrder successOrd}, {ppMemoryOrder failOrd})"
  | .fence order =>
    s!"fence({ppMemoryOrder order})"
  | .compareExchangeStrong ty ptr expected desired successOrd failOrd =>
    s!"compare_exchange_strong({ppAPexpr ind ty}, {ppAPexpr ind ptr}, {ppAPexpr ind expected}, {ppAPexpr ind desired}, {ppMemoryOrder successOrd}, {ppMemoryOrder failOrd})"
  | .compareExchangeWeak ty ptr expected desired successOrd failOrd =>
    s!"compare_exchange_weak({ppAPexpr ind ty}, {ppAPexpr ind ptr}, {ppAPexpr ind expected}, {ppAPexpr ind desired}, {ppMemoryOrder successOrd}, {ppMemoryOrder failOrd})"
  | .seqRmw isUpdate ty ptr sym val =>
    -- Format: seq_rmw(ty, ptr, sym => val) - lambda-like syntax
    if isUpdate then
      s!"seq_rmw_with_forward({ppAPexpr ind ty}, {ppAPexpr ind ptr}, {ppSym sym} => {ppAPexpr ind val})"
    else
      s!"seq_rmw({ppAPexpr ind ty}, {ppAPexpr ind ptr}, {ppSym sym} => {ppAPexpr ind val})"

/-! ## Effectful Expression Printing -/

/-- Pretty-print polarity keyword -/
def ppPolarity : Polarity → String
  | .pos => "weak"
  | .neg => "strong"

mutual
  /-- Pretty-print effectful expression -/
  partial def ppExpr (ind : Indent) : Expr → String
    | .pure e =>
      let inner := ppAPexpr (ind + 1) e
      withGroupedArg "pure" inner ind
    | .memop op args =>
      s!"memop({ppMemop op}, {joinWith ", " (args.map (ppAPexpr ind))})"
    | .action pact =>
      let actionStr := ppAction ind pact.action.action
      -- Apply polarity: Neg wraps with neg(...), Pos does nothing
      match pact.polarity with
      | .neg => s!"neg({actionStr})"
      | .pos => actionStr
    | .case_ scrut branches =>
      let branchesStr := branches.map fun (pat, e) =>
        s!"\n{indent (ind + 1) ""}| {ppAPattern pat} =>\n{indent (ind + 2) ""}{ppExpr (ind + 2) e}"
      s!"case {ppAPexpr ind scrut} of{joinWith "" branchesStr}\n{indent ind ""}end"
    | .let_ pat e1 e2 =>
      s!"let {ppAPattern pat} = {ppAPexpr ind e1} in\n{indent ind ""}{ppExpr ind e2}"
    | .if_ cond then_ else_ =>
      s!"if {ppAPexpr ind cond} then\n{indent (ind + 1) ""}{ppExpr (ind + 1) then_}\n{indent ind ""}else\n{indent (ind + 1) ""}{ppExpr (ind + 1) else_}"
    | .ccall funPtr funTy args =>
      -- Cerberus prints: ccall(ty, ptr, args...) - type first, then pointer, then args
      -- funPtr is parsed from JSON "function" field, funTy from "type" field
      let allArgs := [ppAPexpr ind funTy, ppAPexpr ind funPtr] ++ args.map (ppAPexpr ind)
      s!"ccall({joinWith ", " allArgs})"
    | .proc name args =>
      s!"pcall({ppName name}, {joinWith ", " (args.map (ppAPexpr ind))})"
    | .unseq es =>
      let innerExprs := es.map (ppExpr (ind + 1))
      let inner := joinWith ", " innerExprs
      withGroupedArg "unseq" inner ind
    | .wseq pat e1 e2 =>
      -- Cerberus: let weak pat = e1 in e2
      s!"let weak {ppAPattern pat} = {ppExpr ind e1} in\n{indent ind ""}{ppExpr ind e2}"
    | .sseq pat e1 e2 =>
      -- Cerberus: if pattern is (_: unit), use semicolon; otherwise let strong
      match pat.pat with
      | .base none .unit =>
        -- Unit pattern with no binding: use semicolon syntax
        s!"{ppExpr ind e1} ;\n{indent ind ""}{ppExpr ind e2}"
      | _ =>
        -- Named pattern or non-unit: use let strong
        s!"let strong {ppAPattern pat} = {ppExpr ind e1} in\n{indent ind ""}{ppExpr ind e2}"
    | .bound e =>
      let inner := ppExpr (ind + 1) e
      withGroupedArg "bound" inner ind
    | .nd es =>
      let esStr := joinWith ", " (es.map (ppExpr ind))
      s!"nd({esStr})"
    | .save retSym retTy args body =>
      let argsStr := joinWith ", " (args.map fun (sym, ty, init) =>
        s!"{ppSym sym}: {ppBaseType ty}:= {ppAPexpr ind init}")
      s!"save {ppSym retSym}: {ppBaseType retTy} ({argsStr}) in\n{indent (ind + 1) ""}{ppExpr (ind + 1) body}"
    | .run label args =>
      s!"run {ppSym label}({joinWith ", " (args.map (ppAPexpr ind))})"
    | .par es =>
      -- Cerberus uses comma separator (with_grouped_args in cerb_pp_prelude.ml)
      s!"par({joinWith ", " (es.map (ppExpr ind))})"
    | .wait tid =>
      s!"wait({tid})"

  /-- Pretty-print annotated expression -/
  partial def ppAExpr (ind : Indent) (e : AExpr) : String := ppExpr ind e.expr
end

/-! ## Function Declaration Printing -/

/-- Pretty-print parameters (Cerberus style: space before parens) -/
def ppParams (params : List (Sym × BaseType)) : String :=
  let paramsStr := joinWith ", " (params.map fun (s, ty) => s!"{ppSym s}: {ppBaseType ty}")
  s!" ({paramsStr})"

/-- Pretty-print function declaration -/
def ppFunDecl (sym : Sym) (decl : FunDecl) : String :=
  match decl with
  | .fun_ retTy params body =>
    s!"fun {ppSym sym}{ppParams params}: {ppBaseType retTy} :=\n  {ppAPexpr 1 body}"
  | .proc _ retTy params body =>
    s!"proc {ppSym sym}{ppParams params}: eff {ppBaseType retTy} :=\n  {ppAExpr 1 body}"
  | .procDecl _ _retTy paramTys =>
    -- Cerberus omits return type for declarations without body (pp_core.ml:785)
    let paramsStr := joinWith ", " (paramTys.map ppBaseType)
    s!"proc {ppSym sym} ({paramsStr})"
  | .builtinDecl _ _retTy paramTys =>
    -- Cerberus omits return type for declarations without body (pp_core.ml:787)
    let paramsStr := joinWith ", " (paramTys.map ppBaseType)
    s!"builtin {ppSym sym} ({paramsStr})"

/-! ## Tag Definition Printing -/

/-- Pretty-print tag definition -/
def ppTagDef (sym : Sym) (tagDef : Loc × TagDef) : String :=
  let (_, def_) := tagDef
  match def_ with
  | .struct_ fields flexOpt =>
    -- For flexible array member, wrap element type in array[] (Cerberus pp_core.ml:770)
    let flexFields := match flexOpt with
      | some flex =>
        let arrayTy := Ctype.array flex.ty none  -- elem_ty[] with no size
        [{ name := flex.name, ty := arrayTy : FieldDef }]
      | none => []
    let allFields := fields ++ flexFields
    let fieldsStr := joinWith "\n  " (allFields.map fun f =>
      s!"{ppIdentifier f.name}: {ppCtypeQuoted f.ty}")
    s!"def struct {ppSym sym} :=\n  {fieldsStr}"
  | .union_ fields =>
    let fieldsStr := joinWith "\n  " (fields.map fun f =>
      s!"{ppIdentifier f.name}: {ppCtypeQuoted f.ty}")
    s!"def union {ppSym sym} :=\n  {fieldsStr}"

/-! ## Global Definition Printing -/

/-- Pretty-print global declaration -/
def ppGlobDecl (sym : Sym) (decl : GlobDecl) : String :=
  match decl with
  | .def_ coreTy cTy init =>
    s!"glob {ppSym sym}: {ppBaseType coreTy} [ail_ctype = {ppCtypeQuoted cTy}] :=\n  {ppAExpr 1 init}"
  | .decl coreTy cTy =>
    s!"glob {ppSym sym}: {ppBaseType coreTy} [ail_ctype = {ppCtypeQuoted cTy}]"

/-! ## File Printing -/

/-- Pretty-print a complete Core file -/
def ppFile (file : File) : String :=
  let parts : List String := []

  -- Tag definitions (structs/unions)
  let hasAggregates := !file.tagDefs.isEmpty

  let parts := if hasAggregates then
    let tagParts := file.tagDefs.map fun (sym, def_) => ppTagDef sym def_
    parts ++ ["-- Aggregates"] ++ tagParts
  else parts

  -- Global definitions
  -- Note: JSON export (json_core.ml) now filters out GlobalDecl (like pp_globs does),
  -- so we only get GlobalDef entries and don't need to filter library globals here
  let hasGlobs := !file.globs.isEmpty
  let globComment := if hasGlobs then ["-- Globals"] else []
  let globParts := file.globs.map fun (sym, decl) => ppGlobDecl sym decl
  let parts := parts ++ globComment ++ globParts

  -- Functions (funs is now a List, preserving order from JSON)
  let funMapComment := if hasAggregates || hasGlobs then ["-- Fun map"] else []
  let funParts := file.funs.map fun (sym, decl) => ppFunDecl sym decl
  let parts := parts ++ funMapComment ++ funParts

  joinWith "\n\n" parts

end CToLean.PrettyPrint
