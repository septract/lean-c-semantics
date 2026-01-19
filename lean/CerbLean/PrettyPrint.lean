/-
  Pretty-printer for Core IR matching Cerberus output format

  Corresponds to: cerberus/ocaml_frontend/pprinters/pp_core.ml
  Audited: 2025-12-31
  Deviations: None - output matches Cerberus compact mode exactly
-/

import CerbLean.Core

namespace CerbLean.PrettyPrint

open CerbLean.Core

/-! ## Basic Utilities -/

/-- Indentation level -/
abbrev Indent := Nat

/-- Check if a location is from the main file (i.e., a .c or .core file).
    Corresponds to: cerb_location.ml:from_main_file
    This is used to filter out stdlib/header definitions in pretty-printing. -/
def Loc.fromMainFile (loc : Loc) : Bool :=
  match loc with
  | .unknown => false
  | .other _ => false
  | .point pos => pos.file.endsWith ".c" || pos.file.endsWith ".core"
  | .region pos _ _ => pos.file.endsWith ".c" || pos.file.endsWith ".core"
  | .regions poss _ =>
    match poss with
    | [] => false
    | (pos, _) :: _ => pos.file.endsWith ".c" || pos.file.endsWith ".core"

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
  String.mk (List.replicate (n * 2) ' ') ++ s

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

/-- Pretty-print real floating type -/
def ppRealFloatingType : RealFloatingType → String
  | .float => "float"
  | .double => "double"
  | .longDouble => "long_double"

/-- Pretty-print floating type -/
def ppFloatingType : FloatingType → String
  | .realFloating ty => ppRealFloatingType ty

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

/-- Pretty-print inner C type -/
partial def ppCtype_ : Ctype_ → String
  | .void => "void"
  | .basic ty => ppBasicType ty
  | .array elemTy size =>
    let sizeStr := match size with | some n => s!"{n}" | none => ""
    s!"{ppCtype_ elemTy}[{sizeStr}]"
  | .function _retQuals retTy params variadic =>
    -- pp_core_ctype.ml ignores qualifiers on function params (has TODO comment)
    -- Note: params now include is_register bool, we ignore it for printing
    let paramsStr := joinWith ", " (params.map fun (_q, t, _isReg) => ppCtype_ t)
    let varStr := if variadic then ", ..." else ""
    -- pp_core_ctype uses ^^^ which adds space before parens
    s!"{ppCtype_ retTy} ({paramsStr}{varStr})"
  | .functionNoParams _retQuals retTy =>
    s!"{ppCtype_ retTy} ()"
  | .pointer _quals pointeeTy =>
    -- pp_core_ctype.ml ignores qualifiers on pointers (has TODO comment)
    -- Function pointers become: ret (args)* not ret (*) (args)
    s!"{ppCtype_ pointeeTy}*"
  | .atomic ty => s!"_Atomic ({ppCtype_ ty})"  -- space before paren (pp_core_ctype.ml uses ^^^)
  | .struct_ tag => s!"struct {ppSym tag}"
  | .union_ tag => s!"union {ppSym tag}"
  | .byte => "byte"

/-- Pretty-print C type (with annotations - annotations are ignored for printing) -/
def ppCtype (ct : Ctype) : String := ppCtype_ ct.ty

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

/-- Pretty-print unspecified UB context -/
def ppUnspecifiedUBContext : UnspecifiedUBContext → String
  | .equalityPtrVsNull => "equality_ptr_vs_NULL"
  | .equalityBothArithOrPtr => "equality_both_arith_or_ptr"
  | .pointerAdd => "pointer_add"
  | .pointerSub => "pointer_sub"
  | .conditional => "conditional"
  | .copyAllocId => "copy_alloc_id"
  | .rvalueMemberof => "rvalue_memberof"
  | .memberofptr => "memberofptr"
  | .do_ => "do"

/-- Pretty-print undefined behavior -/
def ppUndefinedBehavior : UndefinedBehavior → String
  -- Dummy
  | .dummy msg => s!"DUMMY({msg})"
  -- Unspecified lvalue
  | .unspecifiedLvalue => "unspecified_lvalue"
  -- Lifetime errors
  | .ub009_outsideLifetime => "UB009_outside_lifetime"
  | .ub010_pointerToDeadObject => "UB010_pointer_to_dead_object"
  | .ub011_useIndeterminateAutomatic => "UB011_use_indeterminate_automatic_object"
  | .ub_modifyingTemporaryLifetime => "UB_modifying_temporary_lifetime"
  -- Trap representations
  | .ub012_lvalueReadTrapRepresentation => "UB012_lvalue_read_trap_representation"
  | .ub013_lvalueSideEffectTrap => "UB013_lvalue_side_effect_trap_representation"
  -- Redeclaration/linkage
  | .ub008_multipleLinkage => "UB008_multiple_linkage"
  | .ub015_incompatibleRedeclaration => "UB015_incompatible_redeclaration"
  -- Type conversion errors
  | .ub017_outOfRangeFloatingIntConversion => "UB017_out_of_range_floating_integer_conversion"
  | .ub019_lvalueNotAnObject => "UB019_lvalue_not_an_object"
  | .ub024_outOfRangePointerToIntConversion => "UB024_out_of_range_pointer_to_integer_conversion"
  | .ub025_misalignedPointerConversion => "UB025_misaligned_pointer_conversion"
  -- String literals
  | .ub033_modifyingStringLiteral => "UB033_modifying_string_literal"
  -- Sequence point violations
  | .ub035_unsequencedRace => "UB035_unsequenced_race"
  | .ub036_exceptionalCondition => "UB036_exceptional_condition"
  | .ub037_illtypedLoad => "UB037_illtyped_load"
  -- Function calls
  | .ub038_numberOfArgs => "UB038_number_of_args"
  | .ub041_functionNotCompatible => "UB041_function_not_compatible"
  -- Atomic
  | .ub042_accessAtomicStructUnionMember => "UB042_access_atomic_structUnion_member"
  -- Indirection
  | .ub043_indirectionInvalidValue => "UB043_indirection_invalid_value"
  -- Division
  | .ub045a_divisionByZero => "UB045a_division_by_zero"
  | .ub045b_moduloByZero => "UB045b_modulo_by_zero"
  | .ub045c_quotientNotRepresentable => "UB045c_quotient_not_representable"
  -- Pointer arithmetic
  | .ub046_arrayPointerOutside => "UB046_array_pointer_outside"
  | .ub047a_arrayPointerAdditionBeyondIndirection => "UB047a_array_pointer_addition_beyond_indirection"
  | .ub047b_arrayPointerSubtractionBeyondIndirection => "UB047b_array_pointer_subtraction_beyond_indirection"
  | .ub048_disjointArrayPointersSubtraction => "UB048_disjoint_array_pointers_subtraction"
  | .ub050_pointersSubtractionNotRepresentable => "UB050_pointers_subtraction_not_representable"
  -- Shifts
  | .ub051a_negativeShift => "UB051a_negative_shift"
  | .ub051b_shiftTooLarge => "UB51b_shift_too_large"
  | .ub052a_negativeLeftShift => "UB052a_negative_left_shift"
  | .ub052b_nonRepresentableLeftShift => "UB052b_non_representable_left_shift"
  -- Pointer comparison
  | .ub053_distinctAggregateUnionPointerComparison => "UB053_distinct_aggregate_union_pointer_comparison"
  -- Assignment
  | .ub054a_inexactlyOverlappingAssignment => "UB054a_inexactly_overlapping_assignment"
  | .ub054b_incompatibleOverlappingAssignment => "UB054b_incompatible_overlapping_assignment"
  -- Declarations
  | .ub059_incompleteNoLinkageIdentifier => "UB059_incomplete_no_linkage_identifier"
  | .ub061_noNamedMembers => "UB061_no_named_members"
  | .ub064_modifyingConst => "UB064_modifying_const"
  | .ub070_inlineNotDefined => "UB070_inline_not_defined"
  | .ub071_noreturn => "UB071_noreturn"
  -- End of function
  | .ub088_endOfNonVoidFunction => "UB088_end_of_non_void_function"
  -- CERB extensions
  | .ub_cerb001_integerToDeadPointer => "UB_CERB001_integer_to_dead_pointer"
  | .ub_cerb002a_outOfBoundLoad => "UB_CERB002a_out_of_bound_load"
  | .ub_cerb002b_outOfBoundStore => "UB_CERB002b_out_of_bound_store"
  | .ub_cerb002c_outOfBoundFree => "UB_CERB002c_out_of_bound_free"
  | .ub_cerb002d_outOfBoundRealloc => "UB_CERB002d_out_of_bound_realloc"
  | .ub_cerb003_invalidFunctionPointer => "UB_CERB003_invalid_function_pointer"
  | .ub_cerb004_unspecified ctx => s!"UB_CERB004_unspecified__{ppUnspecifiedUBContext ctx}"
  | .ub_cerb005_freeNullptr => "UB_CERB005_free_nullptr"
  -- Catch-all
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
    | .concrete _member addr => s!"0x{String.mk (Nat.toDigits 16 addr)}"

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

/-- Pretty-print effectful expression (generic_expr in Cerberus)
    Corresponds to: pp_expr in pp_core.ml
    Audited: 2025-12-31
    Deviations: None
    Takes AExpr to match Cerberus's generic_expr := annots generic_expr_aux -/
partial def ppExpr (ind : Indent) (e : AExpr) : String :=
  match e.expr with
  | .pure pe =>
    let inner := ppAPexpr (ind + 1) pe
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
    let branchesStr := branches.map fun (pat, body) =>
      s!"\n{indent (ind + 1) ""}| {ppAPattern pat} =>\n{indent (ind + 2) ""}{ppExpr (ind + 2) body}"
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
  | .bound body =>
    let inner := ppExpr (ind + 1) body
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

/-- Pretty-print annotated expression (alias for ppExpr) -/
def ppAExpr (ind : Indent) (e : AExpr) : String := ppExpr ind e

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
  | .proc _ _ retTy params body =>
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

/-- Get location from a FunDecl (for filtering) -/
def funDeclGetLoc : FunDecl → Option Loc
  | .fun_ _ _ _ => none  -- Fun has no location, always included
  | .proc loc _ _ _ _ => some loc
  | .procDecl loc _ _ => some loc
  | .builtinDecl loc _ _ => some loc

/-- Check if a function should be printed (from main file or has no location).
    Corresponds to: pp_cond in pp_core.ml -/
def funDeclShouldPrint (decl : FunDecl) : Bool :=
  match funDeclGetLoc decl with
  | none => true  -- Fun always prints
  | some loc => Loc.fromMainFile loc

/-- Pretty-print a complete Core file.
    Filters stdlib/header items to match Cerberus Basic mode output.
    Corresponds to: pp_file in pp_core.ml -/
def ppFile (file : File) : String :=
  let parts : List String := []

  -- Tag definitions (structs/unions) - filter by location
  let mainFileTags := file.tagDefs.filter fun (_, (loc, _)) => Loc.fromMainFile loc
  let hasAggregates := !mainFileTags.isEmpty

  let parts := if hasAggregates then
    let tagParts := mainFileTags.map fun (sym, def_) => ppTagDef sym def_
    parts ++ ["-- Aggregates"] ++ tagParts
  else parts

  -- Global definitions
  -- Note: JSON export filters out GlobalDecl (like pp_globs does)
  let hasGlobs := !file.globs.isEmpty
  let globComment := if hasGlobs then ["-- Globals"] else []
  let globParts := file.globs.map fun (sym, decl) => ppGlobDecl sym decl
  let parts := parts ++ globComment ++ globParts

  -- Functions - filter by location (like pp_cond in pp_core.ml)
  let mainFileFuns := file.funs.filter fun (_, decl) => funDeclShouldPrint decl
  let funMapComment := if hasAggregates || hasGlobs then ["-- Fun map"] else []
  let funParts := mainFileFuns.map fun (sym, decl) => ppFunDecl sym decl
  let parts := parts ++ funMapComment ++ funParts

  joinWith "\n\n" parts

end CerbLean.PrettyPrint
