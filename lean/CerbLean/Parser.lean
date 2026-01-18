/-
  JSON parser for Cerberus Core output
  Uses Lean's built-in JSON library to deserialize Core IR
-/

import Lean.Data.Json
import CerbLean.Core

open Lean (Json ToJson FromJson)
open CerbLean.Core

namespace CerbLean.Parser

/-! ## JSON Parsing Utilities -/

/-- Get a required field from a JSON object -/
def getField (obj : Json) (field : String) : Except String Json :=
  obj.getObjVal? field

/-- Get an optional field from a JSON object -/
def getFieldOpt (obj : Json) (field : String) : Option Json :=
  match obj.getObjVal? field with
  | .ok v => some v
  | .error _ => none

/-- Truncate JSON for error messages -/
def truncateJson (j : Json) (maxLen : Nat := 100) : String :=
  let s := toString j
  if s.length > maxLen then (s.take maxLen).toString ++ "..." else s

/-- Get a required string field -/
def getStr (obj : Json) (field : String) : Except String String := do
  let v ← getField obj field
  match v.getStr? with
  | .ok s => .ok s
  | .error e => .error s!"{e} (field '{field}' in {truncateJson obj})"

/-- Get a required integer field -/
def getInt (obj : Json) (field : String) : Except String Int := do
  let v ← getField obj field
  match v.getInt? with
  | .ok n => .ok n
  | .error e => .error s!"{e} (field '{field}' in {truncateJson obj})"

/-- Get a required natural number field -/
def getNat (obj : Json) (field : String) : Except String Nat := do
  let n ← getInt obj field
  if n >= 0 then .ok n.toNat
  else .error s!"field '{field}' is negative"

/-- Get a required boolean field -/
def getBool (obj : Json) (field : String) : Except String Bool := do
  let v ← getField obj field
  v.getBool?

/-- Get a required array field -/
def getArr (obj : Json) (field : String) : Except String (Array Json) := do
  let v ← getField obj field
  v.getArr?

/-- Get the "tag" field for discriminated unions -/
def getTag (obj : Json) : Except String String :=
  getStr obj "tag"

/-- Get a field and verify it has the expected tag.
    This is the primary way to access tagged JSON fields - always use this
    instead of getField when the field should contain a tagged object. -/
def getTaggedField (obj : Json) (field : String) (expectedTag : String) : Except String Json := do
  let v ← getField obj field
  let actualTag ← getTag v
  if actualTag == expectedTag then
    .ok v
  else
    .error s!"field '{field}' has tag '{actualTag}', expected '{expectedTag}'"

/-- Get a field and verify it has one of the expected tags.
    Returns the actual tag along with the JSON value. -/
def getTaggedFieldMulti (obj : Json) (field : String) (expectedTags : List String) : Except String (String × Json) := do
  let v ← getField obj field
  let actualTag ← getTag v
  if expectedTags.contains actualTag then
    .ok (actualTag, v)
  else
    .error s!"field '{field}' has tag '{actualTag}', expected one of {expectedTags}"

/-! ## Tag Constants for Validation -/

/-- Valid tags for ObjectType -/
def objectTypeTags : List String :=
  ["OTy_integer", "OTy_floating", "OTy_pointer", "OTy_array", "OTy_struct", "OTy_union"]

/-- Valid tags for BaseType -/
def baseTypeTags : List String :=
  ["BTy_unit", "BTy_boolean", "BTy_ctype", "BTy_storable", "BTy_list", "BTy_tuple",
   "BTy_object", "BTy_loaded"]

/-- Valid tags for Ctype -/
def ctypeTags : List String :=
  ["Void", "Byte", "Basic", "Array", "Function", "FunctionNoParams",
   "Pointer", "Atomic", "Struct", "Union"]

/-- Valid tags for BasicType -/
def basicTypeTags : List String := ["Integer", "Floating"]

/-- Valid tags for IntegerType -/
def integerTypeTags : List String :=
  ["Char", "Bool", "Signed", "Unsigned", "Enum", "Size_t", "Wchar_t", "Wint_t",
   "Ptrdiff_t", "Ptraddr_t"]

/-- Valid tags for IntBaseKind (structured form) -/
def intBaseKindTags : List String := ["IntN_t", "Int_leastN_t", "Int_fastN_t"]

/-- Valid tags for Ctor -/
def ctorTags : List String :=
  ["Cnil", "Ccons", "Ctuple", "Carray", "Civmax", "Civmin", "Civsizeof", "Civalignof",
   "CivCOMPL", "CivAND", "CivOR", "CivXOR", "Cspecified", "Cunspecified",
   "Cfvfromint", "Civfromfloat"]

/-- Valid tags for Value -/
def valueTags : List String :=
  ["Vunit", "Vtrue", "Vfalse", "Vctype", "Vobject", "Vloaded", "Vlist", "Vtuple"]

/-- Valid tags for MemValue -/
def memValueTags : List String :=
  ["MVunspecified", "MVconcurrent", "MVinteger", "MVfloating", "MVpointer", "MVarray", "MVstruct", "MVunion"]

/-- Valid tags for ObjectValue -/
def objectValueTags : List String :=
  ["OVinteger", "OVfloating", "OVpointer", "OVarray", "OVstruct", "OVunion"]

/-- Valid tags for LoadedValue -/
def loadedValueTags : List String := ["LVspecified", "LVunspecified"]

/-- Valid tags for Pattern -/
def patternTags : List String := ["CaseBase", "CaseCtor"]

/-- Valid tags for Pexpr (inner expr field) -/
def pexprTags : List String :=
  ["PEsym", "PEimpl", "PEval", "PEundef", "PEerror", "PEctor", "PEcase",
   "PEarray_shift", "PEmember_shift", "PEnot", "PEop", "PEstruct", "PEunion",
   "PEcfunction", "PEmemberof", "PEcall", "PElet", "PEif", "PEis_scalar",
   "PEis_integer", "PEis_signed", "PEis_unsigned", "PEare_compatible",
   "PEwrapI", "PEcatch_exceptional_condition", "PEconv_int", "PEbmc_assume",
   "PEmemop", "PEconstrained"]

/-- Valid tags for Action -/
def actionTags : List String :=
  ["Create", "CreateReadOnly", "Alloc", "Kill", "Store", "Load", "Fence",
   "SeqRMW", "RMW", "CompareExchangeStrong", "CompareExchangeWeak"]

/-- Valid tags for Expr (inner expr field) -/
def exprTags : List String :=
  ["Epure", "Ememop", "Eaction", "Ecase", "Elet", "Eif", "Eccall", "Eproc",
   "Eunseq", "Ewseq", "Esseq", "Ebound", "End", "Esave", "Erun", "Epar", "Ewait",
   "Eannot"]

/-- Valid tags for Name -/
def nameTags : List String := ["Sym", "Impl"]

/-- Valid tags for KillKind -/
def killKindTags : List String := ["Dynamic", "Static"]

/-- Valid tags for TagDef -/
def tagDefTags : List String := ["StructDef", "UnionDef"]

/-- Valid tags for FunDecl -/
def funDeclTags : List String := ["Fun", "Proc", "ProcDecl", "BuiltinDecl"]

/-- Valid tags for GlobDecl -/
def globDeclTags : List String := ["GlobalDef", "GlobalDecl"]

/-! ## Symbol Parsing -/

/-- Parse a Sym from JSON -/
def parseSym (j : Json) : Except String Sym := do
  let id ← getNat j "id"
  let name := match getFieldOpt j "name" with
    | some (Json.str s) => some s
    | _ => none
  .ok { id := id, name := name }

/-- Parse an optional Sym (handles null) -/
def parseSymOpt (j : Json) : Except String (Option Sym) :=
  if j.isNull then .ok none
  else do
    let sym ← parseSym j
    .ok (some sym)

/-- Parse an Identifier from JSON -/
def parseIdentifier (j : Json) : Except String Identifier := do
  match j.getStr? with
  | .ok s => .ok { loc := .unknown, name := s }
  | .error e => .error s!"{e} (parsing identifier from {truncateJson j})"

/-- Parse a position from JSON: {file: string, line: nat, column: nat}
    Corresponds to: Cerb_position.t -/
def parsePos (j : Json) : Except String Pos := do
  let file ← getStr j "file"
  let line ← getNat j "line"
  let col ← getNat j "column"
  .ok { file, line, col }

/-- Parse cursor from JSON.
    Corresponds to: cursor in cerb_location.ml
    Note: cursor can be null for NoCursor -/
def parseCursor (j : Json) : Except String Cursor := do
  if j.isNull then
    return .noCursor
  let tag ← getTag j
  match tag with
  | "NoCursor" => .ok .noCursor
  | "PointCursor" =>
    let posJ ← getField j "pos"
    let pos ← parsePos posJ
    .ok (.pointCursor pos)
  | "RegionCursor" =>
    let beginJ ← getField j "begin"
    let endJ ← getField j "end"
    let start ← parsePos beginJ
    let end_ ← parsePos endJ
    .ok (.regionCursor start end_)
  | other => .error s!"unknown cursor tag '{other}'"

/-- Parse a Loc from JSON.
    Corresponds to: t in cerb_location.ml -/
def parseLoc (j : Json) : Except String Loc := do
  -- null means unknown location
  if j.isNull then
    return .unknown
  -- Parse structured format with tag
  let tag ← getTag j
  match tag with
  | "Region" =>
    let beginJ ← getField j "begin"
    let endJ ← getField j "end"
    let cursorJ ← getField j "cursor"
    let start ← parsePos beginJ
    let end_ ← parsePos endJ
    let cursor ← parseCursor cursorJ
    .ok (.region start end_ cursor)
  | "Point" =>
    let posJ ← getField j "pos"
    let pos ← parsePos posJ
    .ok (.point pos)
  | "Other" =>
    let desc ← getStr j "desc"
    .ok (.other desc)
  | "Regions" =>
    let regionsJ ← getArr j "regions"
    let cursorJ ← getField j "cursor"
    let cursor ← parseCursor cursorJ
    let regions ← regionsJ.toList.mapM fun r => do
      let beginJ ← getField r "begin"
      let endJ ← getField r "end"
      let start ← parsePos beginJ
      let end_ ← parsePos endJ
      .ok (start, end_)
    .ok (.regions regions cursor)
  | other => .error s!"unknown location tag '{other}', expected Region, Point, Other, or Regions"

/-- Parse annotations from JSON -/
def parseAnnots (j : Json) : Except String Annots := do
  match getFieldOpt j "loc" with
  | some locJson =>
    let loc ← parseLoc locJson
    .ok [.loc loc]
  | none => .ok []

/-! ## Type Parsing -/

/-- Parse an ObjectType from JSON -/
partial def parseObjectType (j : Json) : Except String ObjectType := do
  let tag ← getTag j
  match tag with
  | "OTy_integer" => .ok .integer
  | "OTy_floating" => .ok .floating
  | "OTy_pointer" => .ok .pointer
  | "OTy_array" =>
    let (_, elem) ← getTaggedFieldMulti j "element" objectTypeTags
    let elemTy ← parseObjectType elem
    .ok (.array elemTy)
  | "OTy_struct" =>
    let tagSym ← getField j "struct_tag"
    let sym ← parseSym tagSym
    .ok (.struct_ sym)
  | "OTy_union" =>
    let tagSym ← getField j "union_tag"
    let sym ← parseSym tagSym
    .ok (.union_ sym)
  | other => .error s!"unknown object type tag '{other}', expected one of {objectTypeTags}"

/-- Parse a BaseType from JSON -/
partial def parseBaseType (j : Json) : Except String BaseType := do
  let tag ← getTag j
  match tag with
  | "BTy_unit" => .ok .unit
  | "BTy_boolean" => .ok .boolean
  | "BTy_ctype" => .ok .ctype
  | "BTy_storable" => .ok .storable
  | "BTy_list" =>
    let (_, elem) ← getTaggedFieldMulti j "element" baseTypeTags
    let elemTy ← parseBaseType elem
    .ok (.list elemTy)
  | "BTy_tuple" =>
    let elems ← getArr j "elements"
    let elemTys ← elems.toList.mapM parseBaseType
    .ok (.tuple elemTys)
  | "BTy_object" =>
    let (_, objTy) ← getTaggedFieldMulti j "object_type" objectTypeTags
    let oty ← parseObjectType objTy
    .ok (.object oty)
  | "BTy_loaded" =>
    let (_, objTy) ← getTaggedFieldMulti j "object_type" objectTypeTags
    let oty ← parseObjectType objTy
    .ok (.loaded oty)
  | other => .error s!"unknown base type tag '{other}', expected one of {baseTypeTags}"

/-- Parse Qualifiers from JSON -/
def parseQualifiers (j : Json) : Except String Qualifiers := do
  let const_ ← getBool j "const"
  let restrict ← getBool j "restrict"
  let volatile ← getBool j "volatile"
  .ok { const := const_, restrict := restrict, volatile := volatile }

/-- Parse IntBaseKind from JSON string -/
def parseIntBaseKind (j : Json) : Except String IntBaseKind := do
  match j with
  | .str s =>
    match s with
    | "Ichar" => .ok .ichar
    | "Short" => .ok .short
    | "Int_" => .ok .int_
    | "Long" => .ok .long
    | "LongLong" => .ok .longLong
    | "Intmax_t" => .ok .intmax
    | "Intptr_t" => .ok .intptr
    | _ => .error s!"unknown int base kind: {s}"
  | .obj _ =>
    let tag ← getTag j
    match tag with
    | "IntN_t" =>
      let bits ← getNat j "bits"
      .ok (.intN bits)
    | "Int_leastN_t" =>
      let bits ← getNat j "bits"
      .ok (.intLeastN bits)
    | "Int_fastN_t" =>
      let bits ← getNat j "bits"
      .ok (.intFastN bits)
    | other => .error s!"unknown int base kind tag '{other}', expected one of {intBaseKindTags}"
  | _ => .error "expected int base kind"

/-- Parse IntegerType from structured JSON -/
def parseIntegerTypeStruct (j : Json) : Except String IntegerType := do
  let tag ← getTag j
  match tag with
  | "Char" => .ok .char
  | "Bool" => .ok .bool
  | "Signed" =>
    let kind ← getField j "kind"
    let k ← parseIntBaseKind kind
    .ok (.signed k)
  | "Unsigned" =>
    let kind ← getField j "kind"
    let k ← parseIntBaseKind kind
    .ok (.unsigned k)
  | "Enum" =>
    let tagSym ← getField j "enum_tag"
    let sym ← parseSym tagSym
    .ok (.enum sym)
  | "Size_t" => .ok .size_t
  | "Wchar_t" => .ok .wchar_t
  | "Wint_t" => .ok .wint_t
  | "Ptrdiff_t" => .ok .ptrdiff_t
  | "Ptraddr_t" => .ok .ptraddr_t
  | other => .error s!"unknown integer type tag '{other}', expected one of {integerTypeTags}"

/-- Parse RealFloatingType from JSON string -/
def parseRealFloatingType (j : Json) : Except String RealFloatingType := do
  let s ← j.getStr?
  match s with
  | "Float" => .ok .float
  | "Double" => .ok .double
  | "LongDouble" => .ok .longDouble
  | _ => .error s!"unknown real floating type: {s}"

/-- Parse FloatingType from JSON string -/
def parseFloatingTypeStruct (j : Json) : Except String FloatingType := do
  let rft ← parseRealFloatingType j
  .ok (.realFloating rft)

/-- Parse BasicType from structured JSON -/
def parseBasicType (j : Json) : Except String BasicType := do
  let tag ← getTag j
  match tag with
  | "Integer" =>
    let (_, intTy) ← getTaggedFieldMulti j "int_type" integerTypeTags
    let ity ← parseIntegerTypeStruct intTy
    .ok (.integer ity)
  | "Floating" =>
    let floatTy ← getField j "float_type"  -- FloatingType is a string, not tagged
    let fty ← parseFloatingTypeStruct floatTy
    .ok (.floating fty)
  | other => .error s!"unknown basic type tag '{other}', expected one of {basicTypeTags}"

/-- Parse a Ctype_ (inner type) from structured JSON -/
partial def parseCtype_ (j : Json) : Except String Ctype_ := do
  let tag ← getTag j
  match tag with
  | "Void" => .ok .void
  | "Byte" => .ok .byte
  | "Basic" =>
    let (_, basicTy) ← getTaggedFieldMulti j "basic_type" basicTypeTags
    let bty ← parseBasicType basicTy
    .ok (.basic bty)
  | "Array" =>
    let (_, elemTy) ← getTaggedFieldMulti j "element_type" ctypeTags
    let elem ← parseCtype_ elemTy
    let sizeJ ← getField j "size"
    let size := if sizeJ.isNull then none else sizeJ.getInt?.toOption.map (·.toNat)
    .ok (.array elem size)
  | "Function" =>
    let (_, retTy) ← getTaggedFieldMulti j "return_type" ctypeTags
    let ret ← parseCtype_ retTy
    let retQualsJ ← getField j "return_qualifiers"
    let retQuals ← parseQualifiers retQualsJ
    let paramsJ ← getArr j "params"
    let params ← paramsJ.toList.mapM fun p => do
      let qualsJ ← getField p "qualifiers"
      let quals ← parseQualifiers qualsJ
      let (_, tyJ) ← getTaggedFieldMulti p "type" ctypeTags
      let ty ← parseCtype_ tyJ
      -- Parse is_register, defaulting to false if not present
      let isRegister ← match j.getObjValD "is_register" with
        | .bool b => .ok b
        | _ => .ok false
      .ok (quals, ty, isRegister)
    let variadic ← getBool j "variadic"
    .ok (.function retQuals ret params variadic)
  | "FunctionNoParams" =>
    let (_, retTy) ← getTaggedFieldMulti j "return_type" ctypeTags
    let ret ← parseCtype_ retTy
    let retQualsJ ← getField j "return_qualifiers"
    let retQuals ← parseQualifiers retQualsJ
    .ok (.functionNoParams retQuals ret)
  | "Pointer" =>
    let qualsJ ← getField j "qualifiers"
    let quals ← parseQualifiers qualsJ
    let (_, pointeeTy) ← getTaggedFieldMulti j "pointee_type" ctypeTags
    let pointee ← parseCtype_ pointeeTy
    .ok (.pointer quals pointee)
  | "Atomic" =>
    let (_, innerTy) ← getTaggedFieldMulti j "inner_type" ctypeTags
    let inner ← parseCtype_ innerTy
    .ok (.atomic inner)
  | "Struct" =>
    let tagSym ← getField j "struct_tag"
    let sym ← parseSym tagSym
    .ok (.struct_ sym)
  | "Union" =>
    let tagSym ← getField j "union_tag"
    let sym ← parseSym tagSym
    .ok (.union_ sym)
  | other => .error s!"unknown ctype tag '{other}', expected one of {ctypeTags}"

/-- Parse a Ctype (with annotations) from structured JSON -/
partial def parseCtype (j : Json) : Except String Ctype := do
  -- Parse inner type
  let ty ← parseCtype_ j
  -- Parse annotations (currently just location, same as parseAnnots)
  let annots ← parseAnnots j
  .ok { annots := annots, ty := ty }

/-! ## Value Parsing -/

/-- Parse a Ctor from JSON -/
def parseCtor (j : Json) : Except String Ctor := do
  let tag ← getTag j
  match tag with
  | "Cnil" =>
    let (_, ty) ← getTaggedFieldMulti j "type" baseTypeTags
    let bty ← parseBaseType ty
    .ok (.nil bty)
  | "Ccons" => .ok .cons
  | "Ctuple" => .ok .tuple
  | "Carray" => .ok .array
  | "Civmax" => .ok .ivmax
  | "Civmin" => .ok .ivmin
  | "Civsizeof" => .ok .ivsizeof
  | "Civalignof" => .ok .ivalignof
  | "CivCOMPL" => .ok .ivCOMPL
  | "CivAND" => .ok .ivAND
  | "CivOR" => .ok .ivOR
  | "CivXOR" => .ok .ivXOR
  | "Cspecified" => .ok .specified
  | "Cunspecified" => .ok .unspecified
  | "Cfvfromint" => .ok .fvfromint
  | "Civfromfloat" => .ok .ivfromfloat
  | other => .error s!"unknown constructor tag '{other}', expected one of {ctorTags}"

/-- Parse Polarity from JSON -/
def parsePolarity (j : Json) : Except String Polarity := do
  let s ← j.getStr?
  match s with
  | "Pos" => .ok .pos
  | "Neg" => .ok .neg
  | _ => .error "invalid polarity"

/-- Parse MemoryOrder from JSON -/
def parseMemoryOrder (j : Json) : Except String MemoryOrder := do
  let s ← j.getStr?
  match s with
  | "NA" => .ok .na
  | "Relaxed" => .ok .relaxed
  | "Consume" => .ok .consume
  | "Acquire" => .ok .acquire
  | "Release" => .ok .release
  | "Acq_rel" => .ok .acqRel
  | "Seq_cst" => .ok .seqCst
  | _ => .error "invalid memory order"

/-- Parse KillKind from JSON -/
def parseKillKind (j : Json) : Except String KillKind := do
  let tag ← getTag j
  match tag with
  | "Dynamic" => .ok .dynamic
  | "Static" =>
    let (_, ctyJ) ← getTaggedFieldMulti j "ctype" ctypeTags
    let cty ← parseCtype ctyJ
    .ok (.static cty)
  | other => .error s!"unknown kill kind tag '{other}', expected one of {killKindTags}"

/-- Parse a Name from JSON -/
def parseName (j : Json) : Except String Name := do
  let tag ← getTag j
  match tag with
  | "Sym" =>
    let sym ← getField j "symbol"  -- Sym is not a tagged type
    let s ← parseSym sym
    .ok (.sym s)
  | "Impl" =>
    let c ← getStr j "constant"
    .ok (.impl (.other c))
  | other => .error s!"unknown name kind tag '{other}', expected one of {nameTags}"

/-- Parse an Iop (integer operation) from JSON -/
def parseIop (j : Json) : Except String Iop := do
  let s ← j.getStr?
  match s with
  | "IOpAdd" => return CerbLean.Core.Iop.add
  | "IOpSub" => return CerbLean.Core.Iop.sub
  | "IOpMul" => return CerbLean.Core.Iop.mul
  | "IOpShl" => return CerbLean.Core.Iop.shl
  | "IOpShr" => return CerbLean.Core.Iop.shr
  | "IOpDiv" => return CerbLean.Core.Iop.div
  | "IOpRem_t" => return CerbLean.Core.Iop.rem_t
  | _ => throw s!"unknown iop: {s}"

/-- Parse an IntegerType from JSON (string representation) -/
def parseIntegerTypeStr (s : String) : Except String IntegerType :=
  -- Parse string representations like "signed int", "unsigned char", etc.
  if s == "char" then .ok .char
  else if s == "_Bool" then .ok .bool
  else if s.startsWith "signed " then
    let rest := s.drop 7  -- drop "signed "
    match rest with
    | "char" => .ok (.signed .ichar)
    | "short" => .ok (.signed .short)
    | "int" => .ok (.signed .int_)
    | "long" => .ok (.signed .long)
    | "long long" => .ok (.signed .longLong)
    | _ => .ok (.signed .int_)  -- default
  else if s.startsWith "unsigned " then
    let rest := s.drop 9  -- drop "unsigned "
    match rest with
    | "char" => .ok (.unsigned .ichar)
    | "short" => .ok (.unsigned .short)
    | "int" => .ok (.unsigned .int_)
    | "long" => .ok (.unsigned .long)
    | "long long" => .ok (.unsigned .longLong)
    | _ => .ok (.unsigned .int_)  -- default
  else
    -- Default to signed int for unrecognized
    .ok (.signed .int_)

/-- Parse a Binop from JSON -/
def parseBinop (j : Json) : Except String Binop := do
  let s ← j.getStr?
  match s with
  | "OpAdd" => .ok .add
  | "OpSub" => .ok .sub
  | "OpMul" => .ok .mul
  | "OpDiv" => .ok .div
  | "OpRem_t" => .ok .rem_t
  | "OpRem_f" => .ok .rem_f
  | "OpExp" => .ok .exp
  | "OpEq" => .ok .eq
  | "OpGt" => .ok .gt
  | "OpLt" => .ok .lt
  | "OpGe" => .ok .ge
  | "OpLe" => .ok .le
  | "OpAnd" => .ok .and
  | "OpOr" => .ok .or
  | _ => .error "invalid binop"

/-- Parse SymPrefix from JSON -/
def parsePrefix (j : Json) : Except String SymPrefix := do
  let tag ← getTag j
  -- For now just store as a string representation
  .ok { val := tag }

/-- Parse a Memop from structured JSON -/
def parseMemop (j : Json) : Except String Memop := do
  let tag ← getTag j
  match tag with
  | "PtrEq" => .ok .ptrEq
  | "PtrNe" => .ok .ptrNe
  | "PtrLt" => .ok .ptrLt
  | "PtrGt" => .ok .ptrGt
  | "PtrLe" => .ok .ptrLe
  | "PtrGe" => .ok .ptrGe
  | "Ptrdiff" => .ok .ptrdiff
  | "IntFromPtr" => .ok .intFromPtr
  | "PtrFromInt" => .ok .ptrFromInt
  | "PtrValidForDeref" => .ok .ptrValidForDeref
  | "PtrWellAligned" => .ok .ptrWellAligned
  | "PtrArrayShift" => .ok .ptrArrayShift
  | "PtrMemberShift" =>
    let tagSym ← getField j "struct_tag"
    let sym ← parseSym tagSym
    let memberJ ← getField j "member"
    let member ← parseIdentifier memberJ
    .ok (.ptrMemberShift sym member)
  | "Memcpy" => .ok .memcpy
  | "Memcmp" => .ok .memcmp
  | "Realloc" => .ok .realloc
  | "Va_start" => .ok .vaStart
  | "Va_copy" => .ok .vaCopy
  | "Va_arg" => .ok .vaArg
  | "Va_end" => .ok .vaEnd
  | "Copy_alloc_id" => .ok .copyAllocId
  | "CHERI_intrinsic" =>
    let name ← getStr j "name"
    .ok (.cheriIntrinsic name)
  | _ => .error s!"unknown memop tag: {tag}"

/-- Parse an ImplConst from a string representation -/
def parseImplConst (s : String) : Except String ImplConst :=
  -- Implementation constants are exported as strings like "Characters.bits_in_byte",
  -- "Sizeof(int)", "Alignof(struct foo)", etc.
  -- For now, we store all as .other since parsing the full set is complex
  .ok (.other s)

/-- Parse a LinkingKind from JSON -/
def parseLinkingKind (j : Json) : Except String LinkingKind := do
  let tag ← getTag j
  match tag with
  | "LK_none" => .ok .none_
  | "LK_tentative" =>
    let symJ ← getField j "symbol"
    let sym ← parseSym symJ
    .ok (.tentative sym)
  | "LK_normal" =>
    let symJ ← getField j "symbol"
    let sym ← parseSym symJ
    .ok (.normal sym)
  | _ => .error s!"unknown linking_kind tag: {tag}"

/-! ## Expression Parsing -/

-- Forward declarations for mutual recursion
mutual
  /-- Parse an ObjectValue from JSON -/
  partial def parseObjectValue (j : Json) : Except String ObjectValue := do
    let tag ← getTag j
    match tag with
    | "OVinteger" =>
      let valStr ← getStr j "value"
      let val := valStr.toInt?.getD 0
      .ok (.integer { val := val })
    | "OVfloating" =>
      let valField ← getField j "value"
      match valField with
      | .str s =>
        -- Handle special string values - convert to Lean Float (matches Cerberus FVconcrete)
        -- Cerberus uses OCaml's native float which handles NaN/Inf internally
        let fv := match s with
          | "unspecified" => FloatingValue.unspecified
          | "NaN" => FloatingValue.finite (0.0 / 0.0)  -- Lean Float NaN
          | "Infinity" => FloatingValue.finite (1.0 / 0.0)  -- Lean Float +Inf
          | "-Infinity" => FloatingValue.finite ((-1.0) / 0.0)  -- Lean Float -Inf
          | _ =>
            -- Try parsing as number string
            match s.toNat? with
            | some n => FloatingValue.finite n.toFloat
            | none => FloatingValue.finite 0.0  -- Fallback
        .ok (.floating fv)
      | .num n => .ok (.floating (.finite n.toFloat))
      | _ => .error "OVfloating value must be string or number"
    | "OVpointer" =>
      -- New structured format: value is an object with tag PVnull/PVfunction/PVconcrete
      let valObj ← getField j "value"
      let ptrTag ← getStr valObj "tag"
      match ptrTag with
      | "PVnull" =>
        -- Null pointer with ctype
        let (_, ctypeJ) ← getTaggedFieldMulti valObj "ctype" ctypeTags
        let cty ← parseCtype ctypeJ
        .ok (.pointer { prov := .none, base := .null cty })
      | "PVfunction" =>
        -- Function pointer with symbol (may be null)
        let symJ ← getField valObj "sym"
        match symJ with
        | .null => .ok (.pointer { prov := .none, base := .function { id := 0, name := none } })
        | _ =>
          let sym ← parseSym symJ
          .ok (.pointer { prov := .none, base := .function sym })
      | "PVconcrete" =>
        -- Concrete pointer with optional alloc_id and address
        let allocIdJ ← getField valObj "alloc_id"
        let addrStr ← getStr valObj "addr"
        let addr := addrStr.toNat?.getD 0
        let prov := match allocIdJ with
          | .str s => match s.toNat? with
            | some id => Provenance.some id
            | none => Provenance.none
          | _ => Provenance.none
        .ok (.pointer { prov := prov, base := .concrete none addr })
      | _ => .error s!"unknown pointer tag: {ptrTag}"
    | "OVarray" =>
      let elems ← getArr j "elements"
      let lvs ← elems.toList.mapM parseLoadedValue
      .ok (.array lvs)
    | "OVstruct" =>
      let tagSym ← getField j "struct_tag"  -- Sym is not a tagged type
      let sym ← parseSym tagSym
      let membersArr ← getArr j "members"
      let members ← membersArr.toList.mapM fun m => do
        let nameJ ← getField m "name"
        let name ← parseIdentifier nameJ
        let (_, ctypeJ) ← getTaggedFieldMulti m "ctype" ctypeTags
        let ctype ← parseCtype ctypeJ
        let valJ ← getField m "value"
        let value ← parseMemValue valJ
        pure { name := name, ty := ctype, value := value : StructMember }
      .ok (.struct_ sym members)
    | "OVunion" =>
      let tagSym ← getField j "union_tag"  -- Sym is not a tagged type
      let sym ← parseSym tagSym
      let memberJ ← getField j "member"
      let id ← parseIdentifier memberJ
      let valJ ← getField j "value"
      let value ← parseMemValue valJ
      .ok (.union_ sym id value)
    | other => .error s!"unknown object value tag '{other}', expected one of {objectValueTags}"

  /-- Parse a LoadedValue from JSON -/
  partial def parseLoadedValue (j : Json) : Except String LoadedValue := do
    let tag ← getTag j
    match tag with
    | "LVspecified" =>
      let (_, v) ← getTaggedFieldMulti j "value" objectValueTags
      let ov ← parseObjectValue v
      .ok (.specified ov)
    | "LVunspecified" =>
      let (_, ctyJ) ← getTaggedFieldMulti j "ctype" ctypeTags
      let cty ← parseCtype ctyJ
      .ok (.unspecified cty)
    | other => .error s!"unknown loaded value tag '{other}', expected one of {loadedValueTags}"

  /-- Parse a MemValue from JSON -/
  partial def parseMemValue (j : Json) : Except String MemValue := do
    let tag ← getTag j
    match tag with
    | "MVunspecified" =>
      let (_, ctyJ) ← getTaggedFieldMulti j "ctype" ctypeTags
      let cty ← parseCtype ctyJ
      .ok (.unspecified cty)
    | "MVconcurrent" =>
      -- Concurrent read value - shouldn't occur in sequential, but parse anyway
      let ityJ ← getField j "int_type"
      let ity ← parseIntegerTypeStruct ityJ
      -- Just return unspecified for now since we don't support concurrent
      .ok (.unspecified (.basic (.integer ity)))
    | "MVinteger" =>
      let ityJ ← getField j "int_type"
      let ity ← parseIntegerTypeStruct ityJ
      let valStr ← getStr j "value"
      let val := valStr.toInt?.getD 0
      .ok (.integer ity { val := val })
    | "MVfloating" =>
      let ftyStr ← getStr j "float_type"
      let fty := match ftyStr with
        | "Float" => FloatingType.realFloating .float
        | "Double" => FloatingType.realFloating .double
        | "LongDouble" => FloatingType.realFloating .longDouble
        | _ => FloatingType.realFloating .double  -- fallback
      let valField ← getField j "value"
      -- Convert to Lean Float (matches Cerberus FVconcrete with OCaml native floats)
      let fv := match valField with
        | .str "unspecified" => FloatingValue.unspecified
        | .str "NaN" => FloatingValue.finite (0.0 / 0.0)  -- Lean Float NaN
        | .str "Infinity" => FloatingValue.finite (1.0 / 0.0)  -- Lean Float +Inf
        | .str "-Infinity" => FloatingValue.finite ((-1.0) / 0.0)  -- Lean Float -Inf
        | .str s => match s.toNat? with
          | some n => FloatingValue.finite n.toFloat
          | none => FloatingValue.finite 0.0
        | .num n => FloatingValue.finite n.toFloat
        | _ => FloatingValue.unspecified
      .ok (.floating fty fv)
    | "MVpointer" =>
      let (_, ctyJ) ← getTaggedFieldMulti j "ctype" ctypeTags
      let cty ← parseCtype ctyJ
      let valJ ← getField j "value"
      -- Parse pointer value (reuse logic from OVpointer)
      let ptrTag ← getStr valJ "tag"
      let pv ← match ptrTag with
        | "PVnull" =>
          let (_, nullCtyJ) ← getTaggedFieldMulti valJ "ctype" ctypeTags
          let nullCty ← parseCtype nullCtyJ
          pure { prov := .none, base := .null nullCty : PointerValue }
        | "PVfunction" =>
          let symJ ← getField valJ "sym"
          match symJ with
          | .null => pure { prov := .none, base := .function { id := 0, name := none } : PointerValue }
          | _ =>
            let sym ← parseSym symJ
            pure { prov := .none, base := .function sym : PointerValue }
        | "PVconcrete" =>
          let allocIdJ ← getField valJ "alloc_id"
          let addrStr ← getStr valJ "addr"
          let addr := addrStr.toNat?.getD 0
          let prov := match allocIdJ with
            | .str s => match s.toNat? with
              | some id => Provenance.some id
              | none => Provenance.none
            | _ => Provenance.none
          pure { prov := prov, base := .concrete none addr : PointerValue }
        | _ => .error s!"unknown pointer tag in MVpointer: {ptrTag}"
      .ok (.pointer cty pv)
    | "MVarray" =>
      let elems ← getArr j "elements"
      let mvs ← elems.toList.mapM parseMemValue
      .ok (.array mvs)
    | "MVstruct" =>
      let tagSym ← getField j "struct_tag"
      let sym ← parseSym tagSym
      let membersArr ← getArr j "members"
      let members ← membersArr.toList.mapM fun m => do
        let nameJ ← getField m "name"
        let name ← parseIdentifier nameJ
        let (_, ctyJ) ← getTaggedFieldMulti m "ctype" ctypeTags
        let cty ← parseCtype ctyJ
        let valJ ← getField m "value"
        let val ← parseMemValue valJ
        pure (name, cty, val)
      .ok (.struct_ sym members)
    | "MVunion" =>
      let tagSym ← getField j "union_tag"
      let sym ← parseSym tagSym
      let memberJ ← getField j "member"
      let member ← parseIdentifier memberJ
      let valJ ← getField j "value"
      let val ← parseMemValue valJ
      .ok (.union_ sym member val)
    | other => .error s!"unknown mem_value tag '{other}', expected one of {memValueTags}"

  /-- Parse a Value from JSON -/
  partial def parseValue (j : Json) : Except String Value := do
    let tag ← getTag j
    match tag with
    | "Vunit" => .ok .unit
    | "Vtrue" => .ok .true_
    | "Vfalse" => .ok .false_
    | "Vctype" =>
      let (_, ctyJ) ← getTaggedFieldMulti j "ctype" ctypeTags
      let cty ← parseCtype ctyJ
      .ok (.ctype cty)
    | "Vobject" =>
      let (_, v) ← getTaggedFieldMulti j "value" objectValueTags
      let ov ← parseObjectValue v
      .ok (.object ov)
    | "Vloaded" =>
      let (_, v) ← getTaggedFieldMulti j "value" loadedValueTags
      let lv ← parseLoadedValue v
      .ok (.loaded lv)
    | "Vlist" =>
      let (_, ty) ← getTaggedFieldMulti j "type" baseTypeTags
      let bty ← parseBaseType ty
      let elems ← getArr j "elements"
      let vs ← elems.toList.mapM parseValue
      .ok (.list bty vs)
    | "Vtuple" =>
      let elems ← getArr j "elements"
      let vs ← elems.toList.mapM parseValue
      .ok (.tuple vs)
    | other => .error s!"unknown value tag '{other}', expected one of {valueTags}"

  /-- Parse a Pattern from JSON -/
  partial def parsePattern (j : Json) : Except String APattern := do
    let tag ← getTag j
    let annots ← parseAnnots j
    match tag with
    | "CaseBase" =>
      let symOpt ← match getFieldOpt j "symbol" with
        | some v => if v.isNull then .ok none else do
            let sym ← parseSym v
            .ok (some sym)
        | none => .ok none
      let (_, ty) ← getTaggedFieldMulti j "type" baseTypeTags
      let bty ← parseBaseType ty
      .ok { annots := annots, pat := .base symOpt bty }
    | "CaseCtor" =>
      let (_, ctor) ← getTaggedFieldMulti j "constructor" ctorTags
      let c ← parseCtor ctor
      let pats ← getArr j "patterns"
      let ps ← pats.toList.mapM parsePattern
      .ok { annots := annots, pat := .ctor c (ps.map (·.pat)) }
    | other => .error s!"unknown pattern tag '{other}', expected one of {patternTags}"

  /-- Parse a Pexpr (pure expression) from JSON -/
  partial def parsePexpr (j : Json) : Except String APexpr := do
    let annots ← parseAnnots j
    let exprJ ← getField j "expr"
    let tag ← getTag exprJ
    let expr ← match tag with
    | "PEsym" =>
      let sym ← getField exprJ "symbol"
      let s ← parseSym sym
      .ok (Pexpr.sym s)
    | "PEimpl" =>
      let c ← getStr exprJ "constant"
      .ok (Pexpr.impl (.other c))
    | "PEval" =>
      let (_, v) ← getTaggedFieldMulti exprJ "value" valueTags
      let val ← parseValue v
      .ok (Pexpr.val val)
    | "PEundef" =>
      let locJ ← getField exprJ "loc"
      let loc ← parseLoc locJ
      let ubStr ← getStr exprJ "ub"
      .ok (Pexpr.undef loc (.other ubStr))
    | "PEerror" =>
      let msg ← getStr exprJ "message"
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.error msg pe.expr)
    | "PEctor" =>
      let (_, ctor) ← getTaggedFieldMulti exprJ "constructor" ctorTags
      let c ← parseCtor ctor
      let args ← getArr exprJ "args"
      let pes ← args.toList.mapM parsePexpr
      .ok (Pexpr.ctor c (pes.map (·.expr)))
    | "PEcase" =>
      let scrut ← getField exprJ "scrutinee"
      let s ← parsePexpr scrut
      let branches ← getArr exprJ "branches"
      let bs ← branches.toList.mapM fun b => do
        let (_, pat) ← getTaggedFieldMulti b "pattern" patternTags
        let body ← getField b "body"
        let p ← parsePattern pat
        let e ← parsePexpr body
        .ok (p, e.expr)
      .ok (Pexpr.case_ s.expr bs)
    | "PEarray_shift" =>
      let ptr ← getField exprJ "ptr"
      let p ← parsePexpr ptr
      let (_, ctypeJ) ← getTaggedFieldMulti exprJ "ctype" ctypeTags
      let ctype ← parseCtype ctypeJ
      let idx ← getField exprJ "index"
      let i ← parsePexpr idx
      .ok (Pexpr.arrayShift p.expr ctype i.expr)
    | "PEmember_shift" =>
      let ptr ← getField exprJ "ptr"
      let p ← parsePexpr ptr
      let tagSym ← getField exprJ "struct_tag"
      let t ← parseSym tagSym
      let member ← getField exprJ "member"
      let m ← parseIdentifier member
      .ok (Pexpr.memberShift p.expr t m)
    | "PEnot" =>
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.not_ pe.expr)
    | "PEop" =>
      let op ← getField exprJ "op"
      let binop ← parseBinop op
      let l ← getField exprJ "left"
      let r ← getField exprJ "right"
      let le ← parsePexpr l
      let re ← parsePexpr r
      .ok (Pexpr.op binop le.expr re.expr)
    | "PEstruct" =>
      let tagSym ← getField exprJ "struct_tag"
      let t ← parseSym tagSym
      let members ← getArr exprJ "members"
      let ms ← members.toList.mapM fun m => do
        let name ← getField m "name"
        let id ← parseIdentifier name
        let value ← getField m "value"
        let v ← parsePexpr value
        .ok (id, v.expr)
      .ok (Pexpr.struct_ t ms)
    | "PEunion" =>
      let tagSym ← getField exprJ "union_tag"
      let t ← parseSym tagSym
      let member ← getField exprJ "member"
      let m ← parseIdentifier member
      let value ← getField exprJ "value"
      let v ← parsePexpr value
      .ok (Pexpr.union_ t m v.expr)
    | "PEcfunction" =>
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.cfunction pe.expr)
    | "PEmemberof" =>
      let tagSym ← getField exprJ "member_tag"
      let t ← parseSym tagSym
      let member ← getField exprJ "member"
      let m ← parseIdentifier member
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.memberof t m pe.expr)
    | "PEcall" =>
      let (_, name) ← getTaggedFieldMulti exprJ "name" nameTags
      let n ← parseName name
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM parsePexpr
      .ok (Pexpr.call n (as.map (·.expr)))
    | "PElet" =>
      let (_, pat) ← getTaggedFieldMulti exprJ "pattern" patternTags
      let p ← parsePattern pat
      let binding ← getField exprJ "binding"
      let e1 ← parsePexpr binding
      let body ← getField exprJ "body"
      let e2 ← parsePexpr body
      .ok (Pexpr.let_ p e1.expr e2.expr)
    | "PEif" =>
      let cond ← getField exprJ "condition"
      let c ← parsePexpr cond
      let then_ ← getField exprJ "then_branch"
      let t ← parsePexpr then_
      let else_ ← getField exprJ "else_branch"
      let e ← parsePexpr else_
      .ok (Pexpr.if_ c.expr t.expr e.expr)
    | "PEis_scalar" =>
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.isScalar pe.expr)
    | "PEis_integer" =>
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.isInteger pe.expr)
    | "PEis_signed" =>
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.isSigned pe.expr)
    | "PEis_unsigned" =>
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.isUnsigned pe.expr)
    | "PEare_compatible" =>
      let l ← getField exprJ "left"
      let r ← getField exprJ "right"
      let le ← parsePexpr l
      let re ← parsePexpr r
      .ok (Pexpr.areCompatible le.expr re.expr)
    | "PEwrapI" =>
      let (_, tyJ) ← getTaggedFieldMulti exprJ "type" integerTypeTags
      let ty ← parseIntegerTypeStruct tyJ
      let op ← getField exprJ "op"
      let iop ← parseIop op
      let l ← getField exprJ "left"
      let r ← getField exprJ "right"
      let le ← parsePexpr l
      let re ← parsePexpr r
      .ok (Pexpr.wrapI ty iop le.expr re.expr)
    | "PEcatch_exceptional_condition" =>
      let (_, tyJ) ← getTaggedFieldMulti exprJ "type" integerTypeTags
      let ty ← parseIntegerTypeStruct tyJ
      let op ← getField exprJ "op"
      let iop ← parseIop op
      let l ← getField exprJ "left"
      let r ← getField exprJ "right"
      let le ← parsePexpr l
      let re ← parsePexpr r
      .ok (Pexpr.catchExceptionalCondition ty iop le.expr re.expr)
    | "PEconv_int" =>
      let (_, tyJ) ← getTaggedFieldMulti exprJ "type" integerTypeTags
      let ty ← parseIntegerTypeStruct tyJ
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.convInt ty pe.expr)
    | "PEbmc_assume" =>
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.bmcAssume pe.expr)
    | "PEmemop" =>
      -- op is a tagged object like {"tag": "ByteFromInt"} or {"tag": "DeriveCap", ...}
      let opJ ← getField exprJ "op"
      let op ← getTag opJ
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM parsePexpr
      .ok (Pexpr.pureMemop op (as.map (·.expr)))
    | "PEconstrained" =>
      -- Simplified - just store constraints as string/pexpr pairs
      let pairs ← getArr exprJ "constraints"
      let cs ← pairs.toList.mapM fun p => do
        let c ← getStr p "constraint"
        let e ← getField p "expr"
        let pe ← parsePexpr e
        .ok (c, pe.expr)
      .ok (Pexpr.constrained cs)
    | other => .error s!"unknown pexpr tag '{other}', expected one of {pexprTags}"
    .ok { annots := annots, ty := none, expr := expr }

  /-- Parse an Action from JSON -/
  partial def parseAction (j : Json) : Except String AAction := do
    let locJ ← getField j "loc"
    let loc ← parseLoc locJ
    let actJ ← getField j "action"
    let tag ← getTag actJ
    let action ← match tag with
    | "Create" =>
      let align ← getField actJ "align"
      let a ← parsePexpr align
      let size ← getField actJ "size"
      let s ← parsePexpr size
      let pref ← getField actJ "prefix"
      let p ← parsePrefix pref
      .ok (Action.create a s p)
    | "CreateReadOnly" =>
      let align ← getField actJ "align"
      let a ← parsePexpr align
      let size ← getField actJ "size"
      let s ← parsePexpr size
      let init ← getField actJ "init"
      let i ← parsePexpr init
      let pref ← getField actJ "prefix"
      let p ← parsePrefix pref
      .ok (Action.createReadonly a s i p)
    | "Alloc" =>
      let align ← getField actJ "align"
      let a ← parsePexpr align
      let size ← getField actJ "size"
      let s ← parsePexpr size
      let pref ← getField actJ "prefix"
      let p ← parsePrefix pref
      .ok (Action.alloc a s p)
    | "Kill" =>
      let (_, kind) ← getTaggedFieldMulti actJ "kind" killKindTags
      let k ← parseKillKind kind
      let ptr ← getField actJ "ptr"
      let p ← parsePexpr ptr
      .ok (Action.kill k p)
    | "Store" =>
      let locking ← getBool actJ "locking"
      let ctype ← getField actJ "ctype"
      let ty ← parsePexpr ctype
      let ptr ← getField actJ "ptr"
      let p ← parsePexpr ptr
      let value ← getField actJ "value"
      let v ← parsePexpr value
      let mo ← getField actJ "memory_order"
      let order ← parseMemoryOrder mo
      .ok (Action.store locking ty p v order)
    | "Load" =>
      let ctype ← getField actJ "ctype"
      let ty ← parsePexpr ctype
      let ptr ← getField actJ "ptr"
      let p ← parsePexpr ptr
      let mo ← getField actJ "memory_order"
      let order ← parseMemoryOrder mo
      .ok (Action.load ty p order)
    | "Fence" =>
      let mo ← getField actJ "memory_order"
      let order ← parseMemoryOrder mo
      .ok (Action.fence order)
    | "SeqRMW" =>
      let isUpdate ← getBool actJ "is_update"
      let ctype ← getField actJ "ctype"
      let ty ← parsePexpr ctype
      let ptr ← getField actJ "ptr"
      let p ← parsePexpr ptr
      let sym ← getField actJ "symbol"
      let s ← parseSym sym
      let value ← getField actJ "value"
      let v ← parsePexpr value
      .ok (Action.seqRmw isUpdate ty p s v)
    | "RMW" =>
      let ctype ← getField actJ "ctype"
      let ty ← parsePexpr ctype
      let ptr ← getField actJ "ptr"
      let p ← parsePexpr ptr
      let expected ← getField actJ "expected"
      let exp ← parsePexpr expected
      let desired ← getField actJ "desired"
      let des ← parsePexpr desired
      let succOrd ← getField actJ "success_order"
      let succ ← parseMemoryOrder succOrd
      let failOrd ← getField actJ "failure_order"
      let fail ← parseMemoryOrder failOrd
      .ok (Action.rmw ty p exp des succ fail)
    | "CompareExchangeStrong" =>
      let ctype ← getField actJ "ctype"
      let ty ← parsePexpr ctype
      let ptr ← getField actJ "ptr"
      let p ← parsePexpr ptr
      let expected ← getField actJ "expected"
      let exp ← parsePexpr expected
      let desired ← getField actJ "desired"
      let des ← parsePexpr desired
      let succOrd ← getField actJ "success_order"
      let succ ← parseMemoryOrder succOrd
      let failOrd ← getField actJ "failure_order"
      let fail ← parseMemoryOrder failOrd
      .ok (Action.compareExchangeStrong ty p exp des succ fail)
    | "CompareExchangeWeak" =>
      let ctype ← getField actJ "ctype"
      let ty ← parsePexpr ctype
      let ptr ← getField actJ "ptr"
      let p ← parsePexpr ptr
      let expected ← getField actJ "expected"
      let exp ← parsePexpr expected
      let desired ← getField actJ "desired"
      let des ← parsePexpr desired
      let succOrd ← getField actJ "success_order"
      let succ ← parseMemoryOrder succOrd
      let failOrd ← getField actJ "failure_order"
      let fail ← parseMemoryOrder failOrd
      .ok (Action.compareExchangeWeak ty p exp des succ fail)
    | other => .error s!"unknown action tag '{other}', expected one of {actionTags}"
    .ok { loc := loc, action := action }

  /-- Parse a Paction from JSON -/
  partial def parsePaction (j : Json) : Except String Paction := do
    let pol ← getField j "polarity"
    let p ← parsePolarity pol
    let act ← getField j "action"
    let a ← parseAction act
    .ok { polarity := p, action := a }

  /-- Parse an Expr (effectful expression) from JSON -/
  partial def parseExpr (j : Json) : Except String AExpr := do
    let annots ← parseAnnots j
    let exprJ ← getField j "expr"
    let tag ← getTag exprJ
    let expr ← match tag with
    | "Epure" =>
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Expr.pure pe)
    | "Ememop" =>
      let opJ ← getField exprJ "op"
      let op ← parseMemop opJ
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM parsePexpr
      .ok (Expr.memop op as)
    | "Eaction" =>
      let act ← getField exprJ "action"
      let a ← parsePaction act
      .ok (Expr.action a)
    | "Ecase" =>
      let scrut ← getField exprJ "scrutinee"
      let s ← parsePexpr scrut
      let branches ← getArr exprJ "branches"
      let bs ← branches.toList.mapM fun b => do
        let (_, pat) ← getTaggedFieldMulti b "pattern" patternTags
        let body ← getField b "body"
        let p ← parsePattern pat
        let e ← parseExpr body
        .ok (p, e)
      .ok (Expr.case_ s bs)
    | "Elet" =>
      let (_, pat) ← getTaggedFieldMulti exprJ "pattern" patternTags
      let p ← parsePattern pat
      let binding ← getField exprJ "binding"
      let e1 ← parsePexpr binding
      let body ← getField exprJ "body"
      let e2 ← parseExpr body
      .ok (Expr.let_ p e1 e2)
    | "Eif" =>
      let cond ← getField exprJ "condition"
      let c ← parsePexpr cond
      let then_ ← getField exprJ "then_branch"
      let t ← parseExpr then_
      let else_ ← getField exprJ "else_branch"
      let e ← parseExpr else_
      .ok (Expr.if_ c t e)
    | "Eccall" =>
      -- "type" field contains the function type as a pexpr
      -- This is typically a PEval(Vctype(...)) but can also be a symbol or other
      -- expression that evaluates to a ctype at runtime
      let funTyJ ← getField exprJ "type"
      let funTy ← parsePexpr funTyJ
      let funPtrJ ← getField exprJ "function"
      let funPtr ← parsePexpr funPtrJ
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM parsePexpr
      .ok (Expr.ccall funPtr funTy as)
    | "Eproc" =>
      let (_, name) ← getTaggedFieldMulti exprJ "name" nameTags
      let n ← parseName name
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM parsePexpr
      .ok (Expr.proc n as)
    | "Eunseq" =>
      let es ← getArr exprJ "exprs"
      let exprs ← es.toList.mapM parseExpr
      .ok (Expr.unseq exprs)
    | "Ewseq" =>
      let (_, pat) ← getTaggedFieldMulti exprJ "pattern" patternTags
      let p ← parsePattern pat
      let left ← getField exprJ "left"
      let l ← parseExpr left
      let right ← getField exprJ "right"
      let r ← parseExpr right
      .ok (Expr.wseq p l r)
    | "Esseq" =>
      let (_, pat) ← getTaggedFieldMulti exprJ "pattern" patternTags
      let p ← parsePattern pat
      let left ← getField exprJ "left"
      let l ← parseExpr left
      let right ← getField exprJ "right"
      let r ← parseExpr right
      .ok (Expr.sseq p l r)
    | "Ebound" =>
      let e ← getField exprJ "expr"
      let ex ← parseExpr e
      .ok (Expr.bound ex)
    | "End" =>
      let es ← getArr exprJ "exprs"
      let exprs ← es.toList.mapM parseExpr
      .ok (Expr.nd exprs)
    | "Esave" =>
      let label ← getField exprJ "label"  -- Sym is not a tagged type
      let l ← parseSym label
      let (_, retTy) ← getTaggedFieldMulti exprJ "return_type" baseTypeTags
      let rt ← parseBaseType retTy
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM fun a => do
        let sym ← getField a "symbol"  -- Sym is not a tagged type
        let s ← parseSym sym
        let (_, ty) ← getTaggedFieldMulti a "type" baseTypeTags
        let t ← parseBaseType ty
        let value ← getField a "value"
        let v ← parsePexpr value
        .ok (s, t, v)
      let body ← getField exprJ "body"
      let b ← parseExpr body
      .ok (Expr.save l rt as b)
    | "Erun" =>
      let label ← getField exprJ "label"
      let l ← parseSym label
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM parsePexpr
      .ok (Expr.run l as)
    | "Epar" =>
      let es ← getArr exprJ "exprs"
      let exprs ← es.toList.mapM parseExpr
      .ok (Expr.par exprs)
    | "Ewait" =>
      let tid ← getNat exprJ "thread_id"
      .ok (Expr.wait tid)
    | "Eannot" =>
      -- Dynamic annotations are not serialized to JSON (they're runtime-only)
      -- Parse the inner expression with empty annotations
      let innerJ ← getField exprJ "expr"
      let inner ← parseExpr innerJ
      .ok (Expr.annot [] inner)
    | other => .error s!"unknown expr tag '{other}', expected one of {exprTags}"
    .ok { annots := annots, expr := expr }
end

/-- Parse an ImplDecl from JSON -/
def parseImplDecl (j : Json) : Except String ImplDecl := do
  let tag ← getTag j
  match tag with
  | "Def" =>
    let (_, tyJ) ← getTaggedFieldMulti j "type" baseTypeTags
    let ty ← parseBaseType tyJ
    let exprJ ← getField j "expr"
    let expr ← parsePexpr exprJ
    .ok (.def_ ty expr)
  | "IFun" =>
    let (_, tyJ) ← getTaggedFieldMulti j "return_type" baseTypeTags
    let ty ← parseBaseType tyJ
    let paramsJ ← getArr j "params"
    let params ← paramsJ.toList.mapM fun p => do
      let sym ← getField p "symbol" >>= parseSym
      let (_, ptyJ) ← getTaggedFieldMulti p "type" baseTypeTags
      let pty ← parseBaseType ptyJ
      pure (sym, pty)
    let bodyJ ← getField j "body"
    let body ← parsePexpr bodyJ
    .ok (.ifun ty params body)
  | _ => .error s!"unknown impl_decl tag: {tag}"

/-- Parse an impl entry (constant name + declaration) -/
def parseImplEntry (j : Json) : Except String (ImplConst × ImplDecl) := do
  let constStr ← getStr j "constant"
  let const ← parseImplConst constStr
  let declJ ← getField j "decl"
  let decl ← parseImplDecl declJ
  .ok (const, decl)

/-- Parse an extern entry (identifier + symbols + linking kind) -/
def parseExternEntry (j : Json) : Except String (Identifier × (List Sym × LinkingKind)) := do
  let idJ ← getField j "identifier"
  let id ← parseIdentifier idJ
  let symsJ ← getArr j "symbols"
  let syms ← symsJ.toList.mapM parseSym
  let lkJ ← getField j "linking_kind"
  let lk ← parseLinkingKind lkJ
  .ok (id, (syms, lk))

/-! ## File Parsing -/

/-- Parse a TagDef from JSON -/
def parseTagDef (j : Json) : Except String (Sym × Loc × TagDef) := do
  let sym ← getField j "symbol"  -- Sym is not a tagged type
  let s ← parseSym sym
  let locJ ← getField j "loc"
  let loc ← parseLoc locJ
  let (tag, defJ) ← getTaggedFieldMulti j "definition" tagDefTags
  let def_ ← match tag with
  | "StructDef" =>
    let fields ← getArr defJ "fields"
    let fs ← fields.toList.mapM fun f => do
      let name ← getField f "name"
      let n ← parseIdentifier name
      let (_, ctypeJ) ← getTaggedFieldMulti f "ctype" ctypeTags
      let cty ← parseCtype ctypeJ
      .ok { name := n, ty := cty : FieldDef }
    -- Parse optional flexible array member
    let flexOpt ← match getFieldOpt defJ "flexible_array" with
      | some flexJ =>
        if flexJ.isNull then .ok none
        else do
          let name ← getField flexJ "name"
          let n ← parseIdentifier name
          let (_, ctypeJ) ← getTaggedFieldMulti flexJ "ctype" ctypeTags
          let cty ← parseCtype ctypeJ
          .ok (some { name := n, ty := cty : FieldDef })
      | none => .ok none
    .ok (TagDef.struct_ fs flexOpt)
  | "UnionDef" =>
    let fields ← getArr defJ "fields"
    let fs ← fields.toList.mapM fun f => do
      let name ← getField f "name"
      let n ← parseIdentifier name
      let (_, ctypeJ) ← getTaggedFieldMulti f "ctype" ctypeTags
      let cty ← parseCtype ctypeJ
      .ok { name := n, ty := cty : FieldDef }
    .ok (TagDef.union_ fs)
  | other => .error s!"unknown tag definition tag '{other}', expected one of {tagDefTags}"
  .ok (s, loc, def_)

/-- Parse a GlobDecl from JSON -/
def parseGlobDecl (j : Json) : Except String (Sym × GlobDecl) := do
  let sym ← getField j "symbol"  -- Sym is not a tagged type
  let s ← parseSym sym
  let tag ← getTag j
  let (_, coreTy) ← getTaggedFieldMulti j "core_type" baseTypeTags
  let ct ← parseBaseType coreTy
  let (_, ctypeJ) ← getTaggedFieldMulti j "ctype" ctypeTags
  let cty ← parseCtype ctypeJ
  match tag with
  | "GlobalDef" =>
    let init ← getField j "init"
    let i ← parseExpr init
    .ok (s, .def_ ct cty i)
  | "GlobalDecl" =>
    .ok (s, .decl ct cty)
  | other => .error s!"unknown glob decl tag '{other}', expected one of {globDeclTags}"

/-- Parse a FunDecl from JSON -/
def parseFunDecl (j : Json) : Except String (Sym × FunDecl) := do
  let sym ← getField j "symbol"  -- Sym is not a tagged type
  let s ← parseSym sym
  let (tag, declJ) ← getTaggedFieldMulti j "declaration" funDeclTags
  match tag with
  | "Fun" =>
    let (_, retTy) ← getTaggedFieldMulti declJ "return_type" baseTypeTags
    let rt ← parseBaseType retTy
    let params ← getArr declJ "params"
    let ps ← params.toList.mapM fun p => do
      let sym ← getField p "symbol"  -- Sym is not a tagged type
      let s ← parseSym sym
      let (_, ty) ← getTaggedFieldMulti p "type" baseTypeTags
      let t ← parseBaseType ty
      .ok (s, t)
    let body ← getField declJ "body"
    let b ← parsePexpr body
    .ok (s, .fun_ rt ps b)
  | "Proc" =>
    let locJ ← getField declJ "loc"
    let loc ← parseLoc locJ
    -- Parse optional marker_env field
    let markerEnv : Option Nat := match declJ.getObjValAs? Json "marker_env" with
      | .ok (.num n) => some n.mantissa.toNat
      | _ => none
    let (_, retTy) ← getTaggedFieldMulti declJ "return_type" baseTypeTags
    let rt ← parseBaseType retTy
    let params ← getArr declJ "params"
    let ps ← params.toList.mapM fun p => do
      let sym ← getField p "symbol"  -- Sym is not a tagged type
      let s ← parseSym sym
      let (_, ty) ← getTaggedFieldMulti p "type" baseTypeTags
      let t ← parseBaseType ty
      .ok (s, t)
    let body ← getField declJ "body"
    let b ← parseExpr body
    .ok (s, .proc loc markerEnv rt ps b)
  | "ProcDecl" =>
    let locJ ← getField declJ "loc"
    let loc ← parseLoc locJ
    let (_, retTy) ← getTaggedFieldMulti declJ "return_type" baseTypeTags
    let rt ← parseBaseType retTy
    let paramTys ← getArr declJ "param_types"
    let pts ← paramTys.toList.mapM parseBaseType
    .ok (s, .procDecl loc rt pts)
  | "BuiltinDecl" =>
    let locJ ← getField declJ "loc"
    let loc ← parseLoc locJ
    let (_, retTy) ← getTaggedFieldMulti declJ "return_type" baseTypeTags
    let rt ← parseBaseType retTy
    let paramTys ← getArr declJ "param_types"
    let pts ← paramTys.toList.mapM parseBaseType
    .ok (s, .builtinDecl loc rt pts)
  | other => .error s!"unknown fun decl tag '{other}', expected one of {funDeclTags}"

/-- Parse a single CN magic annotation from JSON
    Corresponds to: cerb::magic attribute in Annot.attributes
    JSON format: { "loc": {...}, "text": "..." } -/
def parseCnMagicAnnotation (j : Json) : Except String CnMagicAnnotation := do
  let locJ ← getField j "loc"
  let loc ← parseLoc locJ
  let text ← match getFieldOpt j "text" with
    | some (.str s) => pure s
    | some _ => .error "cn_magic text must be a string"
    | none => .error "cn_magic entry missing 'text' field"
  pure { loc, text }

/-- Parse a FunInfo entry from JSON -/
def parseFunInfoEntry (j : Json) : Except String (Sym × FunInfo) := do
  let symJ ← getField j "symbol"
  let sym ← parseSym symJ
  let locJ ← getField j "loc"
  let loc ← parseLoc locJ
  -- Parse CN magic annotations (optional, may be empty array or missing)
  -- These come from `/*@ ... @*/` comments when parsed with --switches=at_magic_comments
  let cnMagic ← match getFieldOpt j "cn_magic" with
    | some (.arr arr) => arr.toList.mapM parseCnMagicAnnotation
    | some _ => .error "cn_magic must be an array"
    | none => pure []
  let (_, retTyJ) ← getTaggedFieldMulti j "return_type" ctypeTags
  let returnType ← parseCtype retTyJ
  let paramsJ ← getArr j "params"
  let params ← paramsJ.toList.mapM fun p => do
    let symOpt ← match getFieldOpt p "symbol" with
      | some s => if s.isNull then pure none else do
          let sym ← parseSym s
          pure (some sym)
      | none => pure none
    let (_, tyJ) ← getTaggedFieldMulti p "type" ctypeTags
    let ty ← parseCtype tyJ
    pure { sym := symOpt, ty := ty : FunParam }
  let isVariadic ← match getFieldOpt j "is_variadic" with
    | some (.bool b) => pure b
    | _ => pure false
  let hasProto ← match getFieldOpt j "has_proto" with
    | some (.bool b) => pure b
    | _ => pure true
  pure (sym, { loc, cnMagic, returnType, params, isVariadic, hasProto })

/-- Parse a complete Core File from JSON -/
def parseFile (j : Json) : Except String File := do
  -- Parse main symbol
  let main ← match getFieldOpt j "main" with
    | some v => if v.isNull then .ok none else do
        let sym ← parseSym v
        .ok (some sym)
    | none => .ok none

  -- Parse tag definitions (preserve order from JSON)
  let tagDefsJ ← getArr j "tagDefs"
  let tagDefsList ← tagDefsJ.toList.mapM parseTagDef
  let tagDefs : TagDefs := tagDefsList.map fun (s, l, d) => (s, (l, d))

  -- Parse stdlib functions (if present)
  let stdlib ← match getFieldOpt j "stdlib" with
    | some stdlibJ =>
      let arr ← match stdlibJ with
        | .arr a => .ok a
        | _ => .error "stdlib must be an array"
      arr.toList.mapM parseFunDecl
    | none => .ok []

  -- Parse implementation-defined constants (if present)
  let impl ← match getFieldOpt j "impl" with
    | some implJ =>
      let arr ← match implJ with
        | .arr a => .ok a
        | _ => .error "impl must be an array"
      let entries ← arr.toList.mapM parseImplEntry
      let map := entries.foldl (fun m (c, d) => m.insert c d) ({} : ImplDefs)
      .ok map
    | none => .ok {}

  -- Parse global declarations
  let globsJ ← getArr j "globs"
  let globs ← globsJ.toList.mapM parseGlobDecl

  -- Parse function definitions (preserve order from JSON)
  let funsJ ← getArr j "funs"
  let funs ← funsJ.toList.mapM parseFunDecl

  -- Parse external symbol mapping (if present)
  let extern ← match getFieldOpt j "extern" with
    | some externJ =>
      let arr ← match externJ with
        | .arr a => .ok a
        | _ => .error "extern must be an array"
      let entries ← arr.toList.mapM parseExternEntry
      let map := entries.foldl (fun m (id, v) => m.insert id v) ({} : Std.HashMap Identifier (List Sym × LinkingKind))
      .ok map
    | none => .ok {}

  -- Parse function info map (for cfunction expression)
  let funinfo ← match getFieldOpt j "funinfo" with
    | some funinfoJ =>
      let arr ← match funinfoJ with
        | .arr a => .ok a
        | _ => .error "funinfo must be an array"
      let entries ← arr.toList.mapM parseFunInfoEntry
      let map := entries.foldl (fun m (s, fi) => m.insert s fi) ({} : FunInfoMap)
      .ok map
    | none => .ok {}

  .ok {
    main := main
    tagDefs := tagDefs
    stdlib := stdlib
    impl := impl
    globs := globs
    funs := funs
    extern := extern
    funinfo := funinfo
  }

/-- Parse a Core File from a JSON string -/
def parseFileFromString (s : String) : Except String File := do
  let json ← Json.parse s
  parseFile json

end CerbLean.Parser
