/-
  JSON parser for Cerberus Core output
  Uses Lean's built-in JSON library to deserialize Core IR
-/

import Lean.Data.Json
import CToLean.Core

open Lean (Json ToJson FromJson)
open CToLean.Core

namespace CToLean.Parser

/-! ## JSON Parsing Utilities -/

/-- Get a required field from a JSON object -/
def getField (obj : Json) (field : String) : Except String Json :=
  obj.getObjVal? field

/-- Get an optional field from a JSON object -/
def getFieldOpt (obj : Json) (field : String) : Option Json :=
  match obj.getObjVal? field with
  | .ok v => some v
  | .error _ => none

/-- Get a required string field -/
def getStr (obj : Json) (field : String) : Except String String := do
  let v ← getField obj field
  v.getStr?

/-- Get a required integer field -/
def getInt (obj : Json) (field : String) : Except String Int := do
  let v ← getField obj field
  v.getInt?

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
  let s ← j.getStr?
  .ok { name := s }

/-- Parse a Loc from JSON -/
def parseLoc (j : Json) : Except String Loc := do
  -- Locations can be strings like "file:line:col-line:col" or structured
  match j.getStr? with
  | .ok s =>
    -- Simple string format - just store file name for now
    .ok { file := s, startLine := 0, startCol := 0, endLine := 0, endCol := 0 }
  | .error _ =>
    -- Try structured format
    let file ← getStr j "file"
    let startLine ← getNat j "start_line"
    let startCol ← getNat j "start_col"
    let endLine ← getNat j "end_line"
    let endCol ← getNat j "end_col"
    .ok { file, startLine, startCol, endLine, endCol }

/-- Parse annotations from JSON -/
def parseAnnots (j : Json) : Annots :=
  match getFieldOpt j "loc" with
  | some locJson =>
    match parseLoc locJson with
    | .ok loc => [.loc loc]
    | .error _ => []
  | none => []

/-! ## Type Parsing -/

/-- Parse an ObjectType from JSON -/
partial def parseObjectType (j : Json) : Except String ObjectType := do
  let tag ← getTag j
  match tag with
  | "OTy_integer" => .ok .integer
  | "OTy_floating" => .ok .floating
  | "OTy_pointer" => .ok .pointer
  | "OTy_array" =>
    let elem ← getField j "element"
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
  | _ => .error s!"unknown object type: {tag}"

/-- Parse a BaseType from JSON -/
partial def parseBaseType (j : Json) : Except String BaseType := do
  let tag ← getTag j
  match tag with
  | "BTy_unit" => .ok .unit
  | "BTy_boolean" => .ok .boolean
  | "BTy_ctype" => .ok .ctype
  | "BTy_storable" => .ok .storable
  | "BTy_list" =>
    let elem ← getField j "element"
    let elemTy ← parseBaseType elem
    .ok (.list elemTy)
  | "BTy_tuple" =>
    let elems ← getArr j "elements"
    let elemTys ← elems.toList.mapM parseBaseType
    .ok (.tuple elemTys)
  | "BTy_object" =>
    let objTy ← getField j "object_type"
    let oty ← parseObjectType objTy
    .ok (.object oty)
  | "BTy_loaded" =>
    let objTy ← getField j "object_type"
    let oty ← parseObjectType objTy
    .ok (.loaded oty)
  | _ => .error s!"unknown base type: {tag}"

/-- Parse a Ctype from a string representation -/
-- The JSON outputs ctypes as strings like "signed int", "char*", etc.
partial def parseCtypeStr (s : String) : Except String Ctype := do
  -- Strip trailing whitespace
  let s := s.trim
  -- Handle pointer types (but not function types with parentheses)
  if s.endsWith "*" then
    let inner := s.dropRight 1 |>.trim
    let innerTy ← parseCtypeStr inner
    return .pointer {} innerTy
  -- Handle atomic types BEFORE function types (since _Atomic(x) ends with ')')
  else if s.startsWith "_Atomic" then
    let rest := s.drop 7 |>.trim
    if rest.startsWith "(" && rest.endsWith ")" then
      let inner := (rest.toSubstring.drop 1 |>.dropRight 1).toString.trim
      let innerTy ← parseCtypeStr inner
      return .atomic innerTy
    else
      throw s!"malformed _Atomic type: {s}"
  -- Handle function types like "int ()" or "int (int, int)"
  else if s.endsWith ")" && s.contains '(' then
    -- Find matching open paren from the end
    let parenIdx := s.find (· == '(')
    let retStr := (s.toSubstring.take parenIdx.byteIdx).toString.trim
    let retTy ← parseCtypeStr retStr
    -- Parse params (simplified - we don't need them precisely)
    return .function retTy [] false
  -- Handle array types
  else if s.contains '[' then
    -- Parse array like "int[10]" or "char[]"
    let bracketIdx := s.find (· == '[')
    let elemStr := (s.toSubstring.take bracketIdx.byteIdx).toString.trim
    let closeBracket := s.length - 1
    let sizeStr := (s.toSubstring.drop (bracketIdx.byteIdx + 1) |>.take (closeBracket - bracketIdx.byteIdx - 1)).toString
    let elemTy ← parseCtypeStr elemStr
    let size := if sizeStr.isEmpty then none else sizeStr.toNat?
    return .array elemTy size
  -- Handle basic types
  else if s == "void" then return .void
  else if s == "char" then return .basic (.integer .char)
  else if s == "_Bool" then return .basic (.integer .bool)
  else if s == "signed char" || s == "signed ichar" then return .basic (.integer (.signed .ichar))
  else if s == "unsigned char" || s == "unsigned ichar" then return .basic (.integer (.unsigned .ichar))
  else if s == "short" || s == "signed short" || s == "short int" || s == "signed short int" then
    return .basic (.integer (.signed .short))
  else if s == "unsigned short" || s == "unsigned short int" then
    return .basic (.integer (.unsigned .short))
  else if s == "int" || s == "signed" || s == "signed int" then
    return .basic (.integer (.signed .int_))
  else if s == "unsigned" || s == "unsigned int" then
    return .basic (.integer (.unsigned .int_))
  else if s == "long" || s == "signed long" || s == "long int" || s == "signed long int" then
    return .basic (.integer (.signed .long))
  else if s == "unsigned long" || s == "unsigned long int" then
    return .basic (.integer (.unsigned .long))
  else if s == "long long" || s == "signed long long" || s == "long long int" || s == "signed long long int" then
    return .basic (.integer (.signed .longLong))
  else if s == "unsigned long long" || s == "unsigned long long int" then
    return .basic (.integer (.unsigned .longLong))
  else if s == "float" then return .basic (.floating .float)
  else if s == "double" then return .basic (.floating .double)
  else if s == "long double" then return .basic (.floating .longDouble)
  -- Handle common typedefs (map to void, since we just need them to parse)
  else if s == "size_t" || s == "ssize_t" || s == "ptrdiff_t" ||
          s == "intptr_t" || s == "uintptr_t" ||
          s == "int8_t" || s == "int16_t" || s == "int32_t" || s == "int64_t" ||
          s == "uint8_t" || s == "uint16_t" || s == "uint32_t" || s == "uint64_t" then
    return .basic (.integer (.signed .int_))  -- Simplification
  -- Handle struct/union types
  else if s.startsWith "struct " then
    let tag := s.drop 7
    return .struct_ { id := 0, name := some tag }
  else if s.startsWith "union " then
    let tag := s.drop 6
    return .union_ { id := 0, name := some tag }
  -- Handle enum types
  else if s.startsWith "enum " then
    let tag := s.drop 5
    return .basic (.integer (.enum { id := 0, name := some tag }))
  -- Fallback - treat unknown types as void (with warning in future)
  else
    -- For any unrecognized type, use void as a placeholder
    return .void

def parseCtype (j : Json) : Except String Ctype := do
  match j with
  | .str s => parseCtypeStr s
  | _ => throw "expected ctype string"

/-! ## Value Parsing -/

/-- Parse a Ctor from JSON -/
def parseCtor (j : Json) : Except String Ctor := do
  let tag ← getTag j
  match tag with
  | "Cnil" =>
    let ty ← getField j "type"
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
  | _ => .error s!"unknown constructor: {tag}"

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
    let ctyStr ← getStr j "ctype"
    let cty ← parseCtypeStr ctyStr
    .ok (.static cty)
  | _ => .error s!"unknown kill kind: {tag}"

/-- Parse a Name from JSON -/
def parseName (j : Json) : Except String Name := do
  let tag ← getTag j
  match tag with
  | "Sym" =>
    let sym ← getField j "symbol"
    let s ← parseSym sym
    .ok (.sym s)
  | "Impl" =>
    let c ← getStr j "constant"
    .ok (.impl (.other c))
  | _ => .error s!"unknown name kind: {tag}"

/-- Parse an Iop (integer operation) from JSON -/
def parseIop (j : Json) : Except String Iop := do
  let s ← j.getStr?
  match s with
  | "IOpAdd" => return CToLean.Core.Iop.add
  | "IOpSub" => return CToLean.Core.Iop.sub
  | "IOpMul" => return CToLean.Core.Iop.mul
  | "IOpShl" => return CToLean.Core.Iop.shl
  | "IOpShr" => return CToLean.Core.Iop.shr
  | "IOpDiv" => return CToLean.Core.Iop.div
  | "IOpRem_t" => return CToLean.Core.Iop.rem_t
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

/-- Parse a Memop from a string representation -/
def parseMemop (s : String) : Except String Memop :=
  -- The memop is pretty-printed as a string like "PtrEq", "IntFromPtr", etc.
  -- Handle PtrMemberShift specially since it has extra info in brackets
  if s.startsWith "PtrArrayShift[" then
    -- This is actually PtrMemberShift with [tag, member] info
    -- For now, just treat as ptrArrayShift since parsing brackets is complex
    .ok .ptrArrayShift
  else if s.startsWith "cheri_" then
    .ok (.cheriIntrinsic s)
  else
    match s with
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
    | "Memcpy" => .ok .memcpy
    | "Memcmp" => .ok .memcmp
    | "Realloc" => .ok .realloc
    | "Va_start" => .ok .vaStart
    | "Va_copy" => .ok .vaCopy
    | "Va_arg" => .ok .vaArg
    | "Va_end" => .ok .vaEnd
    | "Copy_alloc_id" => .ok .copyAllocId
    | _ => .error s!"unknown memop: {s}"

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
        -- Handle special string values with proper types
        let fv := match s with
          | "unspecified" => FloatingValue.unspecified
          | "NaN" => FloatingValue.nan
          | "Infinity" => FloatingValue.posInf
          | "-Infinity" => FloatingValue.negInf
          | _ =>
            -- Try parsing as number string
            match s.toNat? with
            | some n => FloatingValue.finite n.toFloat
            | none => FloatingValue.finite 0.0  -- Fallback
        .ok (.floating fv)
      | .num n => .ok (.floating (.finite n.toFloat))
      | _ => .error "OVfloating value must be string or number"
    | "OVpointer" =>
      let valStr ← getStr j "value"
      -- Parse pointer value string: NULL(ctype), Cfunction(sym), or (prov, 0xaddr)
      if valStr.startsWith "NULL(" && valStr.endsWith ")" then
        let ctypeStr := (valStr.drop 5).dropRight 1  -- Remove "NULL(" and ")"
        match parseCtypeStr ctypeStr with
        | .ok cty => .ok (.pointer { prov := .none, base := .null cty })
        | .error _ => .ok (.pointer { prov := .none, base := .null .void })
      else if valStr.startsWith "Cfunction(" then
        -- Function pointer - parse symbol name
        let symName := (valStr.drop 10).dropRight 1  -- Remove "Cfunction(" and ")"
        .ok (.pointer { prov := .none, base := .function { id := 0, name := some symName } })
      else
        -- Concrete pointer: (prov, 0xaddr) - parse address
        -- For now, extract hex address if present
        let parts := valStr.splitOn "0x"
        let addr := if parts.length > 1 then
          let hexPart := parts[1]!.takeWhile (·.isAlphanum)
          hexPart.foldl (fun acc c =>
            let digit := if c.isDigit then c.toNat - '0'.toNat
                        else if c.toLower >= 'a' && c.toLower <= 'f' then c.toLower.toNat - 'a'.toNat + 10
                        else 0
            acc * 16 + digit) 0
        else 0
        .ok (.pointer { prov := .none, base := .concrete none addr })
    | "OVarray" =>
      let elems ← getArr j "elements"
      let lvs ← elems.toList.mapM parseLoadedValue
      .ok (.array lvs)
    | "OVstruct" =>
      let tagSym ← getField j "struct_tag"
      let sym ← parseSym tagSym
      let membersArr ← getArr j "members"
      let members ← membersArr.toList.mapM fun m => do
        let nameJ ← getField m "name"
        let name ← parseIdentifier nameJ
        let ctypeStr ← getStr m "ctype"
        let ctype ← parseCtypeStr ctypeStr
        -- Value is a string representation of mem_value - store as unspecified for now
        -- Full parsing would require interpreting the pp_mem_value output
        pure { name := name, ty := ctype, value := .unspecified ctype : StructMember }
      .ok (.struct_ sym members)
    | "OVunion" =>
      let tagSym ← getField j "union_tag"
      let sym ← parseSym tagSym
      let member ← getField j "member"
      let id ← parseIdentifier member
      -- Value is a string representation - store as unspecified for now
      .ok (.union_ sym id (.unspecified .void))
    | _ => .error s!"unknown object value: {tag}"

  /-- Parse a LoadedValue from JSON -/
  partial def parseLoadedValue (j : Json) : Except String LoadedValue := do
    let tag ← getTag j
    match tag with
    | "LVspecified" =>
      let v ← getField j "value"
      let ov ← parseObjectValue v
      .ok (.specified ov)
    | "LVunspecified" =>
      let ctyStr ← getStr j "ctype"
      let cty ← parseCtypeStr ctyStr
      .ok (.unspecified cty)
    | _ => .error s!"unknown loaded value: {tag}"

  /-- Parse a Value from JSON -/
  partial def parseValue (j : Json) : Except String Value := do
    let tag ← getTag j
    match tag with
    | "Vunit" => .ok .unit
    | "Vtrue" => .ok .true_
    | "Vfalse" => .ok .false_
    | "Vctype" =>
      let ctyStr ← getStr j "ctype"
      let cty ← parseCtypeStr ctyStr
      .ok (.ctype cty)
    | "Vobject" =>
      let v ← getField j "value"
      let ov ← parseObjectValue v
      .ok (.object ov)
    | "Vloaded" =>
      let v ← getField j "value"
      let lv ← parseLoadedValue v
      .ok (.loaded lv)
    | "Vlist" =>
      let ty ← getField j "type"
      let bty ← parseBaseType ty
      let elems ← getArr j "elements"
      let vs ← elems.toList.mapM parseValue
      .ok (.list bty vs)
    | "Vtuple" =>
      let elems ← getArr j "elements"
      let vs ← elems.toList.mapM parseValue
      .ok (.tuple vs)
    | _ => .error s!"unknown value: {tag}"

  /-- Parse a Pattern from JSON -/
  partial def parsePattern (j : Json) : Except String APattern := do
    let tag ← getTag j
    let annots := parseAnnots j
    match tag with
    | "CaseBase" =>
      let symOpt ← match getFieldOpt j "symbol" with
        | some v => if v.isNull then .ok none else do
            let sym ← parseSym v
            .ok (some sym)
        | none => .ok none
      let ty ← getField j "type"
      let bty ← parseBaseType ty
      .ok { annots := annots, pat := .base symOpt bty }
    | "CaseCtor" =>
      let ctor ← getField j "constructor"
      let c ← parseCtor ctor
      let pats ← getArr j "patterns"
      let ps ← pats.toList.mapM parsePattern
      .ok { annots := annots, pat := .ctor c (ps.map (·.pat)) }
    | _ => .error s!"unknown pattern: {tag}"

  /-- Parse a Pexpr (pure expression) from JSON -/
  partial def parsePexpr (j : Json) : Except String APexpr := do
    let annots := parseAnnots j
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
      let v ← getField exprJ "value"
      let val ← parseValue v
      .ok (Pexpr.val val)
    | "PEundef" =>
      let locJ ← getField exprJ "loc"
      let loc ← match parseLoc locJ with
        | .ok l => .ok l
        | .error _ => .ok Loc.unknown
      let ubStr ← getStr exprJ "ub"
      .ok (Pexpr.undef loc (.other ubStr))
    | "PEerror" =>
      let msg ← getStr exprJ "message"
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.error msg pe.expr)
    | "PEctor" =>
      let ctor ← getField exprJ "constructor"
      let c ← parseCtor ctor
      let args ← getArr exprJ "args"
      let pes ← args.toList.mapM parsePexpr
      .ok (Pexpr.ctor c (pes.map (·.expr)))
    | "PEcase" =>
      let scrut ← getField exprJ "scrutinee"
      let s ← parsePexpr scrut
      let branches ← getArr exprJ "branches"
      let bs ← branches.toList.mapM fun b => do
        let pat ← getField b "pattern"
        let body ← getField b "body"
        let p ← parsePattern pat
        let e ← parsePexpr body
        .ok (p, e.expr)
      .ok (Pexpr.case_ s.expr bs)
    | "PEarray_shift" =>
      let ptr ← getField exprJ "ptr"
      let p ← parsePexpr ptr
      let ctypeStr ← getStr exprJ "ctype"
      let ctype ← parseCtypeStr ctypeStr
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
      let name ← getField exprJ "name"
      let n ← parseName name
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM parsePexpr
      .ok (Pexpr.call n (as.map (·.expr)))
    | "PElet" =>
      let pat ← getField exprJ "pattern"
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
      let tyStr ← getStr exprJ "type"
      let ty ← parseIntegerTypeStr tyStr
      let op ← getField exprJ "op"
      let iop ← parseIop op
      let l ← getField exprJ "left"
      let r ← getField exprJ "right"
      let le ← parsePexpr l
      let re ← parsePexpr r
      .ok (Pexpr.wrapI ty iop le.expr re.expr)
    | "PEcatch_exceptional_condition" =>
      let tyStr ← getStr exprJ "type"
      let ty ← parseIntegerTypeStr tyStr
      let op ← getField exprJ "op"
      let iop ← parseIop op
      let l ← getField exprJ "left"
      let r ← getField exprJ "right"
      let le ← parsePexpr l
      let re ← parsePexpr r
      .ok (Pexpr.catchExceptionalCondition ty iop le.expr re.expr)
    | "PEconv_int" =>
      let tyStr ← getStr exprJ "type"
      let ty ← parseIntegerTypeStr tyStr
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.convInt ty pe.expr)
    | "PEbmc_assume" =>
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Pexpr.bmcAssume pe.expr)
    | "PEmemop" =>
      let op ← getStr exprJ "op"
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
    | _ => .error s!"unknown pexpr: {tag}"
    .ok { annots := annots, ty := none, expr := expr }

  /-- Parse an Action from JSON -/
  partial def parseAction (j : Json) : Except String AAction := do
    let loc := match getFieldOpt j "loc" with
      | some locJson =>
        match parseLoc locJson with
        | .ok l => l
        | .error _ => Loc.unknown
      | none => Loc.unknown
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
      let kind ← getField actJ "kind"
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
    | _ => .error s!"unknown action: {tag}"
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
    let annots := parseAnnots j
    let exprJ ← getField j "expr"
    let tag ← getTag exprJ
    let expr ← match tag with
    | "Epure" =>
      let e ← getField exprJ "expr"
      let pe ← parsePexpr e
      .ok (Expr.pure pe)
    | "Ememop" =>
      let opStr ← getStr exprJ "op"
      let op ← parseMemop opStr
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
        let pat ← getField b "pattern"
        let body ← getField b "body"
        let p ← parsePattern pat
        let e ← parseExpr body
        .ok (p, e.expr)
      .ok (Expr.case_ s bs)
    | "Elet" =>
      let pat ← getField exprJ "pattern"
      let p ← parsePattern pat
      let binding ← getField exprJ "binding"
      let e1 ← parsePexpr binding
      let body ← getField exprJ "body"
      let e2 ← parseExpr body
      .ok (Expr.let_ p e1 e2.expr)
    | "Eif" =>
      let cond ← getField exprJ "condition"
      let c ← parsePexpr cond
      let then_ ← getField exprJ "then_branch"
      let t ← parseExpr then_
      let else_ ← getField exprJ "else_branch"
      let e ← parseExpr else_
      .ok (Expr.if_ c t.expr e.expr)
    | "Eccall" =>
      let funPtr ← getField exprJ "function"
      let f ← parsePexpr funPtr
      let funTy ← getField exprJ "type"
      let t ← parsePexpr funTy
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM parsePexpr
      .ok (Expr.ccall f t as)
    | "Eproc" =>
      let name ← getField exprJ "name"
      let n ← parseName name
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM parsePexpr
      .ok (Expr.proc n as)
    | "Eunseq" =>
      let es ← getArr exprJ "exprs"
      let exprs ← es.toList.mapM parseExpr
      .ok (Expr.unseq (exprs.map (·.expr)))
    | "Ewseq" =>
      let pat ← getField exprJ "pattern"
      let p ← parsePattern pat
      let left ← getField exprJ "left"
      let l ← parseExpr left
      let right ← getField exprJ "right"
      let r ← parseExpr right
      .ok (Expr.wseq p l.expr r.expr)
    | "Esseq" =>
      let pat ← getField exprJ "pattern"
      let p ← parsePattern pat
      let left ← getField exprJ "left"
      let l ← parseExpr left
      let right ← getField exprJ "right"
      let r ← parseExpr right
      .ok (Expr.sseq p l.expr r.expr)
    | "Ebound" =>
      let e ← getField exprJ "expr"
      let ex ← parseExpr e
      .ok (Expr.bound ex.expr)
    | "End" =>
      let es ← getArr exprJ "exprs"
      let exprs ← es.toList.mapM parseExpr
      .ok (Expr.nd (exprs.map (·.expr)))
    | "Esave" =>
      let label ← getField exprJ "label"
      let l ← parseSym label
      let retTy ← getField exprJ "return_type"
      let rt ← parseBaseType retTy
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM fun a => do
        let sym ← getField a "symbol"
        let s ← parseSym sym
        let ty ← getField a "type"
        let t ← parseBaseType ty
        let value ← getField a "value"
        let v ← parsePexpr value
        .ok (s, t, v)
      let body ← getField exprJ "body"
      let b ← parseExpr body
      .ok (Expr.save l rt as b.expr)
    | "Erun" =>
      let label ← getField exprJ "label"
      let l ← parseSym label
      let args ← getArr exprJ "args"
      let as ← args.toList.mapM parsePexpr
      .ok (Expr.run l as)
    | "Epar" =>
      let es ← getArr exprJ "exprs"
      let exprs ← es.toList.mapM parseExpr
      .ok (Expr.par (exprs.map (·.expr)))
    | "Ewait" =>
      let tid ← getNat exprJ "thread_id"
      .ok (Expr.wait tid)
    | _ => .error s!"unknown expr: {tag}"
    .ok { annots := annots, expr := expr }
end

/-! ## File Parsing -/

/-- Parse a TagDef from JSON -/
def parseTagDef (j : Json) : Except String (Sym × Loc × TagDef) := do
  let sym ← getField j "symbol"
  let s ← parseSym sym
  let locJ ← getField j "loc"
  let loc := match parseLoc locJ with
    | .ok l => l
    | .error _ => Loc.unknown
  let defJ ← getField j "definition"
  let tag ← getTag defJ
  let def_ ← match tag with
  | "StructDef" =>
    let fields ← getArr defJ "fields"
    let fs ← fields.toList.mapM fun f => do
      let name ← getField f "name"
      let n ← parseIdentifier name
      -- ctype is stored as string
      .ok { name := n, ty := .void : FieldDef }
    .ok (TagDef.struct_ fs)
  | "UnionDef" =>
    let fields ← getArr defJ "fields"
    let fs ← fields.toList.mapM fun f => do
      let name ← getField f "name"
      let n ← parseIdentifier name
      .ok { name := n, ty := .void : FieldDef }
    .ok (TagDef.union_ fs)
  | _ => .error s!"unknown tag definition: {tag}"
  .ok (s, loc, def_)

/-- Parse a GlobDecl from JSON -/
def parseGlobDecl (j : Json) : Except String (Sym × GlobDecl) := do
  let sym ← getField j "symbol"
  let s ← parseSym sym
  let tag ← getStr j "tag"
  let coreTy ← getField j "core_type"
  let ct ← parseBaseType coreTy
  match tag with
  | "GlobalDef" =>
    let init ← getField j "init"
    let i ← parseExpr init
    .ok (s, .def_ ct .void i)
  | "GlobalDecl" =>
    .ok (s, .decl ct .void)
  | _ => .error s!"unknown glob decl: {tag}"

/-- Parse a FunDecl from JSON -/
def parseFunDecl (j : Json) : Except String (Sym × FunDecl) := do
  let sym ← getField j "symbol"
  let s ← parseSym sym
  let declJ ← getField j "declaration"
  let tag ← getTag declJ
  match tag with
  | "Fun" =>
    let retTy ← getField declJ "return_type"
    let rt ← parseBaseType retTy
    let params ← getArr declJ "params"
    let ps ← params.toList.mapM fun p => do
      let sym ← getField p "symbol"
      let s ← parseSym sym
      let ty ← getField p "type"
      let t ← parseBaseType ty
      .ok (s, t)
    let body ← getField declJ "body"
    let b ← parsePexpr body
    .ok (s, .fun_ rt ps b)
  | "Proc" =>
    let locJ ← getField declJ "loc"
    let loc := match parseLoc locJ with
      | .ok l => l
      | .error _ => Loc.unknown
    let retTy ← getField declJ "return_type"
    let rt ← parseBaseType retTy
    let params ← getArr declJ "params"
    let ps ← params.toList.mapM fun p => do
      let sym ← getField p "symbol"
      let s ← parseSym sym
      let ty ← getField p "type"
      let t ← parseBaseType ty
      .ok (s, t)
    let body ← getField declJ "body"
    let b ← parseExpr body
    .ok (s, .proc loc rt ps b)
  | "ProcDecl" =>
    let locJ ← getField declJ "loc"
    let loc := match parseLoc locJ with
      | .ok l => l
      | .error _ => Loc.unknown
    let retTy ← getField declJ "return_type"
    let rt ← parseBaseType retTy
    let paramTys ← getArr declJ "param_types"
    let pts ← paramTys.toList.mapM parseBaseType
    .ok (s, .procDecl loc rt pts)
  | "BuiltinDecl" =>
    let locJ ← getField declJ "loc"
    let loc := match parseLoc locJ with
      | .ok l => l
      | .error _ => Loc.unknown
    let retTy ← getField declJ "return_type"
    let rt ← parseBaseType retTy
    let paramTys ← getArr declJ "param_types"
    let pts ← paramTys.toList.mapM parseBaseType
    .ok (s, .builtinDecl loc rt pts)
  | _ => .error s!"unknown fun decl: {tag}"

/-- Parse a complete Core File from JSON -/
def parseFile (j : Json) : Except String File := do
  -- Parse main symbol
  let main ← match getFieldOpt j "main" with
    | some v => if v.isNull then .ok none else do
        let sym ← parseSym v
        .ok (some sym)
    | none => .ok none

  -- Parse tag definitions
  let tagDefsJ ← getArr j "tagDefs"
  let tagDefsList ← tagDefsJ.toList.mapM parseTagDef
  let tagDefs : TagDefs := tagDefsList.foldl (fun m (s, l, d) => m.insert s (l, d)) {}

  -- Parse global declarations
  let globsJ ← getArr j "globs"
  let globs ← globsJ.toList.mapM parseGlobDecl

  -- Parse function definitions
  let funsJ ← getArr j "funs"
  let funsList ← funsJ.toList.mapM parseFunDecl
  let funs : FunMap := funsList.foldl (fun m (s, d) => m.insert s d) {}

  .ok {
    main := main
    tagDefs := tagDefs
    globs := globs
    funs := funs
  }

/-- Parse a Core File from a JSON string -/
def parseFileFromString (s : String) : Except String File := do
  let json ← Json.parse s
  parseFile json

end CToLean.Parser
