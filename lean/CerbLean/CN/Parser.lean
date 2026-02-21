/-
  CN Specification Parser
  Parses CN magic comment strings into structured FunctionSpec ASTs.

  This parser handles the CN specification language used in function contracts.
  It is designed to be called from the JSON parser after extracting raw magic strings.

  Grammar (simplified ABNF, based on cerberus/parsers/c/c_parser.mly):
  ```
  function_spec  = [trusted] [requires_clause] [ensures_clause]

  requires_clause = "requires" condition+
  ensures_clause  = "ensures" condition+

  condition      = take_clause
                 | let_clause
                 | constraint ";"

  take_clause    = "take" IDENT "=" resource ";"
  let_clause     = "let" IDENT "=" expr ";"
  constraint     = expr

  resource       = pred "(" expr_list ")"
  pred           = ("Owned" | "RW") ["<" ctype ">"]  -- type optional, inferred from pointer
                 | ("Block" | "W")  ["<" ctype ">"]  -- type optional, inferred from pointer
                 | UNAME                     -- user-defined predicate

  expr           = binary_expr ["?" expr ":" expr]
  binary_expr    = unary_expr (binop unary_expr)*
  unary_expr     = "-" unary_expr | "!" unary_expr | "~" unary_expr (bitwise complement)
                 | postfix_expr
  postfix_expr   = atom_expr ("." IDENT | "->" IDENT)*
  atom_expr      = IDENT | NUMBER | "(" expr ")" | "(" cn_base_type ")" unary_expr
                 | "return" | "null" | "true" | "false"
                 | IDENT "(" expr_list ")"   -- function call
  binop          = "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||" | "implies"
                 | "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^"

  cn_base_type   = "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | ...
  ctype          = [sign] [size] [base] ["*"]*  -- C type for resources
  NUMBER         = DIGITS [("i" | "u") DIGITS]  -- optional type suffix (e.g. 42i32, 0u8)
  IDENT          = [a-zA-Z_][a-zA-Z0-9_]*
  UNAME          = [A-Z][a-zA-Z0-9_]*        -- starts with uppercase
  ```

  Reference: cerberus/parsers/c/c_parser.mly lines 2300-2500
  Audited: 2026-02-06
-/

import Std.Internal.Parsec
import Std.Internal.Parsec.String
import CerbLean.CN.Types
import CerbLean.Core.Ctype

namespace CerbLean.CN.Parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String
open CerbLean.Core (Sym Identifier Loc Ctype IntegerType IntBaseKind)
open CerbLean.CN.Types

/-! ## Parser Type and Utilities -/

/-- CN parser type alias -/
abbrev P := Parser

/-- Run a parser on a string, returning Either error or result -/
def runParser (p : P α) (input : String) : Except String α :=
  Parser.run p input

/-! ## Character Classes -/

/-- Is this an identifier start character? -/
def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

/-- Is this an identifier continuation character? -/
def isIdentCont (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-! ## Basic Parsers -/

/-- Parse with surrounding whitespace skipped -/
def lexeme (p : P α) : P α := do
  let r ← p
  ws
  pure r

/-- Parse a specific keyword (must not be followed by identifier char) -/
def keyword (s : String) : P Unit := lexeme do
  let _ ← pstring s
  let next ← peek?
  match next with
  | some c => if isIdentCont c then fail s!"expected keyword '{s}'" else pure ()
  | none => pure ()

/-- Parse a specific symbol -/
def symbol (s : String) : P Unit := lexeme (skipString s)

/-- Parse an identifier -/
def ident : P String := lexeme do
  let first ← satisfy isIdentStart
  let rest ← manyChars (satisfy isIdentCont)
  pure (first.toString ++ rest)

/-- Result of parsing a number: either untyped integer or typed bits -/
inductive NumLit where
  | untyped (value : Int)
  | typed (sign : Sign) (width : Nat) (value : Int)

/-- Parse a signed integer, possibly with a type suffix (e.g., 42i32, 0u8) -/
def signedNumber : P NumLit := lexeme do
  let neg ← optional (pchar '-')
  let n ← digits
  let value : Int := if neg.isSome then -(Int.ofNat n) else Int.ofNat n
  -- Check for optional type suffix: i<N> or u<N>
  let suffix ← optional (attempt do
    let signChar ← satisfy (fun c => c == 'i' || c == 'u')
    let width ← digits
    pure (signChar, width))
  match suffix with
  | some (signChar, width) =>
    let sign : Sign := if signChar == 'u' then .unsigned else .signed
    pure (.typed sign width value)
  | none =>
    pure (.untyped value)

/-! ## CN Type Parsers -/

/-- Sign specifiers for C types -/
inductive CSignSpec where
  | signed
  | unsigned
  deriving Repr, BEq

/-- Size specifiers for C types -/
inductive CSizeSpec where
  | short
  | long
  | longLong
  deriving Repr, BEq

/-- Parse an optional sign specifier (signed/unsigned) -/
def signSpec : P (Option CSignSpec) := optional (attempt do
  let name ← ident
  match name with
  | "signed" => pure .signed
  | "unsigned" => pure .unsigned
  | _ => fail "not a sign specifier")

/-- Parse an optional size specifier (short/long/long long) -/
def sizeSpec : P (Option CSizeSpec) := optional (attempt do
  let name ← ident
  match name with
  | "short" => pure .short
  | "long" =>
    -- Check for "long long"
    let next ← optional (attempt (keyword "long"))
    if next.isSome then pure .longLong else pure .long
  | _ => fail "not a size specifier")

/-- Parse pointer stars and return the count -/
def pointerStars : P Nat := do
  let stars ← many (lexeme (pchar '*'))
  pure stars.toList.length

/-- Build a Ctype from sign, size, base type name, and pointer depth -/
def buildCtype (sign : Option CSignSpec) (size : Option CSizeSpec) (baseName : String) (ptrDepth : Nat) : Ctype :=
  -- First, determine the base integer type
  let intKind : IntBaseKind := match size with
    | some .short => .short
    | some .long => .long
    | some .longLong => .longLong
    | none => .int_

  let intType : IntegerType := match sign with
    | some .unsigned => .unsigned intKind
    | _ => .signed intKind  -- Default to signed

  -- Build the base type
  let baseType : Ctype := match baseName with
    | "void" => .void
    -- Cerberus treats plain 'char' as signed on all supported target platforms
    -- (x86-64 Linux/macOS). This matches Cerberus's ABI choice via its
    -- impl_funs.ml:ocaml_char_is_signed = true. C standard says char signedness
    -- is implementation-defined (C11 6.2.5p15).
    | "char" =>
      let charSign := sign.getD .signed
      .basic (.integer (if charSign == .unsigned then .unsigned .ichar else .signed .ichar))
    | "int" | "" => .basic (.integer intType)  -- "" means just sign/size without explicit "int"
    | "float" => .basic (.floating (.realFloating .float))
    | "double" =>
      -- "long double" is a thing
      if size == some .long
      then .basic (.floating (.realFloating .longDouble))
      else .basic (.floating (.realFloating .double))
    | _ =>
      -- User-defined type (typedef, struct name without 'struct' keyword, etc.)
      -- CN resolves these against the C context later. At parse time, we accept
      -- any identifier as a potential type name and represent it using struct_
      -- (limitation: our Ctype lacks a distinct typedef variant).
      -- Examples: size_t, uint32_t, my_struct_t
      .struct_ { id := 0, name := some baseName }

  -- Apply pointer indirection
  let rec addPointers (ct : Ctype) (n : Nat) : Ctype :=
    match n with
    | 0 => ct
    | n + 1 => addPointers (.pointer {} ct) n

  addPointers baseType ptrDepth

/-- Parse a C type with full support for sign/size specifiers and pointers.

    Grammar:
    ```
    ctype = [sign_spec] [size_spec] [base_type] ["*"]*
          | "struct" IDENT ["*"]*
          | "union" IDENT ["*"]*
          | IDENT ["*"]*
    ```

    Examples:
    - `int` → signed int
    - `signed int` → signed int
    - `unsigned long` → unsigned long int
    - `long long` → signed long long int
    - `int*` → pointer to signed int
    - `struct point` → struct point
    - `struct point*` → pointer to struct point
-/
def parseCtype : P Ctype := do
  ws
  -- Try struct/union first
  let structOrUnion ← optional (attempt do
    let kw ← ident
    if kw == "struct" || kw == "union" then
      let tag ← ident
      let ptrDepth ← pointerStars
      let baseCt := Ctype.struct_ { id := 0, name := some tag }
      pure (buildCtype none none "" ptrDepth |> fun _ => -- Ignore result, use struct directly
        let rec addPointers (ct : Ctype) (n : Nat) : Ctype :=
          match n with
          | 0 => ct
          | n + 1 => addPointers (.pointer {} ct) n
        addPointers baseCt ptrDepth)
    else
      fail "not struct/union")

  match structOrUnion with
  | some ct => pure ct
  | none =>
    -- Parse optional sign specifier
    let sign ← signSpec

    -- Parse optional size specifier
    let size ← sizeSpec

    -- Parse optional base type name
    -- If we have sign or size but no base name, it defaults to "int"
    let baseName ← optional (attempt do
      let name ← ident
      -- Make sure it's a type name, not a keyword or variable
      if name ∈ ["int", "char", "void", "float", "double"] then
        pure name
      else if sign.isNone && size.isNone then
        -- No sign/size, so this could be a typedef name
        pure name
      else
        fail "not a base type name")

    -- If we got nothing, fail
    if sign.isNone && size.isNone && baseName.isNone then
      fail "expected type"

    -- Parse pointer stars
    let ptrDepth ← pointerStars

    -- Build the type
    let finalBaseName := baseName.getD (if sign.isSome || size.isSome then "int" else "")
    pure (buildCtype sign size finalBaseName ptrDepth)

/-- Parse a simple C type (for backward compatibility, now delegates to parseCtype) -/
def ctypeStr : P String := lexeme do
  -- This is kept for any code that needs string representation
  let base ← ident
  let stars ← manyChars (satisfy (· == '*'))
  pure (base ++ stars)

/-- Parse a CN base type.
    Corresponds to: base_type_explicit / base_type in CN grammar.
    base_type_explicit covers keyword-prefixed types (void, bool, i32, struct X, etc.)
    base_type also allows bare cn_variable for type synonyms (not yet supported). -/
partial def cnBaseType : P BaseType := do
  let name ← ident
  match name with
  | "void" => pure .unit
  | "bool" => pure .bool
  | "integer" => pure .integer
  | "i8" => pure (.bits .signed 8)
  | "i16" => pure (.bits .signed 16)
  | "i32" => pure (.bits .signed 32)
  | "i64" => pure (.bits .signed 64)
  | "u8" => pure (.bits .unsigned 8)
  | "u16" => pure (.bits .unsigned 16)
  | "u32" => pure (.bits .unsigned 32)
  | "u64" => pure (.bits .unsigned 64)
  | "real" => pure .real
  | "pointer" => pure .loc
  | "alloc_id" => pure .allocId
  -- Corresponds to: STRUCT <cn_variable> in base_type_explicit
  | "struct" => do
    let tag ← ident
    pure (.struct_ { id := 0, name := some tag })
  -- Corresponds to: CN_DATATYPE <cn_variable> in base_type_explicit
  | "datatype" => do
    let tag ← ident
    pure (.datatype { id := 0, name := some tag })
  -- Corresponds to: CN_MAP LT base_type COMMA base_type GT
  | "map" => do
    symbol "<"; let k ← cnBaseType; symbol ","; let v ← cnBaseType; symbol ">"
    pure (.map k v)
  -- Corresponds to: CN_LIST LT base_type GT
  | "list" => do
    symbol "<"; let t ← cnBaseType; symbol ">"
    pure (.list t)
  -- Corresponds to: CN_SET LT base_type GT
  | "set" => do
    symbol "<"; let t ← cnBaseType; symbol ">"
    pure (.set t)
  | other => fail s!"unrecognized CN base type: {other}"

/-! ## Helper Functions -/

/-- Make an identifier from a string -/
def mkIdent (s : String) : Identifier :=
  { loc := default, name := s }

/-- Make a symbol from a string -/
def mkSym (s : String) : Sym :=
  { id := 0, name := some s }

/-- Make an annotated term with default location and type -/
def mkTerm (t : Term) : AnnotTerm :=
  .mk t .unit default

/-- Make a simple C integer type -/
def mkIntCtype : Ctype :=
  .basic (.integer (.signed .int_))

/-! ## Expression Parsers (Mutual Recursion) -/

mutual

/-- Parse an expression list -/
partial def exprList : P (List AnnotTerm) := do
  let first ← optional expr
  match first with
  | none => pure []
  | some e =>
    let rest ← many do
      symbol ","
      expr
    pure (e :: rest.toList)

/-- Parse a cast expression: (cnBaseType) expr
    Reference: c_parser.mly line 1948: LPAREN base_type_explicit RPAREN expr -/
partial def castExpr : P AnnotTerm := do
  symbol "("
  let bt ← cnBaseType
  symbol ")"
  let e ← unaryExpr
  pure (mkTerm (.cast bt e))

/-- Parse a parenthesized expression -/
partial def parenExpr : P AnnotTerm := do
  symbol "("
  let e ← expr
  symbol ")"
  pure e

/-- Parse an atomic expression (no binary operators) -/
partial def atomExpr : P AnnotTerm := do
  ws
  let c ← peek?
  match c with
  | some '(' =>
    -- Try cast expression: (cnBaseType) expr
    -- Falls back to parenthesized expression if not a cast
    match ← optional (attempt castExpr) with
    | some e => pure e
    | none => parenExpr
  | some c =>
    if c.isDigit || c == '-' then do
      let n ← signedNumber
      match n with
      | .untyped v => pure (mkTerm (.const (.z v)))
      | .typed sign width v =>
        -- Typed literals get the correct base type immediately
        pure (AnnotTerm.mk (.const (.bits sign width v)) (.bits sign width) default)
    else if isIdentStart c then do
      let name ← ident
      match name with
      | "return" => pure (mkTerm (.sym (mkSym "return")))
      | "null" | "NULL" => pure (mkTerm (.const .null))
      | "true" => pure (mkTerm (.const (.bool true)))
      | "false" => pure (mkTerm (.const (.bool false)))
      | _ =>
        let paren ← peek?
        if paren == some '(' then do
          symbol "("
          let args ← exprList
          symbol ")"
          pure (mkTerm (.apply (mkSym name) args))
        else
          pure (mkTerm (.sym (mkSym name)))
    else
      fail s!"unexpected character: {c}"
  | none => fail "unexpected end of input"

/-- Parse member access (postfix . and ->) -/
partial def postfixExpr : P AnnotTerm := do
  let base ← atomExpr
  postfixRest base
where
  postfixRest (e : AnnotTerm) : P AnnotTerm := do
    let c ← peek?
    match c with
    | some '.' => do
      let _ ← any
      ws
      let member ← ident
      let newExpr := mkTerm (.structMember e (mkIdent member))
      postfixRest newExpr
    | some '-' =>
      -- Try -> (member access); if not followed by >, leave '-' for binop parser
      match ← optional (attempt (pstring "->")) with
      | some _ => do
        ws
        let member ← ident
        let newExpr := mkTerm (.structMember e (mkIdent member))
        postfixRest newExpr
      | none => pure e
    | some '[' =>
      -- Subscript: e[idx] → mapGet(e, idx)
      -- CN ref: c_parser.mly CNExpr_binop (CN_map_get) for map subscript
      let _ ← any
      ws
      let idx ← expr
      symbol "]"
      let newExpr := mkTerm (.mapGet e idx)
      postfixRest newExpr
    | _ => pure e

/-- Parse a unary prefix expression: -expr, !expr, ~expr
    Reference: c_parser.mly lines 1937-1946 -/
partial def unaryExpr : P AnnotTerm := do
  ws
  let c ← peek?
  match c with
  | some '!' =>
    -- Must not be != (which is a binop)
    match ← optional (attempt (pstring "!" *> notFollowedBy (pchar '='))) with
    | some _ =>
      ws
      let e ← unaryExpr
      pure (mkTerm (.unop .not e))
    | none => postfixExpr
  | some '~' =>
    let _ ← any
    ws
    let e ← unaryExpr
    pure (mkTerm (.unop .bwCompl e))
  | some '-' =>
    -- Unary minus: try to parse as negative number first (for literals),
    -- but this also handles -expr for variables
    -- We use attempt to distinguish unary - from binary -
    -- If followed by a digit, signedNumber handles it. Otherwise treat as unary op.
    match ← optional (attempt (do
      let _ ← pchar '-'
      -- If next char is a digit, let atomExpr handle the negative literal
      let next ← peek?
      match next with
      | some c => if c.isDigit then fail "let atomExpr handle negative literal" else pure ()
      | none => fail "unexpected end")) with
    | some _ =>
      ws
      let e ← unaryExpr
      pure (mkTerm (.unop .negate e))
    | none => postfixExpr
  | _ => postfixExpr

/-- Parse a binary operator. Returns (opString, binop, swapOperands).
    For `>` and `>=`, we return the corresponding `<`/`<=` op with swap=true,
    since CN normalizes a > b to b < a.
    Supports: arithmetic (+, -, *, /, %), comparison (==, !=, <, <=, >, >=),
    logical (&&, ||, implies), bitwise (&, |, ^).
    NOTE: << and >> are not part of CN's cn_binop type (cn.lem:43-61).
    Reference: c_parser.mly lines 1900-1935 -/
partial def binop : P (String × BinOp × Bool) :=
  attempt keywordBinop <|> symbolBinop
where
  /-- Parse keyword binary operators (e.g., `implies`) -/
  keywordBinop : P (String × BinOp × Bool) := lexeme do
    keyword "implies"
    pure ("implies", .implies, false)
  /-- Parse symbolic binary operators -/
  symbolBinop : P (String × BinOp × Bool) := lexeme do
    let c ← any
    match c with
    | '+' => pure ("+", .add, false)
    | '-' => pure ("-", .sub, false)
    | '*' => pure ("*", .mul, false)
    | '/' => pure ("/", .div, false)
    | '%' => pure ("%", .rem, false)  -- CN's % maps to Rem (C remainder), not Mod
    | '^' => pure ("^", .bwXor, false)
    | '=' =>
      let c2 ← peek?
      if c2 == some '=' then do
        let _ ← any
        pure ("==", .eq, false)
      else
        fail "expected '==' operator"
    | '!' =>
      let c2 ← any
      if c2 == '=' then pure ("!=", .eq, false)  -- Will be wrapped in NOT
      else fail "expected '!=' operator"
    -- NOTE: << and >> are not part of CN's cn_binop type (cn.lem:43-61).
    -- They exist in Core IR but not CN specs.
    | '<' =>
      let c2 ← peek?
      if c2 == some '=' then do
        let _ ← any
        pure ("<=", .le, false)
      else
        pure ("<", .lt, false)
    | '>' =>
      let c2 ← peek?
      if c2 == some '=' then do
        let _ ← any
        -- >= becomes <= with swapped operands: a >= b  ↔  b <= a
        pure (">=", .le, true)
      else
        -- > becomes < with swapped operands: a > b  ↔  b < a
        pure (">", .lt, true)
    | '&' =>
      let c2 ← peek?
      if c2 == some '&' then do
        let _ ← any
        pure ("&&", .and_, false)
      else
        pure ("&", .bwAnd, false)
    | '|' =>
      let c2 ← peek?
      if c2 == some '|' then do
        let _ ← any
        pure ("||", .or_, false)
      else
        pure ("|", .bwOr, false)
    | _ => fail s!"unexpected operator character: {c}"

/-- Binary operator precedence (higher = tighter binding).
    Matches CN spec expression grammar (c_parser.mly lines 1947-2021).
    NOTE: This differs from standard C precedence! CN groups bitwise ops with
    arithmetic: `& ^` at mul level, `|` at add level.
    This means `return == x | y` parses as `return == (x | y)` in CN.
    Reference: c_parser.mly mul_expr, add_expr, rel_expr, bool_*_expr -/
partial def binopPrec : String → Option Nat
  | "*" | "/" | "%" | "&" | "^" => some 6              -- mul_expr
  | "+" | "-" | "|" => some 5                          -- add_expr
  | "<" | "<=" | ">" | ">=" | "==" | "!=" => some 4   -- rel_expr
  | "&&" => some 3                                      -- bool_and_expr
  | "implies" => some 2                                 -- bool_implies_expr
  | "||" => some 1                                      -- bool_or_expr
  | _ => none

/-- Parse a binary expression using precedence climbing -/
partial def expr : P AnnotTerm := do
  let lhs ← unaryExpr
  binExprRest lhs 0
where
  binExprRest (lhs : AnnotTerm) (minPrec : Nat) : P AnnotTerm := do
    -- Parse a binop only if its precedence is high enough.
    -- The precedence check is inside `attempt` so that a too-low-precedence
    -- operator doesn't consume input (the caller needs to see it).
    let opOpt ← optional (attempt do
      let (opStr, op, swap) ← binop
      let some prec := binopPrec opStr
        | fail s!"unknown binary operator: {opStr}"
      if prec < minPrec then fail "precedence too low"
      pure (opStr, op, swap, prec))
    match opOpt with
    | none =>
      -- Check for ternary: expr ? expr : expr (lowest precedence)
      -- Only check at outermost level to avoid precedence bugs
      if minPrec == 0 then
        let ternary ← optional (attempt (symbol "?"))
        match ternary with
        | some _ =>
          let thenE ← expr
          symbol ":"
          let elseE ← expr
          pure (mkTerm (.ite lhs thenE elseE))
        | none => pure lhs
      else
        pure lhs
    | some (opStr, op, swap, _prec) => do
        let some prec := binopPrec opStr
          | fail s!"unknown binary operator: {opStr}"
        let rhs ← unaryExpr
        let rhs ← binExprRest rhs (prec + 1)
        -- If swap is true, flip operands (e.g., a > b becomes b < a)
        let binExpr := if swap then mkTerm (.binop op rhs lhs) else mkTerm (.binop op lhs rhs)
        -- If != operator, wrap in NOT: a != b becomes !(a == b)
        let newLhs := if opStr == "!=" then mkTerm (.unop .not binExpr) else binExpr
        binExprRest newLhs minPrec

end

/-! ## Predicate Parsers -/

/-- Parse a predicate name (Owned, Block, or user-defined).
    CN allows both `Owned<type>(p)` (explicit) and `Owned(p)` (type inferred from p).
    Reference: c_parser.mly cn_pred production -/
def predName : P ResourceName := do
  let name ← ident
  match name with
  | "Owned" | "RW" =>
    -- Parse optional type parameter: Owned<type> or RW<type> or Owned or RW
    -- RW is the production name in CN; Owned is deprecated
    -- When no type given, it will be inferred during resolution from the pointer's C type
    let ctOpt ← optional (attempt do
      symbol "<"
      let ct ← parseCtype
      symbol ">"
      pure ct)
    pure (.owned ctOpt .init)
  | "Block" | "W" =>
    -- Parse optional type parameter: Block<type> or W<type> or Block or W
    -- W is the production name in CN; Block is deprecated
    let ctOpt ← optional (attempt do
      symbol "<"
      let ct ← parseCtype
      symbol ">"
      pure ct)
    -- Block/W represents uninitialized memory
    pure (.owned ctOpt .uninit)
  | _ =>
    if name.front.isUpper then
      pure (.pname (mkSym name))
    else
      fail s!"predicate name must start with uppercase: {name}"

/-- Parse a resource (predicate application) -/
def resource : P Request := do
  let pred ← predName
  symbol "("
  let args ← exprList
  symbol ")"
  match args with
  | [] => fail "resource requires at least one argument (pointer)"
  | ptr :: iargs =>
    pure (.p { name := pred, pointer := ptr, iargs := iargs })

/-- Parse an `each` resource (quantified predicate / QPredicate).
    Format: `each (base_type var; guard) {Pred<type>(pointer_args)}`

    CN ref: c_parser.mly:2377-2384

    Example: `each (u64 i; 0u64 <= i && i < 3u64) {Owned<int>(array_shift(arr, i))}` -/
partial def eachResource : P Request := do
  keyword "each"
  symbol "("
  let qBt ← cnBaseType
  let qName ← ident
  symbol ";"
  let guard ← expr
  symbol ")"
  symbol "{"
  let pred ← predName
  symbol "("
  let args ← exprList
  symbol ")"
  symbol "}"
  match args with
  | [] => fail "each: inner resource requires at least one argument (pointer)"
  | ptr :: iargs =>
    let qSym := mkSym qName
    -- Extract C type from the predicate name for the step type
    let step : Ctype ← match pred with
      | .owned (some ct) _ => pure ct
      | _ => fail "each: cannot infer step type when predicate type is not explicit"
    pure (.q {
      name := pred
      pointer := ptr
      q := (qSym, qBt)
      qLoc := Core.Loc.t.unknown
      step := step
      permission := guard
      iargs := iargs
    })

/-! ## Clause Parsers -/

/-- Parse a take clause: `take v = Resource(...)` or `take v = each (...) {Resource(...)}`
    CN ref: c_parser.mly condition production -/
partial def takeClause : P Clause := do
  keyword "take"
  let name ← ident
  symbol "="
  let sym := mkSym name
  -- Try `each` resource first, then fall back to regular resource
  let req ← attempt eachResource <|> resource
  symbol ";"
  -- Output uses placeholder type (.unit) — resolution will assign the correct type
  -- via requestOutputBaseType which handles both P and Q requests
  let output : Output := { value := mkTerm (.sym sym) }
  pure (.resource sym { request := req, output := output })

/-- Parse a let clause: let v = expr
    Binds variable name for use in subsequent clauses.
    Reference: c_parser.mly CN_LET condition -/
def letClause : P Clause := do
  keyword "let"
  let name ← ident
  symbol "="
  let e ← expr
  symbol ";"
  pure (.letBinding (mkSym name) e)

/-- Keywords that should not be parsed as identifiers in expressions -/
def cnKeywords : List String := ["requires", "ensures", "take", "let", "trusted", "implies",
                                  "accesses", "cn_ghost", "each"]

/-- Fail if next token is a keyword (using negative lookahead) -/
def notKeyword : P Unit := do
  -- Check each keyword - if any matches, fail
  notFollowedBy (keyword "requires")
  notFollowedBy (keyword "ensures")
  notFollowedBy (keyword "take")
  notFollowedBy (keyword "let")
  notFollowedBy (keyword "trusted")
  notFollowedBy (keyword "accesses")
  notFollowedBy (keyword "cn_ghost")
  notFollowedBy (keyword "each")

/-- Parse a constraint clause: expr; -/
def constraintClause : P Clause := do
  -- Don't parse keywords as expressions
  notKeyword
  let e ← expr
  symbol ";"
  pure (.constraint e)

/-- Parse a single condition (take, let, or constraint) -/
def condition : P Clause :=
  attempt takeClause <|> attempt letClause <|> constraintClause

/-! ## Function Spec Parsers -/

/-- Parse an `accesses` clause: `accesses name1, name2, ...;`
    Declares global variables that the function accesses.
    CN ref: c_parser.mly accesses production -/
def accessesClause : P (List String) := do
  keyword "accesses"
  let first ← ident
  let rest ← many (attempt (symbol "," *> ident))
  symbol ";"
  pure (first :: rest.toList)

/-- Parse a single ghost parameter declaration: `type name`
    CN ref: c_parser.mly cn_ghost production -/
partial def ghostParamDecl : P (Sym × BaseType) := do
  let bt ← cnBaseType
  let name ← ident
  pure (mkSym name, bt)

/-- Parse a `cn_ghost` clause: `cn_ghost type1 name1, type2 name2;`
    Declares ghost (logical-only) parameters for the function.
    CN ref: c_parser.mly cn_ghost production, core_to_mucore.ml ghost handling -/
partial def ghostParamsClause : P (List (Sym × BaseType)) := do
  keyword "cn_ghost"
  let first ← ghostParamDecl
  let rest ← many (attempt (symbol "," *> ghostParamDecl))
  symbol ";"
  pure (first :: rest.toList)

/-- Parse a requires clause, optionally preceded by cn_ghost declarations.
    The cn_ghost clause appears after the `requires` keyword in CN syntax:
    ```
    requires cn_ghost i32 a, i32 b;
             a + b == total;
    ```
    CN ref: c_parser.mly requires + cn_ghost interaction -/
partial def requiresClause : P (List Clause × List (Sym × BaseType)) := do
  keyword "requires"
  -- Ghost params can appear right after `requires` keyword
  let ghostParamsOpt ← optional (attempt ghostParamsClause)
  let ghostParams := ghostParamsOpt.getD []
  let clauses ← many1 condition
  pure (clauses.toList, ghostParams)

/-- Parse an ensures clause -/
def ensuresClause : P (List Clause) := do
  keyword "ensures"
  let clauses ← many1 condition
  pure clauses.toList

/-- Parse a complete function specification.
    Corresponds to: fundef_spec parsing in CN, followed by desugaring.

    Creates a return symbol that is used when `return` appears in ensures.
    This matches CN's approach in core_to_mucore.ml:1164 where ret_s is
    created before desugaring ensures.

    Audited: 2026-02-19 against cn/lib/core_to_mucore.ml -/
partial def functionSpec : P FunctionSpec := do
  ws
  let trusted ← optional (keyword "trusted" *> symbol ";")
  -- Parse accesses clauses (can appear before requires)
  let accBlocks ← many (attempt accessesClause)
  let reqBlocks ← many (attempt requiresClause)
  let ensBlocks ← many ensuresClause
  ws
  -- Extract ghost params and clauses from requires blocks
  let allClauses := reqBlocks.toList.map (·.1) |>.flatten
  let allGhostParams := reqBlocks.toList.map (·.2) |>.flatten
  -- Create the return symbol. This is the symbol that `return` references
  -- in the postcondition resolve to. Using ID 0 matches mkSym "return".
  -- Corresponds to: register_new_cn_local (Id.make here "return") in CN
  let returnSym : Sym := { id := 0, name := some "return" }
  pure {
    returnSym := returnSym
    requires := { clauses := allClauses }
    ensures := { clauses := ensBlocks.toList.flatten }
    trusted := trusted.isSome
    accesses := accBlocks.toList.flatten
    ghostParams := allGhostParams
  }

/-! ## Main Entry Points -/

/-- Parse a CN magic string into a FunctionSpec -/
def parseFunctionSpec (input : String) : Except String FunctionSpec :=
  runParser functionSpec input

/-- Parse a CN magic string, returning Option for graceful failure -/
def parseFunctionSpecOpt (input : String) : Option FunctionSpec :=
  match parseFunctionSpec input with
  | .ok spec => some spec
  | .error _ => none

/-! ## Loop Invariant Parsing

Parses loop invariant annotations of the form `inv expr1; expr2; expr3;`.
This is called when processing loop_attributes from CN annotations.

CN ref: c_parser.mly cn_inv production, core_to_mucore.ml loop handling
-/

/-- Parse a loop invariant: `inv expr1; expr2; ...`
    Returns a list of constraint expressions (one per semicolon-separated clause).
    The `inv` keyword has already been consumed by the caller in some contexts;
    this parser expects the full `inv expr; expr; ...` format.

    CN ref: c_parser.mly cn_inv, core_to_mucore.ml loop invariant handling -/
partial def parseInvariant (input : String) : Except String (List AnnotTerm) :=
  runParser (do
    ws
    keyword "inv"
    let mut exprs : List AnnotTerm := []
    -- Parse constraint expressions separated by semicolons
    while (← peek?).isSome do
      -- Don't parse keywords as expressions
      notKeyword
      let e ← expr
      symbol ";"
      exprs := exprs ++ [e]
      ws
    pure exprs) input

/-! ## Ghost Statement Parsing

Parses CN ghost statement text from cerb::magic attributes.
Format: "cn_have(expr)" or "cn_have(expr);" or "have(expr)" etc.

CN ref: cn/lib/parse.ml:78-79 (cn_statements → C_parser.cn_statements)
-/

/-- A parsed ghost statement -/
structure ParsedGhostStatement where
  kind : String
  constraint : Option AnnotTerm
  /-- For focus/instantiate: the resource predicate name -/
  resourcePred : Option ResourceName := none
  /-- For focus/instantiate: the index expression -/
  indexExpr : Option AnnotTerm := none

/-- Parse a focus/instantiate ghost statement: `focus Pred<type>, indexExpr;`
    or `instantiate Pred<type>, indexExpr;`
    CN ref: check.ml:2204-2246 (instantiate and extract/focus handling) -/
partial def focusStatement : P ParsedGhostStatement := do
  ws
  let kind ← ident
  if kind != "focus" && kind != "instantiate" && kind != "extract" then
    fail "not a focus/instantiate statement"
  let pred ← predName
  symbol ","
  let indexE ← expr
  let _ ← optional (symbol ";")
  pure { kind := kind, constraint := none, resourcePred := some pred, indexExpr := some indexE }

/-- Parse a single ghost statement: kind(expr) or kind(expr); or focus Pred, index; -/
partial def ghostStatement : P ParsedGhostStatement := do
  ws
  -- Try focus/instantiate format first (keyword Pred<type>, index;)
  match ← optional (attempt focusStatement) with
  | some stmt => pure stmt
  | none =>
    let kind ← ident
    -- Some statements have an argument expression, some don't
    let constraint ← optional (attempt do
      symbol "("
      let e ← expr
      symbol ")"
      pure e)
    -- Skip optional trailing semicolons
    let _ ← optional (symbol ";")
    pure { kind := kind, constraint := constraint }

/-- Parse one or more ghost statements from a magic attribute string.
    CN ref: cn/lib/parse.ml:78-79 -/
def parseGhostStatements (input : String) : Except String (List ParsedGhostStatement) :=
  runParser (do
    let mut stmts := []
    ws
    -- Parse statements until we hit EOF (peek? returns none)
    while (← peek?).isSome do
      let s ← ghostStatement
      stmts := stmts ++ [s]
      ws
    pure stmts) input

/-- Parse call-site ghost arguments from a magic attribute string.
    Ghost args are comma-separated CN expressions: `3i32, 7i32`
    CN ref: c_parser.mly ghost argument annotations at call sites -/
def parseGhostArgs (input : String) : Except String (List AnnotTerm) :=
  runParser (do
    ws
    let first ← expr
    let mut args := [first]
    while (← optional (symbol ",")).isSome do
      let arg ← expr
      args := args ++ [arg]
    ws
    pure args) input

end CerbLean.CN.Parser
