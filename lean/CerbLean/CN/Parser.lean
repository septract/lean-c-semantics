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
  pred           = "Owned" ["<" ctype ">"]
                 | "Block" ["<" ctype ">"]
                 | UNAME                     -- user-defined predicate

  expr           = term (binop term)*
  term           = IDENT | NUMBER | "(" expr ")" | "return" | "null" | "true" | "false"
                 | term "." IDENT            -- member access
                 | IDENT "(" expr_list ")"   -- function call
  binop          = "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||" | "+" | "-" | "*" | "/"

  ctype          = IDENT ["*"]*              -- simplified C type
  IDENT          = [a-zA-Z_][a-zA-Z0-9_]*
  UNAME          = [A-Z][a-zA-Z0-9_]*        -- starts with uppercase
  NUMBER         = [0-9]+
  ```

  Reference: cerberus/parsers/c/c_parser.mly lines 2300-2500
  Audited: 2025-01-17
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

/-- Parse a signed integer -/
def signedNumber : P Int := lexeme do
  let neg ← optional (pchar '-')
  let n ← digits
  pure (if neg.isSome then -(Int.ofNat n) else Int.ofNat n)

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

/-- Parse a CN base type (for CN-specific type names like i32, u64, etc.) -/
def cnBaseType : P BaseType := do
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
  | _ => pure (.struct_ { id := 0, name := some name })

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
  | some '(' => parenExpr
  | some c =>
    if c.isDigit || c == '-' then do
      let n ← signedNumber
      pure (mkTerm (.const (.z n)))
    else if isIdentStart c then do
      let name ← ident
      match name with
      | "return" => pure (mkTerm (.sym (mkSym "return")))
      | "null" => pure (mkTerm (.const .null))
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
    | some '-' => do
      let _ ← any
      let c2 ← peek?
      if c2 == some '>' then do
        let _ ← any
        ws
        let member ← ident
        let newExpr := mkTerm (.structMember e (mkIdent member))
        postfixRest newExpr
      else
        fail "expected '>' after '-'"
    | _ => pure e

/-- Parse a binary operator. Returns (opString, binop, swapOperands).
    For `>` and `>=`, we return the corresponding `<`/`<=` op with swap=true,
    since CN normalizes a > b to b < a. -/
partial def binop : P (String × BinOp × Bool) := lexeme do
  let c ← any
  match c with
  | '+' => pure ("+", .add, false)
  | '-' => pure ("-", .sub, false)
  | '*' => pure ("*", .mul, false)
  | '/' => pure ("/", .div, false)
  | '%' => pure ("%", .mod_, false)
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
    let c2 ← any
    if c2 == '&' then pure ("&&", .and_, false)
    else fail "expected '&&' operator"
  | '|' =>
    let c2 ← any
    if c2 == '|' then pure ("||", .or_, false)
    else fail "expected '||' operator"
  | _ => fail s!"unexpected operator character: {c}"

/-- Binary operator precedence (higher = tighter binding) -/
partial def binopPrec : String → Nat
  | "*" | "/" | "%" => 6
  | "+" | "-" => 5
  | "<" | "<=" | ">" | ">=" => 4
  | "==" | "!=" => 3
  | "&&" => 2
  | "||" => 1
  | _ => 0

/-- Parse a binary expression using precedence climbing -/
partial def expr : P AnnotTerm := do
  let lhs ← postfixExpr
  exprRest lhs 0
where
  exprRest (lhs : AnnotTerm) (minPrec : Nat) : P AnnotTerm := do
    let opOpt ← optional (attempt binop)
    match opOpt with
    | none => pure lhs
    | some (opStr, op, swap) =>
      let prec := binopPrec opStr
      if prec < minPrec then
        pure lhs
      else do
        let rhs ← postfixExpr
        let rhs ← exprRest rhs (prec + 1)
        -- If swap is true, flip operands (e.g., a > b becomes b < a)
        let binExpr := if swap then mkTerm (.binop op rhs lhs) else mkTerm (.binop op lhs rhs)
        -- If != operator, wrap in NOT: a != b becomes !(a == b)
        let newLhs := if opStr == "!=" then mkTerm (.unop .not binExpr) else binExpr
        exprRest newLhs minPrec

end

/-! ## Predicate Parsers -/

/-- Parse a predicate name (Owned, Block, or user-defined) -/
def predName : P ResourceName := do
  let name ← ident
  match name with
  | "Owned" =>
    -- Parse required type parameter: Owned<type>
    -- CN requires explicit type; no defaulting
    symbol "<"
    let ct ← parseCtype
    symbol ">"
    pure (.owned ct .init)
  | "Block" =>
    -- Parse required type parameter: Block<type>
    -- CN requires explicit type; no defaulting
    symbol "<"
    let ct ← parseCtype
    symbol ">"
    -- Block represents uninitialized memory
    pure (.owned ct .uninit)
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

/-! ## Clause Parsers -/

/-- Parse a take clause: take v = Resource(...) -/
def takeClause : P Clause := do
  keyword "take"
  let name ← ident
  symbol "="
  let res ← resource
  symbol ";"
  let sym := mkSym name
  let output : Output := { value := mkTerm (.sym sym) }
  pure (.resource sym { request := res, output := output })

/-- Parse a let clause: let v = expr -/
def letClause : P Clause := do
  keyword "let"
  let _ ← ident
  symbol "="
  let e ← expr
  symbol ";"
  pure (.constraint e)

/-- Keywords that should not be parsed as identifiers in expressions -/
def cnKeywords : List String := ["requires", "ensures", "take", "let", "trusted"]

/-- Fail if next token is a keyword (using negative lookahead) -/
def notKeyword : P Unit := do
  -- Check each keyword - if any matches, fail
  notFollowedBy (keyword "requires")
  notFollowedBy (keyword "ensures")
  notFollowedBy (keyword "take")
  notFollowedBy (keyword "let")
  notFollowedBy (keyword "trusted")

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

/-- Parse a requires clause -/
def requiresClause : P (List Clause) := do
  keyword "requires"
  let clauses ← many1 condition
  pure clauses.toList

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

    Audited: 2026-01-27 against cn/lib/core_to_mucore.ml -/
def functionSpec : P FunctionSpec := do
  ws
  let trusted ← optional (keyword "trusted" *> symbol ";")
  let reqs ← optional requiresClause
  let enss ← optional ensuresClause
  ws
  -- Create the return symbol. This is the symbol that `return` references
  -- in the postcondition resolve to. Using ID 0 matches mkSym "return".
  -- Corresponds to: register_new_cn_local (Id.make here "return") in CN
  let returnSym : Sym := { id := 0, name := some "return" }
  pure {
    returnSym := returnSym
    requires := { clauses := reqs.getD [] }
    ensures := { clauses := enss.getD [] }
    trusted := trusted.isSome
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

end CerbLean.CN.Parser
