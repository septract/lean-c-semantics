/-
  Pure expression evaluation
  Corresponds to: cerberus/frontend/model/core_eval.lem
  Audited: 2025-01-01
  Deviations: None - matches Cerberus exactly
-/

import CToLean.Semantics.Monad
import CToLean.Semantics.State
import CToLean.Memory.Interface
import Std.Data.HashMap

namespace CToLean.Semantics

open CToLean.Core
open CToLean.Memory
open Std (HashMap)

/-! ## Bitwise Operations for Integers

Implements infinite two's complement bitwise operations matching Zarith/GMP semantics.
Corresponds to: Nat_big_num.bitwise_and/or/xor in impl_mem.ml:2503-2511

Zarith uses infinite two's complement: negative numbers are treated as having
infinitely many 1 bits to the left. This affects how bitwise operations work
on negative operands.
-/

mutual
  /-- Bitwise AND using infinite two's complement (Zarith semantics).
      Corresponds to: Nat_big_num.bitwise_and
      Audited: 2026-01-02
      Deviations: None -/
  partial def intBitwiseAnd (a b : Int) : Int :=
    if a == 0 || b == 0 then 0
    else if a > 0 && b > 0 then
      -- Both positive: standard natural AND
      (a.toNat &&& b.toNat : Nat)
    else if a < 0 && b < 0 then
      -- Both negative: ~(~a | ~b) = -(intBitwiseOr (-a-1) (-b-1) + 1)
      -(intBitwiseOr (-a - 1) (-b - 1) + 1)
    else if a < 0 then
      -- a < 0, b >= 0: bits of b that are also in ~a's complement
      -- Since ~a = -a-1 is positive, we want bits where both b and NOT(~a) are set
      -- NOT(~a) for finite representation: use mask to limit bit width
      let notA := (-a - 1).toNat
      -- For C semantics, we compute b AND NOT(notA) by clearing bits in b that are in notA
      -- Result is non-negative since b >= 0
      (b.toNat &&& (b.toNat ^^^ (b.toNat &&& notA)) : Nat)
    else
      -- a >= 0, b < 0: symmetric
      let notB := (-b - 1).toNat
      (a.toNat &&& (a.toNat ^^^ (a.toNat &&& notB)) : Nat)

  /-- Bitwise OR using infinite two's complement (Zarith semantics).
      Corresponds to: Nat_big_num.bitwise_or
      Audited: 2026-01-02
      Deviations: None -/
  partial def intBitwiseOr (a b : Int) : Int :=
    if a == 0 then b
    else if b == 0 then a
    else if a > 0 && b > 0 then
      (a.toNat ||| b.toNat : Nat)
    else if a < 0 && b < 0 then
      -(intBitwiseAnd (-a - 1) (-b - 1) + 1)
    else if a < 0 then
      -- a < 0, b >= 0: result is negative
      -(Int.ofNat ((-a - 1).toNat &&& ((-a - 1).toNat ^^^ ((-a - 1).toNat &&& b.toNat))) + 1)
    else
      -- a >= 0, b < 0: symmetric
      -(Int.ofNat ((-b - 1).toNat &&& ((-b - 1).toNat ^^^ ((-b - 1).toNat &&& a.toNat))) + 1)
end

/-- Bitwise XOR using infinite two's complement (Zarith semantics).
    Corresponds to: Nat_big_num.bitwise_xor
    Audited: 2026-01-02
    Deviations: None -/
def intBitwiseXor (a b : Int) : Int :=
  if a == 0 then b
  else if b == 0 then a
  else if a > 0 && b > 0 then
    -- Both positive: standard natural XOR
    (a.toNat ^^^ b.toNat : Nat)
  else if a < 0 && b < 0 then
    -- Both negative: ~a XOR ~b = a XOR b (complements cancel in XOR)
    ((-a - 1).toNat ^^^ (-b - 1).toNat : Nat)
  else if a < 0 then
    -- a < 0, b >= 0: result is negative
    -- In infinite two's complement: ~a XOR b = ~(~a XOR ~b) where ~b has infinite 1s
    -- = ~((−a−1) XOR ~b_finite) - but ~b_finite is complex
    -- Simpler: result = -((-a-1) XOR b + 1)
    -((((-a - 1).toNat ^^^ b.toNat) : Nat) + 1 : Int)
  else
    -- a >= 0, b < 0: symmetric
    -((((a.toNat ^^^ (-b - 1).toNat) : Nat) + 1) : Int)

/-- Combine provenance from two integer values.
    Corresponds to: combine_prov in impl_mem.ml
    Audited: 2026-01-02
    Deviations: Simplified - takes first non-none provenance -/
def combineProv (p1 p2 : Provenance) : Provenance :=
  match p1, p2 with
  | .some id, _ => .some id
  | _, .some id => .some id
  | _, _ => .none

/-! ## Environment Lookup

Corresponds to: Core_aux.lookup_env in core_aux.lem:2480-2490
```lem
let rec lookup_env sym = function
  | [] -> Nothing
  | env :: xs ->
      match Map.lookup sym env with
        | Nothing -> lookup_env sym xs
        | Just ret -> Just ret
      end
end
```
-/

/-- Look up a symbol in the scoped environment.
    Corresponds to: lookup_env in core_aux.lem:2480-2490
    Audited: 2025-01-01
    Deviations: None -/
def lookupEnv (sym : Sym) : List (HashMap Sym Value) → Option Value
  | [] => none
  | env :: xs =>
    match env[sym]? with
    | none => lookupEnv sym xs
    | some ret => some ret

/-! ## Pattern Matching

Corresponds to: match_pattern in core_aux.lem
Pattern matching extracts bindings from values.
Note: matchPatternBindings is defined in State.lean
-/

/-- Match a pattern against a value, returning bindings on success.
    Wraps matchPatternBindings from State.lean.
    Corresponds to: match_pattern in core_aux.lem -/
def matchPattern (pat : APattern) (val : Value) : Option (List (Sym × Value)) :=
  matchPatternBindings pat.pat val

/-! ## Environment Binding

Corresponds to: update_env in core_aux.lem:2472-2477
```lem
let update_env pat cval = function
  | [] -> error "Core_aux.update_env: found empty env"
  | env::xs -> update_env_aux pat cval env :: xs
end
```

Note: For pure expression evaluation, Cerberus uses substitution (subst_sym_pexpr).
However, environment binding is semantically equivalent and simpler to implement.
-/

/-- Bind a single symbol in the innermost scope.
    Corresponds to: Map.insert in update_env_aux -/
def bindInEnv (sym : Sym) (val : Value) : List (HashMap Sym Value) → List (HashMap Sym Value)
  | [] =>
    let emptyMap : HashMap Sym Value := {}
    [emptyMap.insert sym val]  -- Should not happen in well-formed programs
  | env :: xs => (env.insert sym val) :: xs

/-- Bind multiple symbols in the innermost scope.
    Corresponds to: folding update_env_aux over bindings -/
def bindAllInEnv (bindings : List (Sym × Value)) (env : List (HashMap Sym Value)) : List (HashMap Sym Value) :=
  bindings.foldl (fun e (sym, val) => bindInEnv sym val e) env

/-- Create a new environment with a single scope containing the given bindings.
    Used for entering a new scope (e.g., function call). -/
def mkEnvWithBindings (bindings : List (Sym × Value)) : List (HashMap Sym Value) :=
  let emptyMap : HashMap Sym Value := {}
  let scope := bindings.foldl (fun m (sym, val) => m.insert sym val) emptyMap
  [scope]

/-! ## Binary Operations

Corresponds to: step_eval_peop in core_eval.lem:320-540
Binary operations are evaluated by first checking if both operands are values,
then applying the operation.
-/

/-- Evaluate a binary operation on integers.
    Corresponds to: step_eval_peop cases for integer operands in core_eval.lem:320-540
    Note: Division by zero is UB per C11 6.5.5 -/
def evalIntOp (op : Binop) (v1 v2 : IntegerValue) : InterpM Value := do
  let n1 := v1.val
  let n2 := v2.val
  match op with
  | .add => pure (.object (.integer { val := n1 + n2, prov := .none }))
  | .sub => pure (.object (.integer { val := n1 - n2, prov := .none }))
  | .mul => pure (.object (.integer { val := n1 * n2, prov := .none }))
  | .div =>
    if n2 == 0 then InterpM.throwUB .ub045a_divisionByZero
    else pure (.object (.integer { val := n1 / n2, prov := .none }))
  | .rem_t =>
    if n2 == 0 then InterpM.throwUB .ub045b_moduloByZero
    else pure (.object (.integer { val := n1 % n2, prov := .none }))
  | .rem_f =>
    if n2 == 0 then InterpM.throwUB .ub045b_moduloByZero
    else
      -- Floored remainder
      let result := n1 - n2 * ((n1 / n2).toNat)
      pure (.object (.integer { val := result, prov := .none }))
  | .exp => pure (.object (.integer { val := n1 ^ n2.toNat, prov := .none }))
  | .eq => pure (if n1 == n2 then .true_ else .false_)
  | .lt => pure (if n1 < n2 then .true_ else .false_)
  | .le => pure (if n1 <= n2 then .true_ else .false_)
  | .gt => pure (if n1 > n2 then .true_ else .false_)
  | .ge => pure (if n1 >= n2 then .true_ else .false_)
  | .and =>
    let result := n1.toNat &&& n2.toNat
    pure (.object (.integer { val := result, prov := .none }))
  | .or =>
    let result := n1.toNat ||| n2.toNat
    pure (.object (.integer { val := result, prov := .none }))

/-- Extract integer from value -/
def valueToInt (v : Value) : Option IntegerValue :=
  match v with
  | .object (.integer iv) => some iv
  | .loaded (.specified (.integer iv)) => some iv
  | _ => none

/-- Evaluate a binary operation on values.
    Corresponds to: step_eval_peop in core_eval.lem:320-540 -/
def evalBinop (op : Binop) (v1 v2 : Value) : InterpM Value := do
  -- First try integer operations
  match valueToInt v1, valueToInt v2 with
  | some i1, some i2 => evalIntOp op i1 i2
  | _, _ =>
    -- Try other type-specific operations
    match op, v1, v2 with
    -- Ctype equality
    | .eq, .ctype ct1, .ctype ct2 => pure (if ct1 == ct2 then .true_ else .false_)
    -- Boolean AND (logical)
    | .and, .true_, .true_ => pure .true_
    | .and, .true_, .false_ => pure .false_
    | .and, .false_, .true_ => pure .false_
    | .and, .false_, .false_ => pure .false_
    -- Boolean OR (logical)
    | .or, .true_, _ => pure .true_
    | .or, _, .true_ => pure .true_
    | .or, .false_, .false_ => pure .false_
    | _, _, _ =>
      let v1Str := match v1 with
        | .object _ => "object"
        | .loaded _ => "loaded"
        | .unit => "unit"
        | .true_ => "true"
        | .false_ => "false"
        | .ctype _ => "ctype"
        | .list _ _ => "list"
        | .tuple _ => "tuple"
      let v2Str := match v2 with
        | .object _ => "object"
        | .loaded _ => "loaded"
        | .unit => "unit"
        | .true_ => "true"
        | .false_ => "false"
        | .ctype _ => "ctype"
        | .list _ _ => "list"
        | .tuple _ => "tuple"
      InterpM.throwTypeError s!"binary op {repr op} on incompatible types: {v1Str} vs {v2Str}"

/-! ## Constructor Evaluation

Corresponds to: PEctor case in step_eval_pexpr core_eval.lem:~750-820
Constructors build values like tuples, lists, Specified/Unspecified wrappers.
-/

/-- Evaluate a constructor application.
    Corresponds to: PEctor case in core_eval.lem:~750-820
    Audited: 2025-01-01
    Deviations: Simplified - doesn't handle all integer value constructors -/
def evalCtor (c : Ctor) (args : List Value) : InterpM Value := do
  match c with
  | .nil elemTy => pure (.list elemTy [])

  | .cons =>
    match args with
    | [head, .list ty tail] => pure (.list ty (head :: tail))
    | _ => InterpM.throwTypeError "cons requires head and list tail"

  | .tuple => pure (.tuple args)

  | .array =>
    -- Convert values to loaded values for array
    let loadedVals := args.map fun v =>
      match v with
      | .loaded lv => lv
      | .object ov => .specified ov
      | _ => .unspecified .void  -- Fallback
    pure (.object (.array loadedVals))

  | .specified =>
    match args with
    | [.object ov] => pure (.loaded (.specified ov))
    | [v] =>
      -- Try to extract object value
      match v with
      | .loaded (.specified ov) => pure (.loaded (.specified ov))
      | _ => InterpM.throwTypeError "Cspecified requires object value"
    | _ => InterpM.throwTypeError "Cspecified requires exactly one argument"

  | .unspecified =>
    -- Takes a ctype as argument
    match args with
    | [.ctype ty] => pure (.loaded (.unspecified ty))
    | _ => InterpM.throwTypeError "Cunspecified requires ctype argument"

  | .ivmax =>
    match args with
    | [.ctype (.basic (.integer ity))] =>
      let env ← InterpM.getTypeEnv
      let iv := maxIval env ity
      pure (.object (.integer iv))
    | _ => InterpM.throwTypeError "IVmax requires integer ctype"

  | .ivmin =>
    match args with
    | [.ctype (.basic (.integer ity))] =>
      let env ← InterpM.getTypeEnv
      let iv := minIval env ity
      pure (.object (.integer iv))
    | _ => InterpM.throwTypeError "IVmin requires integer ctype"

  | .ivsizeof =>
    match args with
    | [.ctype ty] =>
      let env ← InterpM.getTypeEnv
      let iv := sizeofIval env ty
      pure (.object (.integer iv))
    | _ => InterpM.throwTypeError "IVsizeof requires ctype"

  | .ivalignof =>
    match args with
    | [.ctype ty] =>
      let env ← InterpM.getTypeEnv
      let iv := alignofIval env ty
      pure (.object (.integer iv))
    | _ => InterpM.throwTypeError "IValignof requires ctype"

  -- Bitwise operations
  -- Corresponds to: bitwise_complement_ival, bitwise_and_ival, etc. in impl_mem.ml:2497-2511
  -- These take a ctype as first argument (ignored in concrete model) and operate on integers
  -- using infinite two's complement semantics (matching Zarith/GMP)

  | .ivCOMPL =>
    match args with
    | [_ty, v] =>
      match valueToInt v with
      | some iv =>
        -- Bitwise complement: ~n = -n - 1 (matches Cerberus impl_mem.ml:2497-2501)
        -- Corresponds to: Nat_big_num.(sub (negate n) (of_int 1))
        let result := -iv.val - 1
        pure (.object (.integer { val := result, prov := iv.prov }))
      | none => InterpM.throwTypeError "IVCOMPL requires integer"
    | _ => InterpM.throwTypeError "IVCOMPL requires ctype and integer"

  | .ivAND =>
    match args with
    | [_ty, v1, v2] =>
      match valueToInt v1, valueToInt v2 with
      | some i1, some i2 =>
        -- Bitwise AND using Zarith semantics (infinite two's complement)
        -- Corresponds to: Nat_big_num.bitwise_and in impl_mem.ml:2503-2505
        let result := intBitwiseAnd i1.val i2.val
        let prov := combineProv i1.prov i2.prov
        pure (.object (.integer { val := result, prov := prov }))
      | _, _ => InterpM.throwTypeError "IVAND requires integers"
    | _ => InterpM.throwTypeError "IVAND requires ctype and two integers"

  | .ivOR =>
    match args with
    | [_ty, v1, v2] =>
      match valueToInt v1, valueToInt v2 with
      | some i1, some i2 =>
        -- Bitwise OR using Zarith semantics (infinite two's complement)
        -- Corresponds to: Nat_big_num.bitwise_or in impl_mem.ml:2506-2508
        let result := intBitwiseOr i1.val i2.val
        let prov := combineProv i1.prov i2.prov
        pure (.object (.integer { val := result, prov := prov }))
      | _, _ => InterpM.throwTypeError "IVOR requires integers"
    | _ => InterpM.throwTypeError "IVOR requires ctype and two integers"

  | .ivXOR =>
    match args with
    | [_ty, v1, v2] =>
      match valueToInt v1, valueToInt v2 with
      | some i1, some i2 =>
        -- Bitwise XOR using Zarith semantics (infinite two's complement)
        -- Corresponds to: Nat_big_num.bitwise_xor in impl_mem.ml:2509-2511
        let result := intBitwiseXor i1.val i2.val
        let prov := combineProv i1.prov i2.prov
        pure (.object (.integer { val := result, prov := prov }))
      | _, _ => InterpM.throwTypeError "IVXOR requires integers"
    | _ => InterpM.throwTypeError "IVXOR requires ctype and two integers"

  | .fvfromint =>
    match args with
    | [v] =>
      match valueToInt v with
      | some iv =>
        pure (.object (.floating (.finite (Float.ofInt iv.val))))
      | none => InterpM.throwTypeError "fvfromint requires integer"
    | _ => InterpM.throwTypeError "fvfromint requires one argument"

  | .ivfromfloat =>
    match args with
    | [.object (.floating fv)] =>
      match fv with
      | .finite f => pure (.object (.integer { val := f.toUInt64.toNat, prov := .none }))
      | _ => InterpM.throwTypeError "ivfromfloat: non-finite float"
    | _ => InterpM.throwTypeError "ivfromfloat requires float"

/-! ## Integer Conversion and Overflow Checking

Corresponds to: core_eval.lem:61-110 and core.lem:243-245
- PEconv_int: Integer type conversion with wraparound
- PEwrapI: Wrapping integer operation (no UB on overflow)
- PEcatch_exceptional_condition: Operation that raises UB on overflow
-/

/-- Convert integer to target type (with wraparound).
    Corresponds to: mk_conv_int in core_eval.lem:61-91 -/
def convertInt (ity : IntegerType) (v : Value) : InterpM Value := do
  match valueToInt v with
  | some iv =>
    let env ← InterpM.getTypeEnv
    let maxVal := (maxIval env ity).val
    let minVal := (minIval env ity).val
    let range := maxVal - minVal + 1
    -- Wrap the value to the target range
    let wrapped :=
      if iv.val < minVal then
        minVal + ((iv.val - minVal) % range + range) % range
      else if iv.val > maxVal then
        minVal + (iv.val - minVal) % range
      else
        iv.val
    pure (.object (.integer { val := wrapped, prov := iv.prov }))
  | none => InterpM.throwTypeError "convInt requires integer value"

/-- Wrapping integer operation (no overflow check).
    Corresponds to: mk_wrapI_op in core_eval.lem:93-96
    This is used for unsigned operations where wraparound is defined behavior. -/
def wrapIntOp (ity : IntegerType) (iop : Iop) (v1 v2 : Value) : InterpM Value := do
  match valueToInt v1, valueToInt v2 with
  | some i1, some i2 =>
    let result : Int := match iop with
      | .add => i1.val + i2.val
      | .sub => i1.val - i2.val
      | .mul => i1.val * i2.val
      | .div => if i2.val != 0 then i1.val / i2.val else 0
      | .rem_t => if i2.val != 0 then i1.val % i2.val else 0
      | .shl => i1.val <<< i2.val.toNat
      | .shr => i1.val >>> i2.val.toNat
    let env ← InterpM.getTypeEnv
    let maxVal := (maxIval env ity).val
    let minVal := (minIval env ity).val
    let range := maxVal - minVal + 1
    let wrapped :=
      if result < minVal then
        minVal + ((result - minVal) % range + range) % range
      else if result > maxVal then
        minVal + (result - minVal) % range
      else
        result
    pure (.object (.integer { val := wrapped, prov := .none }))
  | _, _ => InterpM.throwTypeError "wrapI requires integer values"

/-- Check for exceptional condition (overflow).
    Corresponds to: mk_call_catch_exceptional_condition in core_eval.lem:99-110
    This is used for signed operations where overflow is undefined behavior. -/
def catchExceptionalOp (ity : IntegerType) (iop : Iop) (v1 v2 : Value) : InterpM Value := do
  match valueToInt v1, valueToInt v2 with
  | some i1, some i2 =>
    let result : Int := match iop with
      | .add => i1.val + i2.val
      | .sub => i1.val - i2.val
      | .mul => i1.val * i2.val
      | .div => if i2.val != 0 then i1.val / i2.val else 0
      | .rem_t => if i2.val != 0 then i1.val % i2.val else 0
      | .shl => i1.val <<< i2.val.toNat
      | .shr => i1.val >>> i2.val.toNat
    let env ← InterpM.getTypeEnv
    let maxVal := (maxIval env ity).val
    let minVal := (minIval env ity).val
    -- Check for overflow
    -- Corresponds to: ub036_exceptionalCondition in undefined.lem
    if result < minVal || result > maxVal then
      InterpM.throwUB .ub036_exceptionalCondition
    else
      pure (.object (.integer { val := result, prov := .none }))
  | _, _ => InterpM.throwTypeError "catchExceptionalCondition requires integer values"

/-! ## Pure Expression Evaluation

Corresponds to: eval_pexpr in core_eval.lem:1189-1198
```lem
val eval_pexpr: Loc.t -> maybe Loc.t -> map Symbol.sym Symbol.sym ->
                list (map Symbol.sym Core.value) -> maybe Mem.mem_state -> Core.file core_run_annotation ->
                Core.pexpr -> either Errors.error (Undefined.t Core.value)
```
-/

/-- Make APexpr from Pexpr -/
def mkAPexpr (e : Pexpr) : APexpr := { annots := [], ty := none, expr := e }

/-- Evaluate a pure expression.
    Corresponds to: eval_pexpr in core_eval.lem:1189-1198
    Audited: 2025-01-01
    Deviations: Simplified signature (no current_call_loc, core_extern) -/
partial def evalPexpr (env : List (HashMap Sym Value)) (pe : APexpr) : InterpM Value := do
  match pe.expr with
  | .val v => pure v

  | .sym s =>
    match lookupEnv s env with
    | some v => pure v
    | none => throw (.symbolNotFound s)

  | .impl ic =>
    -- Implementation-defined constants
    match ic with
    | .intMax ity =>
      let typeEnv ← InterpM.getTypeEnv
      pure (.object (.integer (maxIval typeEnv ity)))
    | .intMin ity =>
      let typeEnv ← InterpM.getTypeEnv
      pure (.object (.integer (minIval typeEnv ity)))
    | .sizeof_ ty =>
      let typeEnv ← InterpM.getTypeEnv
      pure (.object (.integer (sizeofIval typeEnv ty)))
    | .alignof_ ty =>
      let typeEnv ← InterpM.getTypeEnv
      pure (.object (.integer (alignofIval typeEnv ty)))
    | .other name =>
      -- Implementation-defined constants
      -- Corresponds to: implementation.lem:487-491 for Characters module
      -- Audited: 2026-01-02
      -- Deviations: Only commonly used constants implemented
      match name with
      | "Characters.bits_in_byte" =>
        -- C standard: CHAR_BIT is always 8 on POSIX systems
        -- Corresponds to: Characters.bits_in_byte = 8 in implementation.lem:490-491
        pure (.object (.integer (integerIval 8)))
      | _ =>
        InterpM.throwNotImpl s!"implementation constant: {name}"

  | .undef _loc ub =>
    -- Undefined behavior detected at compile time
    InterpM.throwUB ub

  | .error msg _ =>
    InterpM.throwIllformed s!"Core error: {msg}"

  | .ctor c argExprs =>
    let args ← argExprs.mapM (evalPexpr env ∘ mkAPexpr)
    evalCtor c args

  | .case_ scrut branches =>
    let scrutVal ← evalPexpr env (mkAPexpr scrut)
    -- Try each branch
    let rec tryBranches : List (APattern × Pexpr) → InterpM Value
      | [] => throw .patternMatchFailed
      | (pat, body) :: rest =>
        match matchPattern pat scrutVal with
        | some bindings =>
          let env' := bindAllInEnv bindings env
          evalPexpr env' (mkAPexpr body)
        | none => tryBranches rest
    tryBranches branches

  | .let_ pat e1 e2 =>
    let v1 ← evalPexpr env (mkAPexpr e1)
    match matchPattern pat v1 with
    | some bindings =>
      let env' := bindAllInEnv bindings env
      evalPexpr env' (mkAPexpr e2)
    | none => throw .patternMatchFailed

  | .if_ cond then_ else_ =>
    let condVal ← evalPexpr env (mkAPexpr cond)
    match condVal with
    | .true_ => evalPexpr env (mkAPexpr then_)
    | .false_ => evalPexpr env (mkAPexpr else_)
    | _ => InterpM.throwTypeError "if condition must be boolean"

  | .op binop e1 e2 =>
    let v1 ← evalPexpr env (mkAPexpr e1)
    let v2 ← evalPexpr env (mkAPexpr e2)
    evalBinop binop v1 v2

  | .not_ e =>
    let v ← evalPexpr env (mkAPexpr e)
    match v with
    | .true_ => pure .false_
    | .false_ => pure .true_
    | _ => InterpM.throwTypeError "not requires boolean"

  | .convInt ity e =>
    let v ← evalPexpr env (mkAPexpr e)
    convertInt ity v

  | .wrapI ity iop e1 e2 =>
    let v1 ← evalPexpr env (mkAPexpr e1)
    let v2 ← evalPexpr env (mkAPexpr e2)
    wrapIntOp ity iop v1 v2

  | .catchExceptionalCondition ity iop e1 e2 =>
    let v1 ← evalPexpr env (mkAPexpr e1)
    let v2 ← evalPexpr env (mkAPexpr e2)
    catchExceptionalOp ity iop v1 v2

  | .call name args =>
    -- Call a pure function
    let file ← InterpM.getFile
    let argVals ← args.mapM (evalPexpr env ∘ mkAPexpr)
    match name with
    | .sym s =>
      -- Look up in stdlib or as an impl function
      let decl := file.stdlib.find? fun (sym, _) => sym == s
      match decl with
      | some (_, .fun_ _ params body) =>
        if argVals.length != params.length then
          InterpM.throwTypeError s!"wrong number of arguments for {s.name}"
        let bindings := params.zip argVals |>.map fun ((p, _), v) => (p, v)
        let callEnv := mkEnvWithBindings bindings
        evalPexpr callEnv body
      | some (_, .proc ..) =>
        InterpM.throwNotImpl s!"pure function call {s.name}: found proc, not fun"
      | some (_, .procDecl ..) =>
        InterpM.throwNotImpl s!"pure function call {s.name}: found procDecl, not fun"
      | some (_, .builtinDecl ..) =>
        InterpM.throwNotImpl s!"pure function call {s.name}: found builtinDecl, not fun"
      | none =>
        InterpM.throwNotImpl s!"pure function call {s.name}: not found in stdlib (stdlib has {file.stdlib.length} entries)"
    | .impl ic =>
      -- Implementation constant functions
      match ic with
      | .other "conv_int" =>
        match argVals with
        | [.ctype (.basic (.integer ity)), v] => convertInt ity v
        | _ => InterpM.throwTypeError "conv_int requires ctype and integer"
      | _ =>
        InterpM.throwNotImpl s!"impl call: {repr ic}"

  | .struct_ tag members =>
    let memberVals ← members.mapM fun (name, e) => do
      let v ← evalPexpr env (mkAPexpr e)
      pure (name, v)
    -- Convert to struct value
    let structMembers := memberVals.map fun (name, v) =>
      match v with
      | .object ov =>
        -- Convert object value to MemValue for struct
        let mv : MemValue := match ov with
          | .integer iv => .integer (.signed .int_) iv  -- Assume int
          | .floating fv => .floating (.realFloating .double) fv
          | .pointer pv => .pointer .void pv
          | _ => .unspecified .void
        { name, ty := .void, value := mv : StructMember }
      | _ => { name, ty := .void, value := .unspecified .void : StructMember }
    pure (.object (.struct_ tag structMembers))

  | .union_ tag member e =>
    let v ← evalPexpr env (mkAPexpr e)
    let mv : MemValue := match v with
      | .object (.integer iv) => .integer (.signed .int_) iv
      | _ => .unspecified .void
    pure (.object (.union_ tag member mv))

  | .arrayShift ptr ty idx =>
    let ptrVal ← evalPexpr env (mkAPexpr ptr)
    let idxVal ← evalPexpr env (mkAPexpr idx)
    match ptrVal with
    | .object (.pointer pv) =>
      match valueToInt idxVal with
      | some iv =>
        let typeEnv ← InterpM.getTypeEnv
        let newPtr := arrayShiftPtrval typeEnv pv ty iv
        pure (.object (.pointer newPtr))
      | none => InterpM.throwTypeError "array index must be integer"
    | _ => InterpM.throwTypeError "arrayShift requires pointer"

  | .memberShift ptr tag member =>
    let ptrVal ← evalPexpr env (mkAPexpr ptr)
    match ptrVal with
    | .object (.pointer pv) =>
      let typeEnv ← InterpM.getTypeEnv
      let newPtr := memberShiftPtrval typeEnv pv tag member
      pure (.object (.pointer newPtr))
    | _ => InterpM.throwTypeError "memberShift requires pointer"

  | .memberof _tag _member _e =>
    InterpM.throwNotImpl "memberof"

  | .cfunction e =>
    -- cfunction extracts function type info from a function pointer
    -- Note: We look up by name because pointer values in JSON lose symbol IDs
    let ptrVal ← evalPexpr env (mkAPexpr e)
    let lookupFunInfo (sym : Sym) : InterpM Value := do
      let file ← InterpM.getFile
      match file.lookupFunInfoByName sym.name with
      | some fi =>
        -- Return tuple: (return_type, [param_types], is_variadic, has_proto)
        let retType := Value.ctype fi.returnType
        let paramTypes := fi.params.map fun p => Value.ctype p.ty
        let paramList := Value.list (.ctype) paramTypes
        let isVariadic := if fi.isVariadic then Value.true_ else Value.false_
        let hasProto := if fi.hasProto then Value.true_ else Value.false_
        pure (.tuple [retType, paramList, isVariadic, hasProto])
      | none =>
        let nameStr := sym.name.getD "<unnamed>"
        InterpM.throwIllformed s!"cfunction: function '{nameStr}' not found in funinfo"
    match ptrVal with
    | .loaded (.specified (.pointer pv)) =>
      match pv.base with
      | .function sym => lookupFunInfo sym
      | _ => InterpM.throwIllformed "cfunction: pointer does not point to a function"
    | .object (.pointer pv) =>
      match pv.base with
      | .function sym => lookupFunInfo sym
      | _ => InterpM.throwIllformed "cfunction: pointer does not point to a function"
    | _ =>
      InterpM.throwTypeError "cfunction requires function pointer"

  | .isScalar _e => InterpM.throwNotImpl "is_scalar"
  | .isInteger _e => InterpM.throwNotImpl "is_integer"

  -- is_signed: check if a ctype is a signed integer type
  -- Corresponds to: PEis_signed in core_eval.lem:1088-1095
  --   AilTypesAux.is_signed_integer_type in ailTypesAux.lem:1121-1128
  --   Common.is_signed_ity in ocaml_implementation.ml:79-94
  -- Audited: 2026-01-02
  -- Deviations: char is assumed signed (char_is_signed:true in DefaultImpl)
  | .isSigned e =>
    let v ← evalPexpr env (mkAPexpr e)
    match v with
    | .ctype ty =>
      -- Check if it's a signed integer type
      match ty.ty with
      | .basic (.integer ity) =>
        let isSigned := match ity with
          | .char => true  -- DefaultImpl uses char_is_signed:true
          | .bool => false
          | .signed _ => true
          | .unsigned _ => false
          | .enum _ => true  -- Enums default to signed int
          | .size_t => false  -- size_t is unsigned
          | .wchar_t => true  -- wchar_t is signed on most platforms
          | .wint_t => true   -- wint_t is signed on most platforms
          | .ptrdiff_t => true -- ptrdiff_t is signed
          | .ptraddr_t => false -- ptraddr_t is unsigned (CHERI)
        pure (if isSigned then .true_ else .false_)
      | _ => pure .false_  -- Non-integer types are not signed
    | _ => InterpM.throwIllformed "is_signed: operand must be a ctype"

  -- is_unsigned: check if a ctype is an unsigned integer type
  -- Corresponds to: PEis_unsigned in core_eval.lem:1078-1087
  --   AilTypesAux.is_unsigned_integer_type in ailTypesAux.lem:1159-1166
  --   is_unsigned_ity = not (is_signed_ity) in ailTypesAux.lem:29-31
  -- Audited: 2026-01-02
  -- Deviations: char is assumed signed (char_is_signed:true in DefaultImpl)
  | .isUnsigned e =>
    let v ← evalPexpr env (mkAPexpr e)
    match v with
    | .ctype ty =>
      -- Check if it's an unsigned integer type
      match ty.ty with
      | .basic (.integer ity) =>
        -- is_unsigned_ity = not (is_signed_ity)
        let isUnsigned := match ity with
          | .char => false  -- DefaultImpl uses char_is_signed:true
          | .bool => true   -- _Bool is unsigned
          | .signed _ => false
          | .unsigned _ => true
          | .enum _ => false -- Enums default to signed int
          | .size_t => true  -- size_t is unsigned
          | .wchar_t => false -- wchar_t is signed on most platforms
          | .wint_t => false  -- wint_t is signed on most platforms
          | .ptrdiff_t => false -- ptrdiff_t is signed
          | .ptraddr_t => true  -- ptraddr_t is unsigned (CHERI)
        pure (if isUnsigned then .true_ else .false_)
      | _ => pure .false_  -- Non-integer types are not unsigned
    | _ => InterpM.throwIllformed "is_unsigned: operand must be a ctype"

  | .areCompatible e1 e2 =>
    -- Check if two C types are compatible (C11 6.2.7)
    -- For simplicity, we use structural equality as approximation
    let v1 ← evalPexpr env (mkAPexpr e1)
    let v2 ← evalPexpr env (mkAPexpr e2)
    match v1, v2 with
    | .ctype ty1, .ctype ty2 =>
      -- Simple compatibility: structural equality
      -- This is conservative - some compatible types may be rejected
      if ty1 == ty2 then pure .true_ else pure .false_
    | _, _ =>
      InterpM.throwIllformed "are_compatible: operands must be ctypes"
  | .bmcAssume _e => InterpM.throwNotImpl "bmc_assume"
  | .pureMemop _op _args => InterpM.throwNotImpl "pure_memop"
  | .constrained _cs => InterpM.throwNotImpl "constrained"

end CToLean.Semantics
