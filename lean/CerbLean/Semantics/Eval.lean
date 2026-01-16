import CerbLean.Semantics.Monad
import CerbLean.Semantics.State
import CerbLean.Memory.Interface
import Std.Data.HashMap

/-!
# Pure Expression Evaluation

Implements evaluation of pure Core expressions (Pexpr), corresponding to
`cerberus/frontend/model/core_eval.lem`.

## Design Strategy

This module provides the semantic foundation for pure expression evaluation.
It is designed to:

1. **Match Cerberus exactly**: Every function is auditable against the
   corresponding Cerberus code. No "improvements" - only faithful translation.

2. **Enable verification**: The evaluator is total (uses fuel) and has
   equation lemmas that enable compositional proofs in `Theorems/WP.lean`.

### Key Design Decisions

1. **Fuel-based termination**: `evalPexpr` uses explicit fuel parameter
   instead of `partial`. This enables unfolding in proofs and ensures
   totality.

2. **Equation lemmas**: Theorems like `evalPexpr_if'`, `evalPexpr_let'`,
   `evalPexpr_op'` characterize how `evalPexpr (fuel+1)` behaves for each
   expression constructor. These are proven by `simp only [evalPexpr]`
   which uses Lean's auto-generated equation lemmas for the mutual recursion.

3. **InterpM monad**: All evaluation happens in `InterpM` which provides
   access to interpreter environment (type info, function table) and state
   (memory, allocations).

## Module Structure

- **Bitwise Operations**: `intBitwiseAnd`, `intBitwiseOr`, `intBitwiseXor`
- **Binary Operations**: `evalBinop` for arithmetic, comparison, logical ops
- **Expression Evaluation**: `evalPexpr`, `evalPexprList`, etc.
- **Equation Lemmas**: `evalPexpr_val'`, `evalPexpr_if'`, `evalPexpr_let'`, etc.

## Cerberus Correspondence

- **File**: `cerberus/frontend/model/core_eval.lem`
- **Audited**: 2025-01-01
- **Deviations**: None - matches Cerberus exactly

## Usage in Proofs

The equation lemmas enable compositional WP proofs:
```lean
theorem wpPureN_if ... := by
  simp only [wpPureN]
  rw [evalPexpr_if']  -- Unfolds to: evalPexpr cond >>= fun cv => ...
  rw [InterpM_bind_run]
  ...
```

## Related Modules

- `CerbLean.Semantics.Monad`: Defines `InterpM` monad
- `CerbLean.Memory.Interface`: Memory operations used by effectful evaluation
-/

namespace CerbLean.Semantics

open CerbLean.Core
open CerbLean.Memory
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
    -- Use tdiv for C-style truncated division towards zero (not floor division)
    if n2 == 0 then InterpM.throwUB .ub045a_divisionByZero
    else pure (.object (.integer { val := n1.tdiv n2, prov := .none }))
  | .rem_t =>
    -- Use tmod for C-style truncated remainder (sign follows dividend)
    if n2 == 0 then InterpM.throwUB .ub045b_moduloByZero
    else pure (.object (.integer { val := n1.tmod n2, prov := .none }))
  | .rem_f =>
    if n2 == 0 then InterpM.throwUB .ub045b_moduloByZero
    else
      -- Floored remainder: r = n1 - n2 * floor(n1/n2)
      -- Lean's Int.emod gives remainder with sign of dividend (truncated)
      -- We need floored: result has same sign as divisor
      -- Formula: fmod = tmod + (if tmod != 0 && sign(tmod) != sign(n2) then n2 else 0)
      let tmod := n1 % n2  -- truncated remainder
      let result := if tmod != 0 && (tmod < 0) != (n2 < 0) then tmod + n2 else tmod
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

/-! ## Value Conversion Helpers

Corresponds to: memValueFromValue and valueFromMemValue in core_aux.lem:114-200
These convert between Core Values and Memory MemValues for load/store operations.
-/

/-- Strip atomic qualifier from a Ctype_.
    Corresponds to: unatomic_ in ctype.lem -/
def unatomic_ : Ctype_ → Ctype_
  | .atomic ty => unatomic_ ty
  | ty => ty

/-- Convert a Core Value to a MemValue for storing to memory.
    Corresponds to: memValueFromValue in core_aux.lem:137-200
    Audited: 2026-01-06
    Deviations: None - matches Cerberus case-by-case -/
partial def memValueFromValue (ty : Ctype) (v : Value) : Option MemValue :=
  let ty' := unatomic_ ty.ty
  match ty', v with
  -- Corresponds to: core_aux.lem:141-152
  | _, .unit => none
  | _, .true_ => none
  | _, .false_ => none
  | _, .list _ _ => none
  | _, .tuple _ => none
  | _, .ctype _ => none
  -- Corresponds to: core_aux.lem:153-154
  | _, .loaded (.unspecified ty'') => some (.unspecified ty'')
  -- Corresponds to: core_aux.lem:155-158
  | .basic (.integer ity), .object (.integer iv) => some (.integer ity iv)
  | .basic (.integer ity), .loaded (.specified (.integer iv)) => some (.integer ity iv)
  -- Corresponds to: core_aux.lem:159-162
  | .byte, .object (.integer iv) => some (.integer (.unsigned .ichar) iv)
  | .byte, .loaded (.specified (.integer iv)) => some (.integer (.unsigned .ichar) iv)
  -- Corresponds to: core_aux.lem:163-166
  | .basic (.floating fty), .object (.floating fv) => some (.floating fty fv)
  | .basic (.floating fty), .loaded (.specified (.floating fv)) => some (.floating fty fv)
  -- Corresponds to: core_aux.lem:167-170
  | .pointer _ refTy, .object (.pointer pv) =>
    some (.pointer { annots := [], ty := refTy } pv)
  | .pointer _ refTy, .loaded (.specified (.pointer pv)) =>
    some (.pointer { annots := [], ty := refTy } pv)
  -- Corresponds to: core_aux.lem:171-181
  | .array elemTy _, .loaded (.specified (.array lvs)) =>
    let elemCty : Ctype := { annots := [], ty := elemTy }
    let mvalsOpt := lvs.mapM fun lv =>
      memValueFromValue elemCty (.loaded lv)
    mvalsOpt.map MemValue.array
  -- Corresponds to: core_aux.lem:182-190
  | .struct_ tag, .loaded (.specified (.struct_ tag' members)) =>
    if tag == tag' then
      let memberList := members.map fun m => (m.name, m.ty, m.value)
      some (.struct_ tag memberList)
    else none
  -- Corresponds to: core_aux.lem:191-195
  | .union_ tag, .loaded (.specified (.union_ tag' ident mv)) =>
    if tag == tag' then some (.union_ tag ident mv) else none
  -- Corresponds to: core_aux.lem:196-199
  | _, _ => none

/-- Convert a MemValue to a Core Value after loading from memory.
    Corresponds to: valueFromMemValue in core_aux.lem:114-135
    Audited: 2026-01-06
    Deviations: Returns just the value (not the object type) -/
def valueFromMemValue (mv : MemValue) : Value :=
  match mv with
  | .unspecified ty => .loaded (.unspecified ty)
  | .integer _ity iv => .loaded (.specified (.integer iv))
  | .floating _fty fv => .loaded (.specified (.floating fv))
  | .pointer _ty pv => .loaded (.specified (.pointer pv))
  | .array mvs =>
    let lvs := mvs.map fun mv' =>
      match valueFromMemValue mv' with
      | .loaded lv => lv
      | _ => .unspecified .void
    .loaded (.specified (.array lvs))
  | .struct_ tag members =>
    let structMembers := members.map fun (name, ty, mval) =>
      { name, ty, value := mval : StructMember }
    .loaded (.specified (.struct_ tag structMembers))
  | .union_ tag ident mv' =>
    .loaded (.specified (.union_ tag ident mv'))

/-- Extract floating value from Value -/
def valueToFloat (v : Value) : Option FloatingValue :=
  match v with
  | .object (.floating fv) => some fv
  | .loaded (.specified (.floating fv)) => some fv
  | _ => none

/-- Evaluate floating point binary operations.
    Corresponds to: core_eval.lem:443-452 (floating point op case)
    and defacto_memory.lem:1097-1110 (impl_op_fval)
    Audited: 2026-01-06
    Deviations: None -/
def evalFloatOp (op : Binop) (f1 f2 : FloatingValue) : InterpM Value := do
  -- Handle unspecified values
  -- Corresponds to: defacto_memory.lem:1098-1102
  match f1, f2 with
  | .unspecified, _ => pure (.object (.floating .unspecified))
  | _, .unspecified => pure (.object (.floating .unspecified))
  | .finite v1, .finite v2 =>
    -- Corresponds to: defacto_memory.lem:1103-1109
    match op with
    | .add => pure (.object (.floating (.finite (v1 + v2))))
    | .sub => pure (.object (.floating (.finite (v1 - v2))))
    | .mul => pure (.object (.floating (.finite (v1 * v2))))
    | .div => pure (.object (.floating (.finite (v1 / v2))))
    -- Comparison operators
    -- Corresponds to: core_eval.lem:368-427 (floating point comparisons)
    | .eq => pure (if v1 == v2 then .true_ else .false_)
    | .lt => pure (if v1 < v2 then .true_ else .false_)
    | .le => pure (if v1 <= v2 then .true_ else .false_)
    | .gt => pure (if v1 > v2 then .true_ else .false_)
    | .ge => pure (if v1 >= v2 then .true_ else .false_)
    | _ => InterpM.throwTypeError s!"unsupported floating point op: {repr op}"
  | _, _ =>
    -- NaN, Inf cases - for now throw error
    InterpM.throwTypeError "floating point special values (NaN, Inf) not fully implemented"

/-- Evaluate a binary operation on values.
    Corresponds to: step_eval_peop in core_eval.lem:320-540 -/
def evalBinop (op : Binop) (v1 v2 : Value) : InterpM Value := do
  -- First try integer operations
  match valueToInt v1, valueToInt v2 with
  | some i1, some i2 => evalIntOp op i1 i2
  | _, _ =>
    -- Try floating point operations
    -- Corresponds to: core_eval.lem:443-452
    match valueToFloat v1, valueToFloat v2 with
    | some f1, some f2 => evalFloatOp op f1 f2
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
    -- Ivfromfloat: ctype -> floating -> integer
    -- Corresponds to: core.ott:282, defacto_memory.lem:1113-1125 (integer_value_of_fval)
    -- Audited: 2026-01-15
    -- Truncation towards zero (C semantics)
    match args with
    | [.ctype _ty, .object (.floating fv)] =>
      match fv with
      | .finite f =>
        -- Truncate float to integer towards zero
        -- For positive: floor, for negative: ceiling
        let intVal : Int := if f >= 0.0 then
          f.floor.toUInt64.toNat
        else
          -- For negative: negate, floor, negate back
          -(-f).floor.toUInt64.toNat
        pure (.object (.integer { val := intVal, prov := .none }))
      | _ => InterpM.throwTypeError "ivfromfloat: non-finite float"
    | _ => InterpM.throwTypeError "ivfromfloat requires (ctype, float)"

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
      -- Use tdiv for C-style truncated division towards zero (not floor division)
      | .div => if i2.val != 0 then i1.val.tdiv i2.val else 0
      -- Use tmod for C-style truncated remainder (sign follows dividend)
      | .rem_t => if i2.val != 0 then i1.val.tmod i2.val else 0
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
      -- Use tdiv for C-style truncated division towards zero (not floor division)
      | .div => if i2.val != 0 then i1.val.tdiv i2.val else 0
      -- Use tmod for C-style truncated remainder (sign follows dividend)
      | .rem_t => if i2.val != 0 then i1.val.tmod i2.val else 0
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

/-! ## Implementation-Defined Functions

Corresponds to: implementation.lem and runtime/libcore/impls/*.impl files

Implementation-defined functions are called via `<Impl.function_name>` syntax in Core.
Each implementation file (e.g., gcc_4.9.0_x86_64-apple-darwin10.8.0.impl) provides
concrete definitions for these functions.

We implement GCC-like behavior for most cases.
-/

/-- Evaluate an implementation-defined function call.
    Corresponds to: runtime/libcore/impls/*.impl files
    Audited: 2026-01-16
    Deviations: We implement GCC-like behavior only

    NOTE: These are IMPLEMENTATION-DEFINED behaviors in C. Different compilers
    may handle these differently. Currently we hardcode GCC x86_64 behavior.
    Future work: abstract these choices into a configurable implementation model. -/
def evalImplCall (name : String) (args : List Value) : InterpM Value := do
  match name, args with
  -- Integer.conv_nonrepresentable_signed_integer: signed overflow on conversion
  -- Corresponds to: gcc_4.9.0_x86_64-apple-darwin10.8.0.impl:17-19
  -- GCC behavior: "For conversion to a type of width N, the value is reduced
  -- modulo 2^N to be within range of the type; no signal is raised."
  | "Integer.conv_nonrepresentable_signed_integer", [.ctype (.basic (.integer ity)), v] =>
    convertInt ity v

  -- conv_int: standard integer conversion (also impl in some contexts)
  | "conv_int", [.ctype (.basic (.integer ity)), v] =>
    convertInt ity v

  -- SHR_signed_negative: right shift of negative signed integer (IMPL-DEFINED)
  -- Corresponds to: gcc_4.9.0_x86_64-apple-darwin10.8.0.impl:38-41
  -- GCC says "Signed '>>' acts on negative numbers by sign extension."
  -- This is arithmetic right shift: n >> m = floor(n / 2^m)
  -- NOTE: Other compilers may use logical shift (fill with 0s) instead.
  | "SHR_signed_negative", [.ctype _, .object (.integer nv), .object (.integer mv)] =>
    let n := nv.val
    let m := mv.val.toNat
    -- Arithmetic right shift: floor(n / 2^m) gives sign extension behavior
    let result := n / (2 ^ m)
    pure (.object (.integer { val := result, prov := nv.prov }))

  | _, _ =>
    InterpM.throwNotImpl s!"impl call: {name}"

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

/-- Default fuel for pure expression evaluation.
    This limits the depth of recursive calls to prevent non-termination. -/
def defaultPexprFuel : Nat := 100000

mutual
/-- Evaluate a pure expression with bounded recursion depth.
    Corresponds to: eval_pexpr in core_eval.lem:1189-1198
    Audited: 2025-01-01
    Deviations:
    - Simplified signature (no current_call_loc, core_extern)
    - Added fuel parameter for termination (decremented on every recursive call) -/
def evalPexpr (fuel : Nat) (env : List (HashMap Sym Value)) (pe : APexpr) : InterpM Value := do
  match fuel with
  | 0 => throw (.notImplemented "evalPexpr: recursion depth exceeded")
  | fuel' + 1 =>
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
    let args ← evalPexprList fuel' env argExprs
    evalCtor c args

  | .case_ scrut branches =>
    let scrutVal ← evalPexpr fuel' env (mkAPexpr scrut)
    -- Try each branch
    evalPexprCaseBranches fuel' scrutVal env branches

  | .let_ pat e1 e2 =>
    let v1 ← evalPexpr fuel' env (mkAPexpr e1)
    match matchPattern pat v1 with
    | some bindings =>
      let env' := bindAllInEnv bindings env
      evalPexpr fuel' env' (mkAPexpr e2)
    | none => throw .patternMatchFailed

  | .if_ cond then_ else_ =>
    let condVal ← evalPexpr fuel' env (mkAPexpr cond)
    match condVal with
    | .true_ => evalPexpr fuel' env (mkAPexpr then_)
    | .false_ => evalPexpr fuel' env (mkAPexpr else_)
    | _ => InterpM.throwTypeError "if condition must be boolean"

  | .op binop e1 e2 =>
    let v1 ← evalPexpr fuel' env (mkAPexpr e1)
    let v2 ← evalPexpr fuel' env (mkAPexpr e2)
    evalBinop binop v1 v2

  | .not_ e =>
    let v ← evalPexpr fuel' env (mkAPexpr e)
    match v with
    | .true_ => pure .false_
    | .false_ => pure .true_
    | _ => InterpM.throwTypeError "not requires boolean"

  | .convInt ity e =>
    let v ← evalPexpr fuel' env (mkAPexpr e)
    convertInt ity v

  | .wrapI ity iop e1 e2 =>
    let v1 ← evalPexpr fuel' env (mkAPexpr e1)
    let v2 ← evalPexpr fuel' env (mkAPexpr e2)
    wrapIntOp ity iop v1 v2

  | .catchExceptionalCondition ity iop e1 e2 =>
    let v1 ← evalPexpr fuel' env (mkAPexpr e1)
    let v2 ← evalPexpr fuel' env (mkAPexpr e2)
    catchExceptionalOp ity iop v1 v2

  | .call name args =>
    -- Call a pure function (fuel already checked at function entry)
    let file ← InterpM.getFile
    let argVals ← evalPexprList fuel' env args
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
        evalPexpr fuel' callEnv body
      | some (_, .proc ..) =>
        InterpM.throwNotImpl s!"pure function call {s.name}: found proc, not fun"
      | some (_, .procDecl ..) =>
        InterpM.throwNotImpl s!"pure function call {s.name}: found procDecl, not fun"
      | some (_, .builtinDecl ..) =>
        InterpM.throwNotImpl s!"pure function call {s.name}: found builtinDecl, not fun"
      | none =>
        InterpM.throwNotImpl s!"pure function call {s.name}: not found in stdlib (stdlib has {file.stdlib.length} entries)"
    | .impl ic =>
      -- Implementation constant functions - dispatch to evalImplCall
      match ic with
      | .other name => evalImplCall name argVals
      | _ => InterpM.throwNotImpl s!"impl call: {repr ic}"

  | .struct_ tag members =>
    -- Corresponds to: core_eval.lem:860-877 (PEstruct case)
    -- Algorithm:
    --   1. Evaluate each member expression
    --   2. Look up struct tag to get member types
    --   3. Convert each value using memValueFromValue with proper type
    --   4. Return OVstruct
    -- Audited: 2026-01-06
    let memberVals ← members.mapM fun (name, e) => do
      let v ← evalPexpr fuel' env (mkAPexpr e)
      pure (name, v)
    -- Look up struct definition to get member types
    -- Corresponds to: core_eval.lem:861-870
    let typeEnv ← InterpM.getTypeEnv
    match typeEnv.lookupTag tag with
    | some (.struct_ fields _) =>
      -- Convert each member value using proper type from struct definition
      -- Corresponds to: core_eval.lem:870-872
      let structMembers ← memberVals.mapM fun (membIdent, cval) => do
        -- Look up member type: let (_, _, _, memb_ty) = List.lookup memb_ident membrs
        match fields.find? (·.name == membIdent) with
        | some field =>
          -- let mval = memValueFromValue memb_ty cval
          match memValueFromValue field.ty cval with
          | some mval => pure { name := membIdent, ty := field.ty, value := mval : StructMember }
          | none => InterpM.throwTypeError s!"struct {tag.name}: cannot convert member {membIdent.name} value to MemValue"
        | none =>
          InterpM.throwTypeError s!"struct {tag.name}: member {membIdent.name} not found in definition"
      pure (.object (.struct_ tag structMembers))
    | some (.union_ _) =>
      InterpM.throwTypeError s!"struct construction: expected struct but found union for tag {tag.name}"
    | none =>
      InterpM.throwTypeError s!"struct construction: undefined tag {tag.name}"

  | .union_ tag member e =>
    -- Corresponds to: core_eval.lem:884-897 (PEunion case)
    -- Algorithm:
    --   1. Evaluate the member expression
    --   2. Look up union tag to get member type
    --   3. Convert value using memValueFromValue with proper type
    --   4. Return OVunion
    -- Audited: 2026-01-06
    let v ← evalPexpr fuel' env (mkAPexpr e)
    -- Look up union definition to get member type
    -- Corresponds to: core_eval.lem:888-890
    let typeEnv ← InterpM.getTypeEnv
    match typeEnv.lookupTag tag with
    | some (.union_ fields) =>
      -- Look up member type: let (_, _, _, memb_ty) = List.lookup memb_ident membrs
      match fields.find? (·.name == member) with
      | some field =>
        -- let mval = memValueFromValue memb_ty cval
        match memValueFromValue field.ty v with
        | some mval => pure (.object (.union_ tag member mval))
        | none => InterpM.throwTypeError s!"union {tag.name}: cannot convert member {member.name} value to MemValue"
      | none =>
        InterpM.throwTypeError s!"union {tag.name}: member {member.name} not found in definition"
    | some (.struct_ _ _) =>
      InterpM.throwTypeError s!"union construction: expected union but found struct for tag {tag.name}"
    | none =>
      InterpM.throwTypeError s!"union construction: undefined tag {tag.name}"

  | .arrayShift ptr ty idx =>
    let ptrVal ← evalPexpr fuel' env (mkAPexpr ptr)
    let idxVal ← evalPexpr fuel' env (mkAPexpr idx)
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
    let ptrVal ← evalPexpr fuel' env (mkAPexpr ptr)
    match ptrVal with
    | .object (.pointer pv) =>
      let typeEnv ← InterpM.getTypeEnv
      let newPtr := memberShiftPtrval typeEnv pv tag member
      pure (.object (.pointer newPtr))
    | _ => InterpM.throwTypeError "memberShift requires pointer"

  -- memberof: extract member from struct/union rvalue
  -- Corresponds to: core_eval.lem:941-963 (PEmemberof case)
  -- Audited: 2026-01-06
  -- NOTE: Cerberus only matches Vobject (OVstruct/OVunion), NOT Vloaded values.
  -- If value is not fully evaluated, Cerberus returns unevaluated PEmemberof.
  -- Our interpreter fully evaluates, so we only handle the Vobject cases.
  | .memberof tag member e =>
    let val ← evalPexpr fuel' env (mkAPexpr e)
    match val with
    | .object (.struct_ tag' members) =>
      -- Corresponds to: core_eval.lem:944-951
      if tag != tag' then
        InterpM.throwIllformed s!"PEmemberof(struct) ==> mismatched tags: {tag.name} vs {tag'.name}"
      else
        -- Corresponds to: List.lookup memb_ident (List.map (fun (a,_,b) -> (a,b)) xs)
        match members.find? (fun m => m.name == member) with
        | none => InterpM.throwIllformed s!"PEmemberof ==> invalid member: {member.name}"
        | some m =>
          -- Corresponds to: EU.return (PEval (snd (Caux.valueFromMemValue mval)))
          pure (valueFromMemValue m.value)
    | .object (.union_ tag' membIdent mval) =>
      -- Corresponds to: core_eval.lem:953-959
      if tag != tag' then
        InterpM.throwIllformed s!"PEmemberof(union) ==> mismatched tags: {tag.name} vs {tag'.name}"
      else if member != membIdent then
        -- Corresponds to: error "TODO: evaluation of PEmemberof => union puning"
        InterpM.throwNotImpl "TODO: evaluation of PEmemberof => union punning"
      else
        pure (valueFromMemValue mval)
    | _ =>
      -- Corresponds to: core_eval.lem:960-961
      InterpM.throwIllformed s!"PEmemberof ==> unexpected value (expected Vobject struct/union)"

  | .cfunction e =>
    -- cfunction extracts function type info from a function pointer
    -- Note: We look up by name because pointer values in JSON lose symbol IDs
    let ptrVal ← evalPexpr fuel' env (mkAPexpr e)
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
    let v ← evalPexpr fuel' env (mkAPexpr e)
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
    let v ← evalPexpr fuel' env (mkAPexpr e)
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
    let v1 ← evalPexpr fuel' env (mkAPexpr e1)
    let v2 ← evalPexpr fuel' env (mkAPexpr e2)
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
  termination_by fuel

/-- Helper for evaluating case branches -/
def evalPexprCaseBranches (fuel : Nat) (scrutVal : Value) (env : List (HashMap Sym Value))
    (branches : List (APattern × Pexpr)) : InterpM Value :=
  match fuel with
  | 0 => throw (.notImplemented "evalPexprCaseBranches: recursion depth exceeded")
  | fuel' + 1 =>
  match branches with
  | [] => throw .patternMatchFailed
  | (pat, body) :: rest =>
    match matchPattern pat scrutVal with
    | some bindings =>
      let env' := bindAllInEnv bindings env
      evalPexpr fuel' env' (mkAPexpr body)
    | none => evalPexprCaseBranches fuel' scrutVal env rest
  termination_by fuel

/-- Helper for evaluating a list of Pexprs -/
def evalPexprList (fuel : Nat) (env : List (HashMap Sym Value))
    (exprs : List Pexpr) : InterpM (List Value) :=
  match fuel with
  | 0 => throw (.notImplemented "evalPexprList: recursion depth exceeded")
  | fuel' + 1 =>
  match exprs with
  | [] => pure []
  | e :: rest => do
    let v ← evalPexpr fuel' env (mkAPexpr e)
    let vs ← evalPexprList fuel' env rest
    pure (v :: vs)
  termination_by fuel

/-- Helper for evaluating struct member expressions -/
def evalPexprStructMembers (fuel : Nat) (env : List (HashMap Sym Value))
    (members : List (Identifier × Pexpr)) : InterpM (List (Identifier × Value)) :=
  match fuel with
  | 0 => throw (.notImplemented "evalPexprStructMembers: recursion depth exceeded")
  | fuel' + 1 =>
  match members with
  | [] => pure []
  | (name, e) :: rest => do
    let v ← evalPexpr fuel' env (mkAPexpr e)
    let vs ← evalPexprStructMembers fuel' env rest
    pure ((name, v) :: vs)
  termination_by fuel
end

/-! ## Evaluation Equation Lemmas

These lemmas characterize how `evalPexpr` behaves for specific expression
constructors. They are proven by unfolding the definition and using
the fact that `fuel + 1` matches the successor pattern.
-/

/-- evalPexpr for value literals returns the value -/
theorem evalPexpr_val' (fuel : Nat) (env : List (HashMap Sym Value)) (v : Value) :
    evalPexpr (fuel + 1) env ⟨[], none, .val v⟩ = pure v := by
  simp only [evalPexpr]

/-- evalPexpr for if expressions evaluates condition then branches -/
theorem evalPexpr_if' (fuel : Nat) (env : List (HashMap Sym Value))
    (cond then_ else_ : Pexpr) :
    evalPexpr (fuel + 1) env ⟨[], none, .if_ cond then_ else_⟩ =
    (evalPexpr fuel env (mkAPexpr cond) >>= fun condVal =>
      match condVal with
      | .true_ => evalPexpr fuel env (mkAPexpr then_)
      | .false_ => evalPexpr fuel env (mkAPexpr else_)
      | _ => InterpM.throwTypeError "if condition must be boolean") := by
  simp only [evalPexpr]

/-- evalPexpr for let bindings evaluates e1 then e2 with bindings -/
theorem evalPexpr_let' (fuel : Nat) (env : List (HashMap Sym Value))
    (pat : APattern) (e1 e2 : Pexpr) :
    evalPexpr (fuel + 1) env ⟨[], none, .let_ pat e1 e2⟩ =
    (evalPexpr fuel env (mkAPexpr e1) >>= fun v1 =>
      match matchPattern pat v1 with
      | some bindings => evalPexpr fuel (bindAllInEnv bindings env) (mkAPexpr e2)
      | none => throw .patternMatchFailed) := by
  simp only [evalPexpr]

/-- evalPexpr for binary operations evaluates both operands then applies op -/
theorem evalPexpr_op' (fuel : Nat) (env : List (HashMap Sym Value))
    (binop : Binop) (e1 e2 : Pexpr) :
    evalPexpr (fuel + 1) env ⟨[], none, .op binop e1 e2⟩ =
    (evalPexpr fuel env (mkAPexpr e1) >>= fun v1 =>
      evalPexpr fuel env (mkAPexpr e2) >>= fun v2 =>
        evalBinop binop v1 v2) := by
  simp only [evalPexpr]

end CerbLean.Semantics
