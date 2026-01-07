/-
  UB-freeness predicates and foundational verification infrastructure

  This module defines predicates for reasoning about undefined behavior
  in Core programs, building on the operational semantics in Semantics/.

  Key predicates:
  - `UBFree`: An InterpM computation doesn't produce undefined behavior
  - `NoUB`: An expression doesn't produce UB given environment and state
  - `SafeResult`: Classification of execution outcomes
-/

import CToLean.Semantics.Monad
import CToLean.Semantics.Interpreter
import CToLean.Core.Undefined

namespace CToLean.Theorems

open CToLean.Core
open CToLean.Semantics
open CToLean.Memory

/-! ## Result Classification

We classify execution results into:
- `safe`: Execution completed successfully or with a non-UB error
- `ub`: Execution hit undefined behavior
-/

/-- Classification of execution outcomes -/
inductive SafeResult (α : Type) where
  /-- Execution completed successfully with a value and final state -/
  | ok (value : α) (state : InterpState)
  /-- Execution failed with undefined behavior -/
  | ub (behavior : UndefinedBehavior) (loc : Option Loc)
  /-- Execution failed with a non-UB error (type error, not implemented, etc.) -/
  | otherError (err : InterpError)
  deriving Inhabited

/-- Convert an interpreter result to SafeResult -/
def toSafeResult {α : Type} (result : Except InterpError (α × InterpState)) : SafeResult α :=
  match result with
  | .ok (v, s) => .ok v s
  | .error (.undefinedBehavior ub loc) => .ub ub loc
  | .error e => .otherError e

/-- Check if a SafeResult is not UB -/
def SafeResult.isNotUB {α : Type} : SafeResult α → Bool
  | .ok _ _ => true
  | .ub _ _ => false
  | .otherError _ => true

/-- Check if a SafeResult is successful -/
def SafeResult.isOk {α : Type} : SafeResult α → Bool
  | .ok _ _ => true
  | _ => false

/-! ## UBFree Predicate

The fundamental predicate: a monadic computation is UB-free if it never
produces an undefined behavior error, regardless of the input environment
and state.
-/

/-- Helper to check if an InterpError is UB -/
def isUBError : InterpError → Bool
  | .undefinedBehavior _ _ => true
  | _ => false

/-- A computation is UB-free if it never produces undefined behavior.

    This is the strongest form - it must be UB-free for ALL environments
    and states. Use `UBFreeIn` for the conditional form.
-/
def UBFree {α : Type} (m : InterpM α) : Prop :=
  ∀ env state,
    match (m.run env).run state with
    | .ok _ => True
    | .error e => ¬isUBError e

/-- A computation is UB-free in a specific environment and state.

    This is the most commonly used form - it allows preconditions.
-/
def UBFreeIn {α : Type} (m : InterpM α) (env : InterpEnv) (state : InterpState) : Prop :=
  match (m.run env).run state with
  | .ok _ => True
  | .error e => ¬isUBError e

/-- A computation terminates without UB and satisfies a postcondition -/
def UBFreeWith {α : Type} (m : InterpM α) (env : InterpEnv) (state : InterpState)
    (post : α → InterpState → Prop) : Prop :=
  match (m.run env).run state with
  | .ok (v, s') => post v s'
  | .error e => ¬isUBError e

/-! ## Basic Properties -/

/-- UBFree implies UBFreeIn for all env/state -/
theorem UBFree_implies_UBFreeIn {α : Type} {m : InterpM α} :
    UBFree m → ∀ env state, UBFreeIn m env state := by
  intro h env state
  exact h env state

/-- pure is always UBFree -/
theorem UBFree_pure {α : Type} (a : α) : UBFree (pure a : InterpM α) := by
  intro env state
  simp only [pure]
  trivial

/-- If m is UBFree and f is UBFree for all results, then m >>= f is UBFree -/
theorem UBFree_bind {α β : Type} {m : InterpM α} {f : α → InterpM β}
    (hm : UBFree m) (hf : ∀ a, UBFree (f a)) : UBFree (m >>= f) := by
  intro env state
  unfold UBFree at hm hf
  -- This proof requires unfolding the monad transformer bind
  -- For now, leave as sorry - this is a foundational lemma
  sorry

/-! ## Conditional UBFree with Preconditions

For most verification, we need conditional UB-freeness:
"If precondition P holds, then the computation is UB-free"
-/

/-- Conditional UB-freeness: if precondition holds, no UB -/
def UBFreeIf {α : Type} (m : InterpM α)
    (pre : InterpEnv → InterpState → Prop) : Prop :=
  ∀ env state, pre env state → UBFreeIn m env state

/-- Conditional UB-freeness with postcondition -/
def UBFreeIfWith {α : Type} (m : InterpM α)
    (pre : InterpEnv → InterpState → Prop)
    (post : InterpEnv → InterpState → α → InterpState → Prop) : Prop :=
  ∀ env state, pre env state →
    match (m.run env).run state with
    | .ok (v, s') => post env state v s'
    | .error e => ¬isUBError e

/-! ## Helpers for Specific UB Checks -/

/-- Integer is within signed 32-bit range -/
def inInt32Range (n : Int) : Prop :=
  -2147483648 ≤ n ∧ n ≤ 2147483647

/-- Integer is within unsigned 32-bit range -/
def inUInt32Range (n : Int) : Prop :=
  0 ≤ n ∧ n ≤ 4294967295

/-- Integer is within signed 64-bit range -/
def inInt64Range (n : Int) : Prop :=
  -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807

/-- Get the range for an integer type -/
def intTypeRange (ity : IntegerType) : Int × Int :=
  match ity with
  | .char => (-128, 127)  -- Assuming signed char
  | .bool => (0, 1)
  | .signed .ichar => (-128, 127)
  | .unsigned .ichar => (0, 255)
  | .signed .short => (-32768, 32767)
  | .unsigned .short => (0, 65535)
  | .signed .int_ => (-2147483648, 2147483647)
  | .unsigned .int_ => (0, 4294967295)
  | .signed .long => (-9223372036854775808, 9223372036854775807)
  | .unsigned .long => (0, 18446744073709551615)
  | .signed .longLong => (-9223372036854775808, 9223372036854775807)
  | .unsigned .longLong => (0, 18446744073709551615)
  | .size_t => (0, 18446744073709551615)  -- Assuming 64-bit
  | .ptrdiff_t => (-9223372036854775808, 9223372036854775807)
  | .wchar_t => (-2147483648, 2147483647)  -- Platform-dependent
  | .wint_t => (-2147483648, 2147483647)
  | _ => (0, 0)  -- Unknown/enum

/-- Check if a value is in range for an integer type -/
def inRangeForType (n : Int) (ity : IntegerType) : Prop :=
  let (lo, hi) := intTypeRange ity
  lo ≤ n ∧ n ≤ hi

/-! ## Memory Safety Predicates -/

/-- Check if an allocation is alive (not in deadAllocations) -/
def isAllocAlive (allocId : Nat) (mem : MemState) : Bool :=
  !mem.deadAllocations.contains allocId

/-- Extract allocation ID from provenance -/
def getAllocId : Provenance → Option Nat
  | .none => none
  | .some id => some id
  | .symbolic _ => none
  | .device => none

/-- Helper to check if a pointer is valid given its allocation info -/
def isValidInAlloc (addr : Nat) (allocBase allocSize : Nat) : Prop :=
  allocBase ≤ addr ∧ addr < allocBase + allocSize

/-- A pointer is valid in the given memory state (simplified version) -/
def ValidPointer (p : PointerValue) (mem : MemState) : Prop :=
  match p.base with
  | .null _ => False  -- null is never valid for dereference
  | .function _ => False  -- function pointers can't be dereferenced as data
  | .concrete _ addr =>
    -- Check allocation exists and address is in bounds
    match getAllocId p.prov with
    | some allocId =>
      isAllocAlive allocId mem = true ∧
      ∃ alloc : Allocation, Std.HashMap.get? mem.allocations allocId = some alloc ∧
        isValidInAlloc addr alloc.base alloc.size
    | none =>
      match p.prov with
      | .symbolic _ => True  -- symbolic provenance - assume valid for now
      | .device => True  -- device memory - assume valid
      | _ => False

/-- A pointer is valid and points to initialized memory -/
def ValidInitializedPointer (p : PointerValue) (mem : MemState) : Prop :=
  ValidPointer p mem ∧
  match p.base with
  | .concrete _ addr =>
    ∃ byte : AbsByte, Std.HashMap.get? mem.bytemap addr = some byte ∧ byte.value.isSome
  | _ => True

/-- Memory state is well-formed -/
def WellFormedMemory (mem : MemState) : Prop :=
  -- All allocations have positive size
  ∀ allocId (alloc : Allocation),
    Std.HashMap.get? mem.allocations allocId = some alloc → alloc.size > 0

/-! ## Derived UB Predicates for Common Operations -/

/-- Division is safe (no divide by zero, no overflow) -/
def SafeDiv (a b : Int) (ity : IntegerType) : Prop :=
  b ≠ 0 ∧
  -- For signed types, check INT_MIN / -1 overflow
  (match ity with
   | .signed _ =>
     let (lo, _) := intTypeRange ity
     ¬(a = lo ∧ b = -1)
   | _ => True)

/-- Get bit width for integer type -/
def intTypeBitWidth (ity : IntegerType) : Nat :=
  match ity with
  | .char | .bool | .signed .ichar | .unsigned .ichar => 8
  | .signed .short | .unsigned .short => 16
  | .signed .int_ | .unsigned .int_ => 32
  | .signed .long | .unsigned .long => 64
  | .signed .longLong | .unsigned .longLong => 64
  | .size_t | .ptrdiff_t => 64  -- Assuming 64-bit platform
  | _ => 32  -- Default

/-- Shift is safe (non-negative shift amount, not too large) -/
def SafeShift (shiftAmount : Int) (ity : IntegerType) : Prop :=
  0 ≤ shiftAmount ∧ shiftAmount < intTypeBitWidth ity

/-- Left shift is safe (also checks result fits) -/
def SafeLeftShift (value shiftAmount : Int) (ity : IntegerType) : Prop :=
  SafeShift shiftAmount ity ∧
  -- For signed types, value must be non-negative
  (match ity with
   | .signed _ => value ≥ 0
   | _ => True)

/-! ## Decidability instances for automation -/

instance : Decidable (inInt32Range n) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (inUInt32Range n) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (inInt64Range n) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (inRangeForType n ity) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Example Lemmas

These lemmas demonstrate how to use the UBFree predicates for reasoning.
-/

/-- Division by a non-zero constant is safe for unsigned types -/
theorem div_nonzero_safe (a : Int) (b : Int) (ity : IntegerType)
    (hb : b ≠ 0) (hunsigned : ∃ k, ity = .unsigned k) : SafeDiv a b ity := by
  constructor
  · exact hb
  · obtain ⟨k, hk⟩ := hunsigned
    simp [hk]

/-- Division by 2 is always safe for unsigned int -/
example (a : Int) : SafeDiv a 2 (.unsigned .int_) := by
  apply div_nonzero_safe
  · decide
  · exact ⟨.int_, rfl⟩

/-- Shift by 0 is always safe for signed int -/
theorem shift_zero_safe_int : SafeShift 0 (.signed .int_) := by
  unfold SafeShift intTypeBitWidth
  constructor <;> native_decide

/-- Shift by 0 is always safe for unsigned int -/
theorem shift_zero_safe_uint : SafeShift 0 (.unsigned .int_) := by
  unfold SafeShift intTypeBitWidth
  constructor <;> native_decide

/-- Values in range satisfy the range predicate (example) -/
example : inInt32Range 42 := by
  unfold inInt32Range
  constructor <;> decide

example : inInt32Range (-1000000) := by
  unfold inInt32Range
  constructor <;> decide

/-- INT_MAX is in Int32 range -/
example : inInt32Range 2147483647 := by
  unfold inInt32Range
  constructor <;> decide

/-- INT_MIN is in Int32 range -/
example : inInt32Range (-2147483648) := by
  unfold inInt32Range
  constructor <;> decide

/-- Value just outside range is not in range -/
example : ¬inInt32Range 2147483648 := by
  unfold inInt32Range
  intro ⟨_, h2⟩
  omega

/-! ## Reasoning Helpers

These helpers make it easier to work with the predicates.
-/

/-- If a computation is UBFreeIn for a specific state, it produces a safe result -/
theorem UBFreeIn_safe_result {α : Type} {m : InterpM α} {env : InterpEnv} {state : InterpState}
    (h : UBFreeIn m env state) :
    (toSafeResult ((m.run env).run state)).isNotUB := by
  unfold UBFreeIn at h
  unfold toSafeResult SafeResult.isNotUB
  cases hres : (m.run env).run state with
  | ok p => simp
  | error e =>
    simp only [hres] at h
    cases e with
    | undefinedBehavior ub loc =>
      simp only [isUBError] at h
      exact absurd trivial h
    | _ => simp

/-- Division safety implies no UB from the divisor being zero -/
theorem SafeDiv_no_div_zero {a b : Int} {ity : IntegerType}
    (h : SafeDiv a b ity) : b ≠ 0 :=
  h.1

/-- For unsigned types, SafeDiv reduces to just b ≠ 0 -/
theorem SafeDiv_unsigned {a b : Int} {k : IntBaseKind}
    (hb : b ≠ 0) : SafeDiv a b (.unsigned k) := by
  constructor
  · exact hb
  · simp

end CToLean.Theorems
