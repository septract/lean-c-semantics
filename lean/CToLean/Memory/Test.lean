/-
  Memory model unit tests
  Tests core memory operations without needing the full interpreter.
-/

import CToLean.Memory

namespace CToLean.Memory.Test

open CToLean.Core
open CToLean.Memory

/-! ## Test Helpers -/

/-- Empty type environment for simple tests -/
def emptyEnv : TypeEnv := { tagDefs := [] }

/-- Run a memory operation and return result -/
def runMem (m : ConcreteMemM α) : Except MemError α :=
  runConcreteMemM' emptyEnv m

/-- Run a memory operation expecting success -/
def expectOk (m : ConcreteMemM α) (msg : String := "expected success") : IO α := do
  match runMem m with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{msg}: {e}")

/-- Run a memory operation expecting a specific error -/
def expectError (m : ConcreteMemM α) (check : MemError → Bool) (msg : String := "expected error") : IO Unit := do
  match runMem m with
  | .ok _ => throw (IO.userError s!"{msg}: got success instead of error")
  | .error e =>
    if check e then pure ()
    else throw (IO.userError s!"{msg}: got wrong error {e}")

/-! ## Layout Tests -/

#check sizeof emptyEnv (.basic (.integer (.signed .int_))) -- Should be 4

/-- Test basic type sizes -/
def testBasicSizes : IO Unit := do
  let env := emptyEnv

  -- Integer types
  assert! sizeof env (.basic (.integer (.signed .ichar))) == 1
  assert! sizeof env (.basic (.integer (.signed .short))) == 2
  assert! sizeof env (.basic (.integer (.signed .int_))) == 4
  assert! sizeof env (.basic (.integer (.signed .long))) == 8
  assert! sizeof env (.basic (.integer (.signed .longLong))) == 8

  -- Unsigned same sizes
  assert! sizeof env (.basic (.integer (.unsigned .int_))) == 4

  -- Floating types
  assert! sizeof env (.basic (.floating .float)) == 4
  assert! sizeof env (.basic (.floating .double)) == 8
  assert! sizeof env (.basic (.floating .longDouble)) == 16

  -- Pointer
  assert! sizeof env (.pointer {} .void) == 8

  -- Bool
  assert! sizeof env (.basic (.integer .bool)) == 1

  IO.println "✓ Basic size tests passed"

/-- Test alignment -/
def testAlignment : IO Unit := do
  let env := emptyEnv

  assert! alignof env (.basic (.integer (.signed .ichar))) == 1
  assert! alignof env (.basic (.integer (.signed .int_))) == 4
  assert! alignof env (.basic (.integer (.signed .long))) == 8
  assert! alignof env (.basic (.floating .double)) == 8
  assert! alignof env (.pointer {} .void) == 8

  IO.println "✓ Alignment tests passed"

/-- Test array sizes -/
def testArraySizes : IO Unit := do
  let env := emptyEnv

  -- int[10] = 40 bytes
  assert! sizeof env (.array (.basic (.integer (.signed .int_))) (some 10)) == 40

  -- char[100] = 100 bytes
  assert! sizeof env (.array (.basic (.integer .char)) (some 100)) == 100

  -- Flexible array member has size 0
  assert! sizeof env (.array (.basic (.integer (.signed .int_))) none) == 0

  IO.println "✓ Array size tests passed"

/-! ## Memory Operation Tests -/

/-- Test basic allocation -/
def testAllocation : IO Unit := do
  let result ← expectOk (do
    -- Allocate an int
    let intTy := Ctype.basic (.integer (.signed .int_))
    let ptr ← allocateImpl "x" 4 (some intTy) 4 .writable none
    pure ptr
  ) "allocation"

  -- Should have provenance
  match result.prov with
  | .some _ => pure ()
  | _ => throw (IO.userError "allocation should have provenance")

  IO.println "✓ Allocation test passed"

/-- Test store and load roundtrip -/
def testStoreLoad : IO Unit := do
  let intTy := Ctype.basic (.integer (.signed .int_))

  let result ← expectOk (do
    -- Allocate
    let ptr ← allocateImpl "x" 4 (some intTy) 4 .writable none

    -- Store value 42
    let val : MemValue := .integer (.signed .int_) (integerIval 42)
    let _ ← storeImpl intTy false ptr val

    -- Load it back
    let (_, loaded) ← loadImpl intTy ptr
    pure loaded
  ) "store/load"

  -- Check we got 42 back
  match result with
  | .integer _ iv =>
    if iv.val == 42 then
      IO.println "✓ Store/load roundtrip test passed"
    else
      throw (IO.userError s!"expected 42, got {iv.val}")
  | _ => throw (IO.userError s!"expected integer, got {repr result}")

/-- Test null pointer dereference detection -/
def testNullDeref : IO Unit := do
  let intTy := Ctype.basic (.integer (.signed .int_))
  let nullPtr := nullPtrval intTy

  expectError (loadImpl intTy nullPtr)
    (fun e => match e with | .access .nullPtr _ => true | _ => false)
    "null dereference"

  IO.println "✓ Null dereference detection test passed"

/-- Test use-after-free detection -/
def testUseAfterFree : IO Unit := do
  let intTy := Ctype.basic (.integer (.signed .int_))

  -- This needs to run in sequence, so we use a single computation
  let result := runConcreteMemM emptyEnv (do
    -- Allocate
    let ptr ← allocateImpl "x" 4 (some intTy) 4 .writable none

    -- Free it
    killImpl true ptr

    -- Try to load - should fail
    let (_, _) ← loadImpl intTy ptr
    pure ()
  )

  match result with
  | .error (.access .deadPtr _) =>
    IO.println "✓ Use-after-free detection test passed"
  | .error e =>
    throw (IO.userError s!"expected deadPtr error, got {e}")
  | .ok _ =>
    throw (IO.userError "expected error for use-after-free")

/-- Test double-free detection -/
def testDoubleFree : IO Unit := do
  let intTy := Ctype.basic (.integer (.signed .int_))

  let result := runConcreteMemM emptyEnv (do
    let ptr ← allocateImpl "x" 4 (some intTy) 4 .writable none
    killImpl true ptr
    killImpl true ptr  -- Double free
  )

  match result with
  | .error (.free .deadAllocation) =>
    IO.println "✓ Double-free detection test passed"
  | .error e =>
    throw (IO.userError s!"expected deadAllocation error, got {e}")
  | .ok _ =>
    throw (IO.userError "expected error for double-free")

/-- Test out-of-bounds access detection -/
def testOutOfBounds : IO Unit := do
  let intTy := Ctype.basic (.integer (.signed .int_))

  let result := runConcreteMemM emptyEnv (do
    -- Allocate single int (4 bytes)
    let ptr ← allocateImpl "x" 4 (some intTy) 4 .writable none

    -- Shift pointer past allocation
    let shiftedPtr ← effArrayShiftPtrvalImpl ptr intTy (integerIval 10)

    -- Try to load from out-of-bounds location
    let _ ← loadImpl intTy shiftedPtr
    pure ()
  )

  match result with
  | .error (.access .outOfBoundPtr _) =>
    IO.println "✓ Out-of-bounds detection test passed"
  | .error e =>
    throw (IO.userError s!"expected outOfBoundPtr error, got {e}")
  | .ok _ =>
    throw (IO.userError "expected error for out-of-bounds access")

/-- Test read-only memory protection -/
def testReadOnly : IO Unit := do
  let intTy := Ctype.basic (.integer (.signed .int_))

  let result := runConcreteMemM emptyEnv (do
    -- Allocate and store with locking
    let ptr ← allocateImpl "const_x" 4 (some intTy) 4 .writable none
    let val : MemValue := .integer (.signed .int_) (integerIval 42)
    let _ ← storeImpl intTy true ptr val  -- isLocking = true

    -- Try to store again - should fail
    let val2 : MemValue := .integer (.signed .int_) (integerIval 100)
    let _ ← storeImpl intTy false ptr val2
    pure ()
  )

  match result with
  | .error .readonlyWrite =>
    IO.println "✓ Read-only protection test passed"
  | .error e =>
    throw (IO.userError s!"expected readonlyWrite error, got {e}")
  | .ok _ =>
    throw (IO.userError "expected error for write to read-only")

/-- Test pointer arithmetic -/
def testPointerArithmetic : IO Unit := do
  let intTy := Ctype.basic (.integer (.signed .int_))

  let result := runConcreteMemM emptyEnv (do
    -- Allocate array of 10 ints
    let ptr ← allocateImpl "arr" 40 (some (.array intTy (some 10))) 4 .writable none

    -- Get base address
    let baseAddr := match ptr.base with
      | .concrete _ a => a
      | _ => 0

    -- Shift by 5 elements
    let shifted ← effArrayShiftPtrvalImpl ptr intTy (integerIval 5)
    let shiftedAddr := match shifted.base with
      | .concrete _ a => a
      | _ => 0

    -- Should be 5 * 4 = 20 bytes ahead
    pure (shiftedAddr - baseAddr)
  )

  match result with
  | .ok (diff, _) =>
    if diff == 20 then
      IO.println "✓ Pointer arithmetic test passed"
    else
      throw (IO.userError s!"expected offset 20, got {diff}")
  | .error e =>
    throw (IO.userError s!"pointer arithmetic failed: {e}")

/-- Test pointer comparison -/
def testPointerComparison : IO Unit := do
  let intTy := Ctype.basic (.integer (.signed .int_))

  let result ← expectOk (do
    let ptr ← allocateImpl "arr" 40 (some (.array intTy (some 10))) 4 .writable none
    let shifted ← effArrayShiftPtrvalImpl ptr intTy (integerIval 5)

    let eq ← eqPtrvalImpl ptr ptr
    let ne ← eqPtrvalImpl ptr shifted
    let lt : Bool := match ptr.base, shifted.base with
      | .concrete _ a1, .concrete _ a2 => a1 < a2
      | _, _ => false

    pure (eq, !ne, lt)
  ) "pointer comparison"

  match result with
  | (true, true, true) =>
    IO.println "✓ Pointer comparison test passed"
  | (a, b, c) =>
    throw (IO.userError s!"pointer comparison failed: eq={a} ne={b} lt={c}")

/-! ## Run All Tests -/

/-- Run all memory model tests -/
def runAllTests : IO Unit := do
  IO.println "Running memory model tests..."
  IO.println ""

  IO.println "=== Layout Tests ==="
  testBasicSizes
  testAlignment
  testArraySizes
  IO.println ""

  IO.println "=== Memory Operation Tests ==="
  testAllocation
  testStoreLoad
  testNullDeref
  testUseAfterFree
  testDoubleFree
  testOutOfBounds
  testReadOnly
  testPointerArithmetic
  testPointerComparison
  IO.println ""

  IO.println "All tests passed!"

end CToLean.Memory.Test
