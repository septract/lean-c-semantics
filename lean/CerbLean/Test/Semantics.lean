/-
  Tests for CN Separation Logic Semantics
  Tests the definitions in CerbLean.CN.Semantics
-/

import CerbLean.CN.Semantics

namespace CerbLean.Test.Semantics

open CerbLean.Core
open CerbLean.Memory
open CerbLean.CN
open CerbLean.CN.Semantics

/-! ## Helper: signed int type -/

/-- Signed int type -/
def signedInt : IntegerType := .signed .int_

/-! ## Level 1: Context Tests -/

/-- Test empty context -/
def testEmptyContext : Bool :=
  let ctx := Context.empty
  ctx.resources.isEmpty && ctx.constraints.isEmpty

#guard testEmptyContext

/-! ## Level 2: HeapFragment Tests -/

/-- Test location equality -/
def testLocationEq : Bool :=
  let loc1 : Location := ⟨1, 0x1000⟩
  let loc2 : Location := ⟨1, 0x1000⟩
  let loc3 : Location := ⟨2, 0x1000⟩
  loc1 == loc2 && loc1 != loc3

#guard testLocationEq

/-- Test empty heap fragment -/
def testEmptyHeap : Bool :=
  let h := HeapFragment.empty
  h.cells.isEmpty

#guard testEmptyHeap

/-- Test singleton heap fragment -/
def testSingletonHeap : Bool :=
  let loc : Location := ⟨1, 0x1000⟩
  let val := HeapValue.integer signedInt 42
  let h := HeapFragment.singleton loc val
  h.cells.length == 1

#guard testSingletonHeap

/-- Test heap lookup -/
def testHeapLookup : Bool :=
  let loc : Location := ⟨1, 0x1000⟩
  let val := HeapValue.integer signedInt 42
  let h := HeapFragment.singleton loc val
  match h.lookup loc with
  | some (HeapValue.integer _ n) => n == 42
  | _ => false

#guard testHeapLookup

/-- Test heap lookup miss -/
def testHeapLookupMiss : Bool :=
  let loc1 : Location := ⟨1, 0x1000⟩
  let loc2 : Location := ⟨1, 0x2000⟩
  let val := HeapValue.integer signedInt 42
  let h := HeapFragment.singleton loc1 val
  match h.lookup loc2 with
  | none => true
  | some _ => false

#guard testHeapLookupMiss

/-- Test heap union -/
def testHeapUnion : Bool :=
  let loc1 : Location := ⟨1, 0x1000⟩
  let loc2 : Location := ⟨1, 0x2000⟩
  let val1 := HeapValue.integer signedInt 42
  let val2 := HeapValue.integer signedInt 100
  let h1 := HeapFragment.singleton loc1 val1
  let h2 := HeapFragment.singleton loc2 val2
  let h := h1 ++ h2
  h.cells.length == 2

#guard testHeapUnion

/-- Test heap domain -/
def testHeapDom : Bool :=
  let loc1 : Location := ⟨1, 0x1000⟩
  let loc2 : Location := ⟨1, 0x2000⟩
  let val := HeapValue.integer signedInt 42
  let h := HeapFragment.singleton loc1 val ++ HeapFragment.singleton loc2 val
  h.dom.length == 2

#guard testHeapDom

/-! ## HeapValue Tests -/

/-- Test integer value -/
def testIntegerValue : Bool :=
  let v := HeapValue.integer signedInt 42
  match v with
  | .integer _ n => n == 42
  | _ => false

#guard testIntegerValue

/-- Test pointer value -/
def testPointerValue : Bool :=
  let loc : Location := ⟨1, 0x1000⟩
  let v := HeapValue.pointer (some loc)
  match v with
  | .pointer (some l) => l == loc
  | _ => false

#guard testPointerValue

/-- Test null pointer -/
def testNullPointer : Bool :=
  let v := HeapValue.pointer none
  match v with
  | .pointer none => true
  | _ => false

#guard testNullPointer

/-! ## Valuation Tests -/

/-- Test valuation lookup -/
def testValuationLookup : Bool :=
  let sym1 := mkSym "x" 1
  let sym2 := mkSym "y" 2
  let val1 := HeapValue.integer signedInt 42
  let val2 := HeapValue.integer signedInt 100
  let ρ : Valuation := [(sym1, val1), (sym2, val2)]
  match ρ.lookup sym1 with
  | some (HeapValue.integer _ n) => n == 42
  | _ => false

#guard testValuationLookup

/-- Test valuation lookup miss -/
def testValuationLookupMiss : Bool :=
  let sym1 := mkSym "x" 1
  let sym2 := mkSym "y" 2
  let sym3 := mkSym "z" 3
  let val := HeapValue.integer signedInt 42
  let ρ : Valuation := [(sym1, val), (sym2, val)]
  match ρ.lookup sym3 with
  | none => true
  | some _ => false

#guard testValuationLookupMiss

/-! ## enumList Tests -/

/-- Test enumList empty -/
def testEnumListEmpty : Bool :=
  enumList ([] : List Nat) == []

#guard testEnumListEmpty

/-- Test enumList -/
def testEnumList : Bool :=
  let result := enumList [10, 20, 30]
  result == [(0, 10), (1, 20), (2, 30)]

#guard testEnumList

/-! ## Disjointness Tests -/

/-- Empty heaps are disjoint -/
example : HeapFragment.empty.disjoint HeapFragment.empty := by
  simp [HeapFragment.disjoint, HeapFragment.dom, HeapFragment.empty]

/-- Singleton heaps at different locations are disjoint -/
example :
  let loc1 : Location := ⟨1, 0x1000⟩
  let loc2 : Location := ⟨1, 0x2000⟩
  let val := HeapValue.integer signedInt 42
  let h1 := HeapFragment.singleton loc1 val
  let h2 := HeapFragment.singleton loc2 val
  h1.disjoint h2 := by
  simp only [HeapFragment.disjoint, HeapFragment.dom, HeapFragment.singleton]
  intro loc hloc
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hloc
  subst hloc
  simp only [List.map_cons, List.map_nil, List.mem_singleton, Location.mk.injEq, true_and]
  decide

/-! ## Specification Tests -/

/-- Empty spec structure -/
def testEmptySpec : Bool :=
  let spec : FunctionSpec := { requires := ⟨[]⟩, ensures := ⟨[]⟩, trusted := false }
  spec.requires.clauses.isEmpty && spec.ensures.clauses.isEmpty

#guard testEmptySpec

/-- Trusted spec -/
def testTrustedSpec : Bool :=
  let spec : FunctionSpec := { requires := ⟨[]⟩, ensures := ⟨[]⟩, trusted := true }
  spec.trusted

#guard testTrustedSpec

/-! ## Summary -/

/-- Run all computable tests -/
def runAllTests : IO Unit := do
  IO.println "=== CN Semantics Tests (Two-Level Approach) ==="
  IO.println ""

  -- Level 1: Context tests
  IO.println "--- Level 1: Context ---"
  IO.println s!"Empty context: {if testEmptyContext then "PASS" else "FAIL"}"
  IO.println ""

  -- Level 2: HeapFragment tests
  IO.println "--- Level 2: HeapFragment ---"
  IO.println s!"Location equality: {if testLocationEq then "PASS" else "FAIL"}"
  IO.println s!"Empty heap: {if testEmptyHeap then "PASS" else "FAIL"}"
  IO.println s!"Singleton heap: {if testSingletonHeap then "PASS" else "FAIL"}"
  IO.println s!"Heap lookup: {if testHeapLookup then "PASS" else "FAIL"}"
  IO.println s!"Heap lookup miss: {if testHeapLookupMiss then "PASS" else "FAIL"}"
  IO.println s!"Heap union: {if testHeapUnion then "PASS" else "FAIL"}"
  IO.println s!"Heap domain: {if testHeapDom then "PASS" else "FAIL"}"
  IO.println ""

  -- HeapValue tests
  IO.println "--- HeapValue ---"
  IO.println s!"Integer value: {if testIntegerValue then "PASS" else "FAIL"}"
  IO.println s!"Pointer value: {if testPointerValue then "PASS" else "FAIL"}"
  IO.println s!"Null pointer: {if testNullPointer then "PASS" else "FAIL"}"
  IO.println ""

  -- Valuation tests
  IO.println "--- Valuation ---"
  IO.println s!"Valuation lookup: {if testValuationLookup then "PASS" else "FAIL"}"
  IO.println s!"Valuation lookup miss: {if testValuationLookupMiss then "PASS" else "FAIL"}"
  IO.println ""

  -- enumList tests
  IO.println "--- Helpers ---"
  IO.println s!"enumList empty: {if testEnumListEmpty then "PASS" else "FAIL"}"
  IO.println s!"enumList: {if testEnumList then "PASS" else "FAIL"}"
  IO.println ""

  -- Spec tests
  IO.println "--- Spec ---"
  IO.println s!"Empty spec: {if testEmptySpec then "PASS" else "FAIL"}"
  IO.println s!"Trusted spec: {if testTrustedSpec then "PASS" else "FAIL"}"
  IO.println ""

  IO.println "All tests passed!"

end CerbLean.Test.Semantics
