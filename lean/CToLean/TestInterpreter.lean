/-
  Interpreter test executable
-/

import CToLean.Parser
import CToLean.Semantics
import CToLean.Memory

open CToLean.Core
open CToLean.Parser
open CToLean.Semantics
open CToLean.Memory

/-- Convert UndefinedBehavior to its canonical code string (matching Cerberus) -/
def ubToCode : UndefinedBehavior → String
  | .dummy msg => s!"dummy({msg})"
  | .unspecifiedLvalue => "unspecified_lvalue"
  | .ub009_outsideLifetime => "UB009_outside_lifetime"
  | .ub010_pointerToDeadObject => "UB010_pointer_to_dead_object"
  | .ub011_useIndeterminateAutomatic => "UB011_use_indeterminate_automatic"
  | .ub_modifyingTemporaryLifetime => "UB_modifying_temporary_lifetime"
  | .ub012_lvalueReadTrapRepresentation => "UB012_lvalue_read_trap"
  | .ub013_lvalueSideEffectTrap => "UB013_lvalue_sideeffect_trap"
  | .ub008_multipleLinkage => "UB008_multiple_linkage"
  | .ub015_incompatibleRedeclaration => "UB015_incompatible_redeclaration"
  | .ub017_outOfRangeFloatingIntConversion => "UB017_out_of_range_floating_int"
  | .ub019_lvalueNotAnObject => "UB019_lvalue_not_object"
  | .ub024_outOfRangePointerToIntConversion => "UB024_out_of_range_ptr_int"
  | .ub025_misalignedPointerConversion => "UB025_misaligned_ptr"
  | .ub033_modifyingStringLiteral => "UB033_modifying_string_literal"
  | .ub035_unsequencedRace => "UB035_unsequenced_race"
  | .ub036_exceptionalCondition => "UB036_exceptional_condition"
  | .ub037_illtypedLoad => "UB037_illtyped_load"
  | .ub038_numberOfArgs => "UB038_number_of_args"
  | .ub041_functionNotCompatible => "UB041_function_not_compatible"
  | .ub042_accessAtomicStructUnionMember => "UB042_access_atomic_struct_union"
  | .ub043_indirectionInvalidValue => "UB043_indirection_invalid"
  | .ub045a_divisionByZero => "UB045a_division_by_zero"
  | .ub045b_moduloByZero => "UB045b_modulo_by_zero"
  | .ub045c_quotientNotRepresentable => "UB045c_quotient_not_representable"
  | .ub046_arrayPointerOutside => "UB046_array_pointer_outside"
  | .ub047a_arrayPointerAdditionBeyondIndirection => "UB047a_ptr_add_beyond"
  | .ub047b_arrayPointerSubtractionBeyondIndirection => "UB047b_ptr_sub_beyond"
  | .ub048_disjointArrayPointersSubtraction => "UB048_disjoint_ptr_sub"
  | .ub050_pointersSubtractionNotRepresentable => "UB050_ptr_sub_not_representable"
  | .ub051a_negativeShift => "UB051a_negative_shift"
  | .ub051b_shiftTooLarge => "UB051b_shift_too_large"
  | .ub052a_negativeLeftShift => "UB052a_negative_left_shift"
  | .ub052b_nonRepresentableLeftShift => "UB052b_non_representable_left_shift"
  | .ub053_distinctAggregateUnionPointerComparison => "UB053_distinct_aggregate_ptr_cmp"
  | .ub054a_inexactlyOverlappingAssignment => "UB054a_inexact_overlapping_assign"
  | .ub054b_incompatibleOverlappingAssignment => "UB054b_incompatible_overlapping_assign"
  | .ub059_incompleteNoLinkageIdentifier => "UB059_incomplete_no_linkage"
  | .ub061_noNamedMembers => "UB061_no_named_members"
  | .ub064_modifyingConst => "UB064_modifying_const"
  | .ub070_inlineNotDefined => "UB070_inline_not_defined"
  | .ub071_noreturn => "UB071_noreturn"
  | .ub088_endOfNonVoidFunction => "UB088_end_of_non_void"
  | .ub_cerb001_integerToDeadPointer => "CERB001_int_to_dead_ptr"
  | .ub_cerb002a_outOfBoundLoad => "CERB002a_out_of_bound_load"
  | .ub_cerb002b_outOfBoundStore => "CERB002b_out_of_bound_store"
  | .ub_cerb002c_outOfBoundFree => "CERB002c_out_of_bound_free"
  | .ub_cerb002d_outOfBoundRealloc => "CERB002d_out_of_bound_realloc"
  | .ub_cerb003_invalidFunctionPointer => "CERB003_invalid_function_pointer"
  | .ub_cerb004_unspecified ctx => s!"CERB004_unspecified({repr ctx})"
  | .ub_cerb005_freeNullptr => "CERB005_free_nullptr"
  | .other name => name  -- Pass through the exact Cerberus code

/-- Convert memory errors to UB codes (matching Cerberus UB categories) -/
def memErrorToUBCode : MemError → String
  | .access .nullPtr _ => "UB043_indirection_invalid_value"  -- null pointer deref
  | .access .functionPtr _ => "UB043_indirection_invalid_value"
  | .access .deadPtr _ => "UB010_pointer_to_dead_object"
  | .access .outOfBoundPtr _ => "UB_CERB002a_out_of_bound_load"
  | .access .noProvPtr _ => "UB043_indirection_invalid_value"
  | .access .atomicMemberof _ => "UB042_access_atomic_struct_union_member"
  | .free .nonMatching => "UB_CERB002c_out_of_bound_free"
  | .free .deadAllocation => "UB_CERB002c_out_of_bound_free"  -- double free
  | .free .outOfBound => "UB_CERB002c_out_of_bound_free"
  | .memcpy .overlap => "UB_memcpy_overlap"
  | .memcpy .nonObject => "UB_memcpy_non_object"
  | .memcpy .deadObject => "UB010_pointer_to_dead_object"
  | .memcpy .outOfBound => "UB_CERB002a_out_of_bound_load"
  | .readonlyWrite .stringLiteral => "UB033_modifying_string_literal"
  | .readonlyWrite .temporaryLifetime => "UB_modifying_temporary_lifetime"
  | .readonlyWrite .constQualified => "UB064_modifying_const"
  | .uninitRead _ => "UB011_use_indeterminate_automatic"
  | .trapRepresentation .read => "UB012_lvalue_read_trap_representation"
  | .trapRepresentation .write => "UB013_lvalue_sideeffect_trap"
  | .outsideLifetime _ => "UB009_outside_lifetime"
  | .typeError _ => "UB_internal_type_error"
  | .ptrArithOverflow => "UB046_array_pointer_outside"
  | .alignmentError _ _ => "UB025_misaligned_pointer_conversion"
  | .ptrdiff => "UB050_pointers_subtraction_not_representable"

/-- Parse JSON file and run interpreter -/
def runFile (jsonPath : String) (batch : Bool) : IO Unit := do
  let contents ← IO.FS.readFile jsonPath
  match parseFileFromString contents with
  | .ok file =>
    let result := runMain file
    if batch then
      -- Batch mode: output simple parseable format
      match result.error with
      | some (.undefinedBehavior ub _) =>
        IO.println s!"Undefined \{ub: \"{ubToCode ub}\"}"
      | some (.memoryError err) =>
        -- Memory errors are UB in C semantics
        IO.println s!"Undefined \{ub: \"{memErrorToUBCode err}\"}"
      | some e =>
        IO.println s!"Error \{msg: \"{e}\"}"
      | none =>
        match result.returnValue with
        | some v => IO.println s!"Defined \{value: \"{v}\"}"
        | none => IO.println "Defined {value: \"void\"}"
    else
      -- Verbose mode: full details
      IO.println s!"Result: {result}"
      match result.returnValue with
      | some v => IO.println s!"Return value: {v}"
      | none => IO.println "No return value"
      if result.stdout != "" then
        IO.println s!"stdout: {result.stdout}"
      if result.stderr != "" then
        IO.println s!"stderr: {result.stderr}"
      match result.error with
      | some e => IO.println s!"Error: {e}"
      | none => pure ()
  | .error e =>
    IO.println s!"Parse error: {e}"

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [jsonPath] =>
    runFile jsonPath false
    pure 0
  | ["--batch", jsonPath] =>
    runFile jsonPath true
    pure 0
  | [jsonPath, "--batch"] =>
    runFile jsonPath true
    pure 0
  | _ =>
    IO.println "Usage: ctolean_interp [--batch] <json-file>"
    pure 1
