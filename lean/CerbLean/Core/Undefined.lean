/-
  Undefined behavior kinds
  Corresponds to: cerberus/frontend/model/undefined.lem lines 21-733
  Audited: 2026-02-09
  Deviations: All Cerberus UB codes included. CHERI codes included for completeness.
-/

import Std.Data.HashMap

namespace CerbLean.Core

/-! ## Undefined by Omission

Corresponds to: undefined_by_omission in undefined.lem lines 16-18
-/

/-- UB by standard omission
    Corresponds to: undefined_by_omission in undefined.lem lines 16-18
    Audited: 2026-02-09 -/
inductive UndefinedByOmission where
  | memcpyNonObject
  | memcpyOutOfBound
  deriving Repr, BEq, Inhabited

/-! ## Unspecified UB Context

Corresponds to: unspecified_ub_context in undefined.lem lines 5-14
-/

/-- Context for unspecified behavior becoming undefined
    Corresponds to: unspecified_ub_context in undefined.lem lines 5-14
    Audited: 2026-02-09
    Deviations: None -/
inductive UnspecifiedUBContext where
  | equalityPtrVsNull
  | equalityBothArithOrPtr
  | pointerAdd
  | pointerSub
  | conditional
  | copyAllocId
  | rvalueMemberof
  | memberofptr
  | do_
  deriving Repr, BEq, Inhabited

/-! ## Undefined Behavior

Corresponds to: undefined_behaviour in undefined.lem lines 21-733
Complete enumeration of all Cerberus UB codes.
-/

/-- Undefined behavior categories
    Corresponds to: undefined_behaviour in undefined.lem lines 21-733
    Audited: 2026-02-09
    Deviations: None — all Cerberus codes present -/
inductive UndefinedBehavior where
  -- Dummy/placeholder (undefined.lem:22)
  | dummy (msg : String)
  -- Unspecified lvalue (undefined.lem:26)
  | unspecifiedLvalue
  -- Standard omission (undefined.lem:28)
  | stdOmission (ctx : UndefinedByOmission)
  -- §clause 4: A "shall" requirement outside a constraint is violated
  | ub001
  -- §5.1.1.2: Nonempty source file doesn't end in newline
  | ub002
  -- §5.1.1.2: Token concatenation produces universal character name
  | ub003
  -- §5.1.2.2.1: Incorrect main function forms
  | ub004a_incorrectMainReturnType
  | ub004b_incorrectMainArgument1
  | ub004c_incorrectMainArgument2
  | ub004d_mainNotFunction
  -- §5.1.2.4: Data race
  | ub005_dataRace
  -- §5.2.1: Invalid character in source file
  | ub006
  -- §5.2.1.2: Invalid multibyte character
  | ub007
  -- §6.2.2: Same identifier has internal and external linkage
  | ub008_multipleLinkage
  -- §6.2.4: Object referred to outside lifetime
  | ub009_outsideLifetime
  -- §6.2.4: Pointer to dead object used
  | ub010_pointerToDeadObject
  -- §6.2.4: Use of indeterminate automatic storage object
  | ub011_useIndeterminateAutomatic
  -- §6.2.4: Attempt to modify object with temporary lifetime
  | ub_modifyingTemporaryLifetime
  -- §6.2.6.1: Trap representation read by non-char lvalue
  | ub012_lvalueReadTrapRepresentation
  -- §6.2.6.1: Trap representation produced by side effect
  | ub013_lvalueSideEffectTrap
  -- §6.2.6.2: Negative zero not supported
  | ub014_unsupportedNegativeZero
  -- §6.2.7: Incompatible redeclaration
  | ub015_incompatibleRedeclaration
  -- §6.2.7: Composite type from VLA with unevaluated size
  | ub016
  -- §6.3.1.4: Out of range floating to integer conversion
  | ub017_outOfRangeFloatingIntConversion
  -- §6.3.1.5: Floating demotion out of range
  | ub018
  -- §6.3.2.1: lvalue doesn't designate an object
  | ub019_lvalueNotAnObject
  -- §6.3.2.1: Non-array incomplete lvalue conversion
  | ub020_nonarrayIncompleteLvalueConversion
  -- §6.3.2.1: Uninitialized register auto object used
  | ub021
  -- §6.3.2.1: Register array decays to pointer
  | ub022_registerArrayDecay
  -- §6.3.2.2: Void expression used
  | ub023
  -- §6.3.2.3: Pointer to integer conversion out of range
  | ub024_outOfRangePointerToIntConversion
  -- §6.3.2.3: Misaligned pointer conversion
  | ub025_misalignedPointerConversion
  -- §6.3.2.3: Function called through incompatible pointer
  | ub026
  -- §6.4: Unmatched quote
  | ub027
  -- §6.4.1: Reserved keyword misuse
  | ub028
  -- §6.4.2.1: Universal character name out of range
  | ub029
  -- §6.4.2.1: Initial identifier character is digit UCN
  | ub030
  -- §6.4.2.1: Identifiers differ only in nonsignificant chars
  | ub031
  -- §6.4.2.2: __func__ explicitly declared
  | ub032
  -- §6.4.5: Attempt to modify string literal
  | ub033_modifyingStringLiteral
  -- §6.4.7: Invalid chars in header name
  | ub034
  -- §6.5: Unsequenced race
  | ub035_unsequencedRace
  -- §6.5: Exceptional condition during evaluation
  | ub036_exceptionalCondition
  -- §6.5: Object accessed with wrong lvalue type
  | ub037_illtypedLoad
  -- §6.5.2.2: Wrong number of arguments
  | ub038_numberOfArgs
  -- §6.5.2.2: Prototype mismatch after promotion
  | ub039
  -- §6.5.2.2: Non-prototype argument type mismatch
  | ub040
  -- §6.5.2.2: Function type not compatible
  | ub041_functionNotCompatible
  -- §6.5.2.3: Atomic struct/union member accessed
  | ub042_accessAtomicStructUnionMember
  -- §6.5.3.2: Unary * on invalid pointer
  | ub043_indirectionInvalidValue
  -- §6.5.4: Pointer converted to non-integer/pointer type
  | ub044
  -- §6.5.5: Division/modulo by zero, quotient not representable
  | ub045a_divisionByZero
  | ub045b_moduloByZero
  | ub045c_quotientNotRepresentable
  -- §6.5.6: Pointer arithmetic out of bounds
  | ub046_arrayPointerOutside
  | ub047a_arrayPointerAdditionBeyondIndirection
  | ub047b_arrayPointerSubtractionBeyondIndirection
  -- §6.5.6: Disjoint array pointer subtraction
  | ub048_disjointArrayPointersSubtraction
  -- §6.5.6: Array subscript out of range
  | ub049
  -- §6.5.6: Pointer subtraction not representable
  | ub050_pointersSubtractionNotRepresentable
  -- §6.5.7: Shift operations
  | ub051a_negativeShift
  | ub051b_shiftTooLarge  -- Note: Cerberus has typo "UB51b" (no 0)
  | ub052a_negativeLeftShift
  | ub052b_nonRepresentableLeftShift
  -- §6.5.8: Pointer comparison from different objects
  | ub053_distinctAggregateUnionPointerComparison
  -- §6.5.16.1: Overlapping assignment
  | ub054a_inexactlyOverlappingAssignment
  | ub054b_incompatibleOverlappingAssignment
  -- §6.6: Invalid integer constant expression
  | ub055_invalidIntegerConstantExpression
  -- §6.6: Constant expression in initializer invalid
  | ub056
  -- §6.6: Arithmetic constant expression invalid
  | ub057
  -- §6.6: Object value accessed in address constant creation
  | ub058
  -- §6.7: Incomplete no-linkage identifier
  | ub059_incompleteNoLinkageIdentifier
  -- §6.7.1: Block scope function with storage class
  | ub060_blockScopeFunctionWithStorageClass
  -- §6.7.2.1: No named members
  | ub061_noNamedMembers
  -- §6.7.2.1: Flexible array member with no elements
  | ub062
  -- §6.7.2.3: Incomplete struct/union not completed in scope
  | ub063
  -- §6.7.3: Modifying const-qualified object
  | ub064_modifyingConst
  -- §6.7.3: Volatile access through non-volatile lvalue
  | ub065
  -- §6.7.3: Function type includes qualifiers
  | ub066_qualifiedFunctionSpecification
  -- §6.7.3: Incompatible qualified types
  | ub067
  -- §6.7.3.1: Restrict violation (modified through const restrict)
  | ub068
  -- §6.7.3.1: Restrict pointer assigned incompatible value
  | ub069
  -- §6.7.4: Inline not defined in TU
  | ub070_inlineNotDefined
  -- §6.7.4: _Noreturn function returns
  | ub071_noreturn
  -- §6.7.5: Incompatible alignment specifiers
  | ub072_incompatibleAlignmentSpecifiers
  -- §6.7.5: Different alignment specifiers across TUs
  | ub073
  -- §6.7.6.1: Incompatible pointer types
  | ub074
  -- §6.7.6.2: VLA size is nonpositive
  | ub075
  -- §6.7.6.2: Incompatible array types
  | ub076
  -- §6.7.6.3: Static array parameter not enough elements
  | ub077
  -- §6.7.6.3: Modified void parameter
  | ub078_modifiedVoidParameter
  -- §6.7.6.3: Incompatible function types
  | ub079
  -- §6.7.9: Unnamed member value used
  | ub080
  -- §6.7.9: Scalar initializer not single expression
  | ub081_scalarInitializerNotSingleExpression
  -- §6.7.9: Struct/union auto initializer invalid
  | ub082
  -- §6.7.9: Aggregate initializer not brace-enclosed
  | ub083
  -- §6.9: External linkage identifier not exactly one definition
  | ub084
  -- §6.9.1: Identifier list params not declared
  | ub085
  -- §6.9.1: Adjusted parameter not complete object type
  | ub086_incompleteAdjustedParameter
  -- §6.9.1: Variadic function without ellipsis
  | ub087
  -- §6.9.1: End of non-void function reached
  | ub088_endOfNonVoidFunction
  -- §6.9.2: Tentative definition with internal linkage, incomplete type
  | ub089_tentativeDefinitionInternalLinkage
  -- §6.10.1: 'defined' generated during preprocessing
  | ub090
  -- §6.10.2: #include result doesn't match header form
  | ub091
  -- §6.10.2: #include doesn't start with letter
  | ub092
  -- §6.10.3: Preprocessing directives in macro arguments
  | ub093
  -- §6.10.3.2: # result not valid string literal
  | ub094
  -- §6.10.3.3: ## result not valid preprocessing token
  | ub095
  -- §6.10.4: #line invalid form
  | ub096
  -- §6.10.6: Non-STDC pragma causes UB
  | ub097
  -- §6.10.6: #pragma STDC invalid form
  | ub098
  -- §6.10.8: Predefined macro #define/#undef
  | ub099
  -- §7 (clause 7): Copy to overlapping object via library function
  | ub100
  -- §7.1.2: File with standard header name in standard place
  | ub101
  -- §7.1.2: Header included within external declaration
  | ub102
  -- §7.1.2: Standard header entity used before include
  | ub103
  -- §7.1.2: Standard header included with keyword macro
  | ub104
  -- §7.1.2: Library function declared without external linkage
  | ub105
  -- §7.1.3: Reserved identifier declared/defined
  | ub106
  -- §7.1.3: Underscore macro removed
  | ub107
  -- §7.1.4: Invalid library function argument
  | ub108
  -- §7.1.4: Invalid pointer to library array parameter
  | ub109
  -- §7.2: assert macro definition suppressed
  | ub110
  -- §7.2: assert argument not scalar type
  | ub111_illtypedAssert
  -- §7.3.4,7.6.1,7.12.2: Pragma in wrong context
  | ub112
  -- §7.4: Character handling function arg out of range
  | ub113
  -- §7.5: errno macro suppressed or redefined
  | ub114
  -- §7.6.1: FENV_ACCESS off but FP status used
  | ub115
  -- §7.6.2: Invalid exception mask
  | ub116
  -- §7.6.2.4: fesetexceptflag with wrong flags
  | ub117
  -- §7.6.4.3,7.6.4.4: fesetenv/feupdateenv with invalid arg
  | ub118
  -- §7.8.2,7.22.6,7.22.1: Integer arithmetic result not representable
  | ub119
  -- §7.11.1.1: setlocale string modified
  | ub120
  -- §7.11.2.1: localeconv structure modified
  | ub121
  -- §7.12: math_errhandling suppressed or redefined
  | ub122
  -- §7.12.3,7.12.14: FP classification arg not real floating
  | ub123
  -- §7.13: setjmp macro suppressed or redefined
  | ub124
  -- §7.13.2.1: setjmp in disallowed context
  | ub125
  -- §7.13.2.1: longjmp to nonexistent environment
  | ub126
  -- §7.13.2.1: longjmp access to changed non-volatile auto
  | ub127
  -- §7.14.1.1: Invalid signal handler pointer
  | ub128
  -- §7.14.1.1: Signal handler returns for computational exception
  | ub129
  -- §7.14.1.1: SIGFPE/SIGILL/SIGSEGV handler returns
  | ub130
  -- §7.14.1.1: Signal handler calls raise during abort/raise signal
  | ub131
  -- §7.14.1.1: Signal handler accesses non-atomic non-volatile static
  | ub132
  -- §7.14.1.1: errno referenced after signal
  | ub133
  -- §7.14.1.1: Signal generated by async handler
  | ub134
  -- §7.14.1.1: signal() used in multithreaded program
  | ub135
  -- §7.16: Variadic args accessed improperly
  | ub136
  -- §7.16: va_arg invoked with passed-through ap
  | ub137
  -- §7.16.1: va_start/va_arg/va_copy/va_end macro suppressed
  | ub138
  -- §7.16.1: va_start/va_copy without va_end
  | ub139
  -- §7.16.1.1: va_arg type not pointer-postfixable
  | ub140
  -- §7.16.1.1: va_arg with no next argument or wrong type
  | ub141
  -- §7.16.1.2,7.16.1.4: va_copy/va_start on already-initialized va_list
  | ub142
  -- §7.16.1.4: va_start parmN is register/function/array/incompatible
  | ub143
  -- §7.19: offsetof with invalid member or bitfield
  | ub144
  -- §7.20.4: Integer constant macro arg invalid
  | ub145
  -- §7.21.2: Byte I/O on wide stream or vice versa
  | ub146
  -- §7.21.2: File portion beyond last wide char used
  | ub147
  -- §7.21.3: FILE pointer used after close
  | ub148
  -- §7.21.5.2: fflush on input stream
  | ub149
  -- §7.21.5.3: fopen mode string invalid
  | ub150
  -- §7.21.5.3: Update stream I/O ordering violation
  | ub151
  -- §7.21.5.6: setvbuf array contents used
  | ub152
  -- §7.21.6.1,7.21.6.2: Insufficient/illtyped format arguments
  | ub153a_insufficientArgumentsForFormat
  | ub153b_illtypedArgumentForFormat
  -- Invalid format string
  | invalidFormat (fmt : String)
  -- §7.21.6.1: Precision with wrong conversion specifier
  | ub154
  -- §7.21.6.1: Asterisk field width/precision without argument
  | ub155
  -- §7.21.6.1: # or 0 flag with wrong conversion specifier
  | ub156
  -- §7.21.6.1: Invalid length modifier
  | ub157
  -- §7.21.6.1,7.21.6.2: Length modifier with wrong conversion
  | ub158_invalidLengthModifier
  -- §7.21.6.1: %s argument missing null terminator
  | ub159
  -- §7.21.6.1,7.21.6.2: %n with flags/suppression/width/precision
  | ub160
  -- §7.21.6.1,7.21.6.2: %% not exact
  | ub161
  -- §7.21.6.1,7.21.6.2: Invalid conversion specification
  | ub162
  -- §7.21.6.1: Formatted output count > INT_MAX
  | ub163
  -- §7.21.6.2: Formatted input count > INT_MAX
  | ub164
  -- §7.21.6.2: Conversion result can't be represented
  | ub165
  -- §7.21.6.2: %c/%s/%[ array too small
  | ub166
  -- §7.21.6.2: Wide %c/%s/%[ input not valid multibyte
  | ub167
  -- §7.21.6.2: %p input not from earlier conversion
  | ub168
  -- §7.21.6.8-14: v*printf/v*scanf with bad va_list
  | ub169
  -- §7.21.7.2: fgets/fgetws array used after read error
  | ub170
  -- §7.21.7.10: Binary stream position after ungetc from 0
  | ub171
  -- §7.21.8.1,7.21.8.2: Stream position after fread/fwrite error
  | ub172
  -- §7.21.8.1: Partial fread element used
  | ub173
  -- §7.21.9.2: fseek on text stream with wrong offset
  | ub174
  -- §7.21.9.3: fsetpos with wrong position
  | ub175
  -- §7.22.3: Zero-size allocation non-null pointer used
  | ub176
  -- §7.22.3: Freed/realloced pointer value used
  | ub177
  -- §7.22.3.1: aligned_alloc invalid alignment/size
  | ub178
  -- §7.22.3.3,7.22.3.5: free/realloc with non-matching/deallocated pointer
  | ub179a_nonMatchingAllocationFree
  | ub179b_deadAllocationFree
  | ub179c_nonMatchingAllocationRealloc
  | ub179d_deadAllocationRealloc
  -- §7.22.3.4: malloc'd object value used
  | ub180
  -- §7.22.3.5: realloc new bytes used
  | ub181
  -- §7.22.4.4,7.22.4.7: exit/quick_exit called more than once
  | ub182
  -- §7.22.4.4,7.22.4.7: longjmp from atexit/at_quick_exit handler
  | ub183
  -- §7.22.4.6,7.24.6.2: getenv/strerror string modified
  | ub184
  -- §7.22.4.7: Signal raised during quick_exit
  | ub185
  -- §7.22.4.8: system() causes UB
  | ub186
  -- §7.22.5: Search/sort with invalid pointer
  | ub187
  -- §7.22.5: Comparison function alters array or inconsistent
  | ub188
  -- §7.22.5.1: bsearch array not in order
  | ub189
  -- §7.22.7: Conversion state after LC_CTYPE change
  | ub190
  -- §7.24.1,7.29.4: String utility accesses beyond object
  | ub191
  -- §7.24.1,7.29.4: String utility with invalid pointer
  | ub192
  -- §7.24.4.5,7.27.3.5,7.29.4.4.4,7.29.5.1: Dest used after strxfrm/strftime too small
  | ub193
  -- §7.24.5.8,7.29.4.5.7: strtok/wcstok first arg null in first call
  | ub194
  -- §7.25: Type-generic macro arg type incompatible
  | ub195
  -- §7.25: Complex arg for non-complex generic
  | ub196
  -- §7.27.3.1: asctime broken-down time out of range
  | ub197
  -- §7.29.2.11: fwprintf %s arg not valid multibyte
  | ub198
  -- §7.29.4.5.7: wcstok ptr object changed
  | ub199
  -- §7.29.6: mbstate_t used inappropriately
  | ub200
  -- §7.30.1: wint_t arg not WEOF and not representable as wchar_t
  | ub201
  -- §7.30.2.2.1: iswctype with different LC_CTYPE
  | ub202
  -- §7.30.3.2.1: towctrans with different LC_CTYPE
  | ub203
  -- §6.7.10: _Static_assert expression not integer constant
  | ub204_illtypedStaticAssert
  -- §7.17.7.1: Invalid memory order for atomic store
  | ub205_atomicStoreMemorder
  -- §7.17.7.2: Invalid memory order for atomic load
  | ub206_atomicLoadMemorder
  -- §7.17.7.4: Invalid memory order for atomic compare_exchange
  | ub207_atomicCompareExchangeMemorder

  -- CERB extensions (undefined.lem:711-732)
  | ub_cerb001_integerToDeadPointer
  | ub_cerb002a_outOfBoundLoad
  | ub_cerb002b_outOfBoundStore
  | ub_cerb002c_outOfBoundFree
  | ub_cerb002d_outOfBoundRealloc
  | ub_cerb003_invalidFunctionPointer
  | ub_cerb004_unspecified (ctx : UnspecifiedUBContext)
  | ub_cerb005_freeNullptr

  -- CHERI-specific UBs (undefined.lem:722-726)
  | ub_cheri_invalidCap
  | ub_cheri_insufficientPermissions
  | ub_cheri_boundsViolation
  | ub_cheri_undefinedTag
  | ub_cheri_zeroLength

  deriving Repr, BEq, Inhabited

/-- Bimap entries matching ub_str_bimap in undefined.lem.
    Defined as data (not a pattern match) to avoid Lean heartbeat timeout
    on the 250+ entry string decision tree. -/
private def ubStringEntries : List (String × UndefinedBehavior) :=
  [ ("UB_unspecified_lvalue", .unspecifiedLvalue)
  , ("UB_std_omission_UB_OMIT_memcpy_non_object", .stdOmission .memcpyNonObject)
  , ("UB_std_omission_UB_OMIT_memcpy_out_of_bound", .stdOmission .memcpyOutOfBound)
  , ("UB001", .ub001)
  , ("UB002", .ub002)
  , ("UB003", .ub003)
  , ("UB004a_incorrect_main_return_type", .ub004a_incorrectMainReturnType)
  , ("UB004b_incorrect_main_argument1", .ub004b_incorrectMainArgument1)
  , ("UB004c_incorrect_main_argument2", .ub004c_incorrectMainArgument2)
  , ("UB004d_main_not_function", .ub004d_mainNotFunction)
  , ("UB005_data_race", .ub005_dataRace)
  , ("UB006", .ub006)
  , ("UB007", .ub007)
  , ("UB008_multiple_linkage", .ub008_multipleLinkage)
  , ("UB009_outside_lifetime", .ub009_outsideLifetime)
  , ("UB010_pointer_to_dead_object", .ub010_pointerToDeadObject)
  , ("UB011_use_indeterminate_automatic_object", .ub011_useIndeterminateAutomatic)
  , ("UB_modifying_temporary_lifetime", .ub_modifyingTemporaryLifetime)
  , ("UB012_lvalue_read_trap_representation", .ub012_lvalueReadTrapRepresentation)
  , ("UB013_lvalue_side_effect_trap_representation", .ub013_lvalueSideEffectTrap)
  , ("UB014_unsupported_negative_zero", .ub014_unsupportedNegativeZero)
  , ("UB015_incompatible_redeclaration", .ub015_incompatibleRedeclaration)
  , ("UB016", .ub016)
  , ("UB017_out_of_range_floating_integer_conversion", .ub017_outOfRangeFloatingIntConversion)
  , ("UB018", .ub018)
  , ("UB019_lvalue_not_an_object", .ub019_lvalueNotAnObject)
  , ("UB020_nonarray_incomplete_lvalue_conversion", .ub020_nonarrayIncompleteLvalueConversion)
  , ("UB021", .ub021)
  , ("UB022_register_array_decay", .ub022_registerArrayDecay)
  , ("UB023", .ub023)
  , ("UB024_out_of_range_pointer_to_integer_conversion", .ub024_outOfRangePointerToIntConversion)
  , ("UB025_misaligned_pointer_conversion", .ub025_misalignedPointerConversion)
  , ("UB026", .ub026)
  , ("UB027", .ub027)
  , ("UB028", .ub028)
  , ("UB029", .ub029)
  , ("UB030", .ub030)
  , ("UB031", .ub031)
  , ("UB032", .ub032)
  , ("UB033_modifying_string_literal", .ub033_modifyingStringLiteral)
  , ("UB034", .ub034)
  , ("UB035_unsequenced_race", .ub035_unsequencedRace)
  , ("UB036_exceptional_condition", .ub036_exceptionalCondition)
  , ("UB037_illtyped_load", .ub037_illtypedLoad)
  , ("UB038_number_of_args", .ub038_numberOfArgs)
  , ("UB039", .ub039)
  , ("UB040", .ub040)
  , ("UB041_function_not_compatible", .ub041_functionNotCompatible)
  , ("UB042_access_atomic_structUnion_member", .ub042_accessAtomicStructUnionMember)
  , ("UB043_indirection_invalid_value", .ub043_indirectionInvalidValue)
  , ("UB044", .ub044)
  , ("UB045a_division_by_zero", .ub045a_divisionByZero)
  , ("UB045b_modulo_by_zero", .ub045b_moduloByZero)
  , ("UB045c_quotient_not_representable", .ub045c_quotientNotRepresentable)
  , ("UB046_array_pointer_outside", .ub046_arrayPointerOutside)
  , ("UB047a_array_pointer_addition_beyond_indirection", .ub047a_arrayPointerAdditionBeyondIndirection)
  , ("UB047b_array_pointer_subtraction_beyond_indirection", .ub047b_arrayPointerSubtractionBeyondIndirection)
  , ("UB048_disjoint_array_pointers_subtraction", .ub048_disjointArrayPointersSubtraction)
  , ("UB049", .ub049)
  , ("UB050_pointers_subtraction_not_representable", .ub050_pointersSubtractionNotRepresentable)
  , ("UB051a_negative_shift", .ub051a_negativeShift)
  , ("UB51b_shift_too_large", .ub051b_shiftTooLarge)  -- Note: Cerberus typo "UB51b" (no 0)
  , ("UB052a_negative_left_shift", .ub052a_negativeLeftShift)
  , ("UB052b_non_representable_left_shift", .ub052b_nonRepresentableLeftShift)
  , ("UB053_distinct_aggregate_union_pointer_comparison", .ub053_distinctAggregateUnionPointerComparison)
  , ("UB054a_inexactly_overlapping_assignment", .ub054a_inexactlyOverlappingAssignment)
  , ("UB054b_incompatible_overlapping_assignment", .ub054b_incompatibleOverlappingAssignment)
  , ("UB055_invalid_integer_constant_expression", .ub055_invalidIntegerConstantExpression)
  , ("UB056", .ub056)
  , ("UB057", .ub057)
  , ("UB058", .ub058)
  , ("UB059_incomplete_no_linkage_identifier", .ub059_incompleteNoLinkageIdentifier)
  , ("UB060_block_scope_function_with_storage_class", .ub060_blockScopeFunctionWithStorageClass)
  , ("UB061_no_named_members", .ub061_noNamedMembers)
  , ("UB062", .ub062)
  , ("UB063", .ub063)
  , ("UB064_modifying_const", .ub064_modifyingConst)
  , ("UB065", .ub065)
  , ("UB066_qualified_function_specification", .ub066_qualifiedFunctionSpecification)
  , ("UB067", .ub067)
  , ("UB068", .ub068)
  , ("UB069", .ub069)
  , ("UB070_inline_not_defined", .ub070_inlineNotDefined)
  , ("UB071_noreturn", .ub071_noreturn)
  , ("UB072_incompatible_alignment_specifiers", .ub072_incompatibleAlignmentSpecifiers)
  , ("UB073", .ub073)
  , ("UB074", .ub074)
  , ("UB075", .ub075)
  , ("UB076", .ub076)
  , ("UB077", .ub077)
  , ("UB078_modified_void_parameter", .ub078_modifiedVoidParameter)
  , ("UB079", .ub079)
  , ("UB080", .ub080)
  , ("UB081_scalar_initializer_not_single_expression", .ub081_scalarInitializerNotSingleExpression)
  , ("UB082", .ub082)
  , ("UB083", .ub083)
  , ("UB084", .ub084)
  , ("UB085", .ub085)
  , ("UB086_incomplete_adjusted_parameter", .ub086_incompleteAdjustedParameter)
  , ("UB087", .ub087)
  , ("UB088_reached_end_of_function", .ub088_endOfNonVoidFunction)
  , ("UB089_tentative_definition_internal_linkage", .ub089_tentativeDefinitionInternalLinkage)
  , ("UB090", .ub090)
  , ("UB091", .ub091)
  , ("UB092", .ub092)
  , ("UB093", .ub093)
  , ("UB094", .ub094)
  , ("UB095", .ub095)
  , ("UB096", .ub096)
  , ("UB097", .ub097)
  , ("UB098", .ub098)
  , ("UB099", .ub099)
  , ("UB100", .ub100)
  , ("UB101", .ub101)
  , ("UB102", .ub102)
  , ("UB103", .ub103)
  , ("UB104", .ub104)
  , ("UB105", .ub105)
  , ("UB106", .ub106)
  , ("UB107", .ub107)
  , ("UB108", .ub108)
  , ("UB109", .ub109)
  , ("UB110", .ub110)
  , ("UB111_illtyped_assert", .ub111_illtypedAssert)
  , ("UB112", .ub112)
  , ("UB113", .ub113)
  , ("UB114", .ub114)
  , ("UB115", .ub115)
  , ("UB116", .ub116)
  , ("UB117", .ub117)
  , ("UB118", .ub118)
  , ("UB119", .ub119)
  , ("UB120", .ub120)
  , ("UB121", .ub121)
  , ("UB122", .ub122)
  , ("UB123", .ub123)
  , ("UB124", .ub124)
  , ("UB125", .ub125)
  , ("UB126", .ub126)
  , ("UB127", .ub127)
  , ("UB128", .ub128)
  , ("UB129", .ub129)
  , ("UB130", .ub130)
  , ("UB131", .ub131)
  , ("UB132", .ub132)
  , ("UB133", .ub133)
  , ("UB134", .ub134)
  , ("UB135", .ub135)
  , ("UB136", .ub136)
  , ("UB137", .ub137)
  , ("UB138", .ub138)
  , ("UB139", .ub139)
  , ("UB140", .ub140)
  , ("UB141", .ub141)
  , ("UB142", .ub142)
  , ("UB143", .ub143)
  , ("UB144", .ub144)
  , ("UB145", .ub145)
  , ("UB146", .ub146)
  , ("UB147", .ub147)
  , ("UB148", .ub148)
  , ("UB149", .ub149)
  , ("UB150", .ub150)
  , ("UB151", .ub151)
  , ("UB152", .ub152)
  , ("UB153a_insufficient_arguments_for_format", .ub153a_insufficientArgumentsForFormat)
  , ("UB153b_illtyped_argument_for_format", .ub153b_illtypedArgumentForFormat)
  , ("UB154", .ub154)
  , ("UB155", .ub155)
  , ("UB156", .ub156)
  , ("UB157", .ub157)
  , ("UB158_invalid_length_modifier", .ub158_invalidLengthModifier)
  , ("UB159", .ub159)
  , ("UB160", .ub160)
  , ("UB161", .ub161)
  , ("UB162", .ub162)
  , ("UB163", .ub163)
  , ("UB164", .ub164)
  , ("UB165", .ub165)
  , ("UB166", .ub166)
  , ("UB167", .ub167)
  , ("UB168", .ub168)
  , ("UB169", .ub169)
  , ("UB170", .ub170)
  , ("UB171", .ub171)
  , ("UB172", .ub172)
  , ("UB173", .ub173)
  , ("UB174", .ub174)
  , ("UB175", .ub175)
  , ("UB176", .ub176)
  , ("UB177", .ub177)
  , ("UB178", .ub178)
  , ("UB179a_non_matching_allocation_free", .ub179a_nonMatchingAllocationFree)
  , ("UB179b_dead_allocation_free", .ub179b_deadAllocationFree)
  , ("UB179c_non_matching_allocation_realloc", .ub179c_nonMatchingAllocationRealloc)
  , ("UB179d_dead_allocation_realloc", .ub179d_deadAllocationRealloc)
  , ("UB180", .ub180)
  , ("UB181", .ub181)
  , ("UB182", .ub182)
  , ("UB183", .ub183)
  , ("UB184", .ub184)
  , ("UB185", .ub185)
  , ("UB186", .ub186)
  , ("UB187", .ub187)
  , ("UB188", .ub188)
  , ("UB189", .ub189)
  , ("UB190", .ub190)
  , ("UB191", .ub191)
  , ("UB192", .ub192)
  , ("UB193", .ub193)
  , ("UB194", .ub194)
  , ("UB195", .ub195)
  , ("UB196", .ub196)
  , ("UB197", .ub197)
  , ("UB198", .ub198)
  , ("UB199", .ub199)
  , ("UB200", .ub200)
  , ("UB201", .ub201)
  , ("UB202", .ub202)
  , ("UB203", .ub203)
  , ("UB204_illtyped_Static_assert", .ub204_illtypedStaticAssert)
  , ("UB205_atomic_store_memorder", .ub205_atomicStoreMemorder)
  , ("UB206_atomic_load_memorder", .ub206_atomicLoadMemorder)
  , ("UB207_atomic_compare_exchange_memorder", .ub207_atomicCompareExchangeMemorder)
  , ("UB_CERB001_integer_to_dead_pointer", .ub_cerb001_integerToDeadPointer)
  , ("UB_CERB002a_out_of_bound_load", .ub_cerb002a_outOfBoundLoad)
  , ("UB_CERB002b_out_of_bound_store", .ub_cerb002b_outOfBoundStore)
  , ("UB_CERB002c_out_of_bound_free", .ub_cerb002c_outOfBoundFree)
  , ("UB_CERB002d_out_of_bound_realloc", .ub_cerb002d_outOfBoundRealloc)
  , ("UB_CERB003_invalid_function_pointer", .ub_cerb003_invalidFunctionPointer)
  , ("UB_CERB004_unspecified__equality_ptr_vs_NULL", .ub_cerb004_unspecified .equalityPtrVsNull)
  , ("UB_CERB004_unspecified__equality_both_arith_or_ptr", .ub_cerb004_unspecified .equalityBothArithOrPtr)
  , ("UB_CERB004_unspecified__pointer_add", .ub_cerb004_unspecified .pointerAdd)
  , ("UB_CERB004_unspecified__pointer_sub", .ub_cerb004_unspecified .pointerSub)
  , ("UB_CERB004_unspecified__conditional", .ub_cerb004_unspecified .conditional)
  , ("UB_CERB004_unspecified__copy_alloc_id", .ub_cerb004_unspecified .copyAllocId)
  , ("UB_CERB004_unspecified__rvalue_memberof", .ub_cerb004_unspecified .rvalueMemberof)
  , ("UB_CERB004_unspecified__memberofptr", .ub_cerb004_unspecified .memberofptr)
  , ("UB_CERB004_unspecified__do", .ub_cerb004_unspecified .do_)
  , ("UB_CERB005_free_nullptr", .ub_cerb005_freeNullptr)
  , ("UB_CHERI_InvalidCap", .ub_cheri_invalidCap)
  , ("UB_CHERI_InsufficientPermissions", .ub_cheri_insufficientPermissions)
  , ("UB_CHERI_BoundsViolation", .ub_cheri_boundsViolation)
  , ("UB_CHERI_UndefinedTag", .ub_cheri_undefinedTag)
  , ("UB_CHERI_ZeroLength", .ub_cheri_zeroLength)
  ]

/-- HashMap for O(1) string-to-UB lookup, built from ubStringEntries.
    Mirrors Cerberus's ub_str_bimap approach. -/
private def ubFromStringMap : Std.HashMap String UndefinedBehavior :=
  .ofList ubStringEntries

/-- Parse a UB code string (from Cerberus JSON/bimap) into an UndefinedBehavior.
    Uses HashMap lookup matching ub_str_bimap in undefined.lem.
    Errors on unrecognized strings (fail, never guess). -/
def UndefinedBehavior.fromString (s : String) : Except String UndefinedBehavior :=
  match ubFromStringMap[s]? with
  | some ub => .ok ub
  | none =>
    if s.startsWith "DUMMY(" then .ok (.dummy (s.drop 6 |>.dropRight 1))
    else if s.startsWith "Invalid_format[" then .ok (.invalidFormat (s.drop 15 |>.dropRight 1))
    else .error s!"unknown UB code: {s}"

/-- Convert an UndefinedBehavior to its canonical Cerberus string.
    Matches the ub_str_bimap in undefined.lem. -/
def UndefinedBehavior.toString : UndefinedBehavior → String
  | .dummy msg => s!"DUMMY({msg})"
  | .unspecifiedLvalue => "UB_unspecified_lvalue"
  | .stdOmission .memcpyNonObject => "UB_std_omission_UB_OMIT_memcpy_non_object"
  | .stdOmission .memcpyOutOfBound => "UB_std_omission_UB_OMIT_memcpy_out_of_bound"
  | .ub001 => "UB001"
  | .ub002 => "UB002"
  | .ub003 => "UB003"
  | .ub004a_incorrectMainReturnType => "UB004a_incorrect_main_return_type"
  | .ub004b_incorrectMainArgument1 => "UB004b_incorrect_main_argument1"
  | .ub004c_incorrectMainArgument2 => "UB004c_incorrect_main_argument2"
  | .ub004d_mainNotFunction => "UB004d_main_not_function"
  | .ub005_dataRace => "UB005_data_race"
  | .ub006 => "UB006"
  | .ub007 => "UB007"
  | .ub008_multipleLinkage => "UB008_multiple_linkage"
  | .ub009_outsideLifetime => "UB009_outside_lifetime"
  | .ub010_pointerToDeadObject => "UB010_pointer_to_dead_object"
  | .ub011_useIndeterminateAutomatic => "UB011_use_indeterminate_automatic_object"
  | .ub_modifyingTemporaryLifetime => "UB_modifying_temporary_lifetime"
  | .ub012_lvalueReadTrapRepresentation => "UB012_lvalue_read_trap_representation"
  | .ub013_lvalueSideEffectTrap => "UB013_lvalue_side_effect_trap_representation"
  | .ub014_unsupportedNegativeZero => "UB014_unsupported_negative_zero"
  | .ub015_incompatibleRedeclaration => "UB015_incompatible_redeclaration"
  | .ub016 => "UB016"
  | .ub017_outOfRangeFloatingIntConversion => "UB017_out_of_range_floating_integer_conversion"
  | .ub018 => "UB018"
  | .ub019_lvalueNotAnObject => "UB019_lvalue_not_an_object"
  | .ub020_nonarrayIncompleteLvalueConversion => "UB020_nonarray_incomplete_lvalue_conversion"
  | .ub021 => "UB021"
  | .ub022_registerArrayDecay => "UB022_register_array_decay"
  | .ub023 => "UB023"
  | .ub024_outOfRangePointerToIntConversion => "UB024_out_of_range_pointer_to_integer_conversion"
  | .ub025_misalignedPointerConversion => "UB025_misaligned_pointer_conversion"
  | .ub026 => "UB026"
  | .ub027 => "UB027"
  | .ub028 => "UB028"
  | .ub029 => "UB029"
  | .ub030 => "UB030"
  | .ub031 => "UB031"
  | .ub032 => "UB032"
  | .ub033_modifyingStringLiteral => "UB033_modifying_string_literal"
  | .ub034 => "UB034"
  | .ub035_unsequencedRace => "UB035_unsequenced_race"
  | .ub036_exceptionalCondition => "UB036_exceptional_condition"
  | .ub037_illtypedLoad => "UB037_illtyped_load"
  | .ub038_numberOfArgs => "UB038_number_of_args"
  | .ub039 => "UB039"
  | .ub040 => "UB040"
  | .ub041_functionNotCompatible => "UB041_function_not_compatible"
  | .ub042_accessAtomicStructUnionMember => "UB042_access_atomic_structUnion_member"
  | .ub043_indirectionInvalidValue => "UB043_indirection_invalid_value"
  | .ub044 => "UB044"
  | .ub045a_divisionByZero => "UB045a_division_by_zero"
  | .ub045b_moduloByZero => "UB045b_modulo_by_zero"
  | .ub045c_quotientNotRepresentable => "UB045c_quotient_not_representable"
  | .ub046_arrayPointerOutside => "UB046_array_pointer_outside"
  | .ub047a_arrayPointerAdditionBeyondIndirection => "UB047a_array_pointer_addition_beyond_indirection"
  | .ub047b_arrayPointerSubtractionBeyondIndirection => "UB047b_array_pointer_subtraction_beyond_indirection"
  | .ub048_disjointArrayPointersSubtraction => "UB048_disjoint_array_pointers_subtraction"
  | .ub049 => "UB049"
  | .ub050_pointersSubtractionNotRepresentable => "UB050_pointers_subtraction_not_representable"
  | .ub051a_negativeShift => "UB051a_negative_shift"
  | .ub051b_shiftTooLarge => "UB51b_shift_too_large"  -- Note: matches Cerberus typo
  | .ub052a_negativeLeftShift => "UB052a_negative_left_shift"
  | .ub052b_nonRepresentableLeftShift => "UB052b_non_representable_left_shift"
  | .ub053_distinctAggregateUnionPointerComparison => "UB053_distinct_aggregate_union_pointer_comparison"
  | .ub054a_inexactlyOverlappingAssignment => "UB054a_inexactly_overlapping_assignment"
  | .ub054b_incompatibleOverlappingAssignment => "UB054b_incompatible_overlapping_assignment"
  | .ub055_invalidIntegerConstantExpression => "UB055_invalid_integer_constant_expression"
  | .ub056 => "UB056"
  | .ub057 => "UB057"
  | .ub058 => "UB058"
  | .ub059_incompleteNoLinkageIdentifier => "UB059_incomplete_no_linkage_identifier"
  | .ub060_blockScopeFunctionWithStorageClass => "UB060_block_scope_function_with_storage_class"
  | .ub061_noNamedMembers => "UB061_no_named_members"
  | .ub062 => "UB062"
  | .ub063 => "UB063"
  | .ub064_modifyingConst => "UB064_modifying_const"
  | .ub065 => "UB065"
  | .ub066_qualifiedFunctionSpecification => "UB066_qualified_function_specification"
  | .ub067 => "UB067"
  | .ub068 => "UB068"
  | .ub069 => "UB069"
  | .ub070_inlineNotDefined => "UB070_inline_not_defined"
  | .ub071_noreturn => "UB071_noreturn"
  | .ub072_incompatibleAlignmentSpecifiers => "UB072_incompatible_alignment_specifiers"
  | .ub073 => "UB073"
  | .ub074 => "UB074"
  | .ub075 => "UB075"
  | .ub076 => "UB076"
  | .ub077 => "UB077"
  | .ub078_modifiedVoidParameter => "UB078_modified_void_parameter"
  | .ub079 => "UB079"
  | .ub080 => "UB080"
  | .ub081_scalarInitializerNotSingleExpression => "UB081_scalar_initializer_not_single_expression"
  | .ub082 => "UB082"
  | .ub083 => "UB083"
  | .ub084 => "UB084"
  | .ub085 => "UB085"
  | .ub086_incompleteAdjustedParameter => "UB086_incomplete_adjusted_parameter"
  | .ub087 => "UB087"
  | .ub088_endOfNonVoidFunction => "UB088_reached_end_of_function"
  | .ub089_tentativeDefinitionInternalLinkage => "UB089_tentative_definition_internal_linkage"
  | .ub090 => "UB090"
  | .ub091 => "UB091"
  | .ub092 => "UB092"
  | .ub093 => "UB093"
  | .ub094 => "UB094"
  | .ub095 => "UB095"
  | .ub096 => "UB096"
  | .ub097 => "UB097"
  | .ub098 => "UB098"
  | .ub099 => "UB099"
  | .ub100 => "UB100"
  | .ub101 => "UB101"
  | .ub102 => "UB102"
  | .ub103 => "UB103"
  | .ub104 => "UB104"
  | .ub105 => "UB105"
  | .ub106 => "UB106"
  | .ub107 => "UB107"
  | .ub108 => "UB108"
  | .ub109 => "UB109"
  | .ub110 => "UB110"
  | .ub111_illtypedAssert => "UB111_illtyped_assert"
  | .ub112 => "UB112"
  | .ub113 => "UB113"
  | .ub114 => "UB114"
  | .ub115 => "UB115"
  | .ub116 => "UB116"
  | .ub117 => "UB117"
  | .ub118 => "UB118"
  | .ub119 => "UB119"
  | .ub120 => "UB120"
  | .ub121 => "UB121"
  | .ub122 => "UB122"
  | .ub123 => "UB123"
  | .ub124 => "UB124"
  | .ub125 => "UB125"
  | .ub126 => "UB126"
  | .ub127 => "UB127"
  | .ub128 => "UB128"
  | .ub129 => "UB129"
  | .ub130 => "UB130"
  | .ub131 => "UB131"
  | .ub132 => "UB132"
  | .ub133 => "UB133"
  | .ub134 => "UB134"
  | .ub135 => "UB135"
  | .ub136 => "UB136"
  | .ub137 => "UB137"
  | .ub138 => "UB138"
  | .ub139 => "UB139"
  | .ub140 => "UB140"
  | .ub141 => "UB141"
  | .ub142 => "UB142"
  | .ub143 => "UB143"
  | .ub144 => "UB144"
  | .ub145 => "UB145"
  | .ub146 => "UB146"
  | .ub147 => "UB147"
  | .ub148 => "UB148"
  | .ub149 => "UB149"
  | .ub150 => "UB150"
  | .ub151 => "UB151"
  | .ub152 => "UB152"
  | .ub153a_insufficientArgumentsForFormat => "UB153a_insufficient_arguments_for_format"
  | .ub153b_illtypedArgumentForFormat => "UB153b_illtyped_argument_for_format"
  | .invalidFormat fmt => s!"Invalid_format[{fmt}]"
  | .ub154 => "UB154"
  | .ub155 => "UB155"
  | .ub156 => "UB156"
  | .ub157 => "UB157"
  | .ub158_invalidLengthModifier => "UB158_invalid_length_modifier"
  | .ub159 => "UB159"
  | .ub160 => "UB160"
  | .ub161 => "UB161"
  | .ub162 => "UB162"
  | .ub163 => "UB163"
  | .ub164 => "UB164"
  | .ub165 => "UB165"
  | .ub166 => "UB166"
  | .ub167 => "UB167"
  | .ub168 => "UB168"
  | .ub169 => "UB169"
  | .ub170 => "UB170"
  | .ub171 => "UB171"
  | .ub172 => "UB172"
  | .ub173 => "UB173"
  | .ub174 => "UB174"
  | .ub175 => "UB175"
  | .ub176 => "UB176"
  | .ub177 => "UB177"
  | .ub178 => "UB178"
  | .ub179a_nonMatchingAllocationFree => "UB179a_non_matching_allocation_free"
  | .ub179b_deadAllocationFree => "UB179b_dead_allocation_free"
  | .ub179c_nonMatchingAllocationRealloc => "UB179c_non_matching_allocation_realloc"
  | .ub179d_deadAllocationRealloc => "UB179d_dead_allocation_realloc"
  | .ub180 => "UB180"
  | .ub181 => "UB181"
  | .ub182 => "UB182"
  | .ub183 => "UB183"
  | .ub184 => "UB184"
  | .ub185 => "UB185"
  | .ub186 => "UB186"
  | .ub187 => "UB187"
  | .ub188 => "UB188"
  | .ub189 => "UB189"
  | .ub190 => "UB190"
  | .ub191 => "UB191"
  | .ub192 => "UB192"
  | .ub193 => "UB193"
  | .ub194 => "UB194"
  | .ub195 => "UB195"
  | .ub196 => "UB196"
  | .ub197 => "UB197"
  | .ub198 => "UB198"
  | .ub199 => "UB199"
  | .ub200 => "UB200"
  | .ub201 => "UB201"
  | .ub202 => "UB202"
  | .ub203 => "UB203"
  | .ub204_illtypedStaticAssert => "UB204_illtyped_Static_assert"
  | .ub205_atomicStoreMemorder => "UB205_atomic_store_memorder"
  | .ub206_atomicLoadMemorder => "UB206_atomic_load_memorder"
  | .ub207_atomicCompareExchangeMemorder => "UB207_atomic_compare_exchange_memorder"
  | .ub_cerb001_integerToDeadPointer => "UB_CERB001_integer_to_dead_pointer"
  | .ub_cerb002a_outOfBoundLoad => "UB_CERB002a_out_of_bound_load"
  | .ub_cerb002b_outOfBoundStore => "UB_CERB002b_out_of_bound_store"
  | .ub_cerb002c_outOfBoundFree => "UB_CERB002c_out_of_bound_free"
  | .ub_cerb002d_outOfBoundRealloc => "UB_CERB002d_out_of_bound_realloc"
  | .ub_cerb003_invalidFunctionPointer => "UB_CERB003_invalid_function_pointer"
  | .ub_cerb004_unspecified .equalityPtrVsNull => "UB_CERB004_unspecified__equality_ptr_vs_NULL"
  | .ub_cerb004_unspecified .equalityBothArithOrPtr => "UB_CERB004_unspecified__equality_both_arith_or_ptr"
  | .ub_cerb004_unspecified .pointerAdd => "UB_CERB004_unspecified__pointer_add"
  | .ub_cerb004_unspecified .pointerSub => "UB_CERB004_unspecified__pointer_sub"
  | .ub_cerb004_unspecified .conditional => "UB_CERB004_unspecified__conditional"
  | .ub_cerb004_unspecified .copyAllocId => "UB_CERB004_unspecified__copy_alloc_id"
  | .ub_cerb004_unspecified .rvalueMemberof => "UB_CERB004_unspecified__rvalue_memberof"
  | .ub_cerb004_unspecified .memberofptr => "UB_CERB004_unspecified__memberofptr"
  | .ub_cerb004_unspecified .do_ => "UB_CERB004_unspecified__do"
  | .ub_cerb005_freeNullptr => "UB_CERB005_free_nullptr"
  | .ub_cheri_invalidCap => "UB_CHERI_InvalidCap"
  | .ub_cheri_insufficientPermissions => "UB_CHERI_InsufficientPermissions"
  | .ub_cheri_boundsViolation => "UB_CHERI_BoundsViolation"
  | .ub_cheri_undefinedTag => "UB_CHERI_UndefinedTag"
  | .ub_cheri_zeroLength => "UB_CHERI_ZeroLength"

instance : ToString UndefinedBehavior where
  toString := UndefinedBehavior.toString

end CerbLean.Core
