# Pretty-Printer Discrepancies: Lean vs Cerberus

This document categorizes the differences between the Lean pretty-printer output and the Cerberus pretty-printer output (in compact mode). These were identified by running `scripts/test_pp.sh` on 243 test files, of which 121 succeeded in Cerberus and 59 had mismatches.

Current match rate: **51%** (62/121)

---

## Fix Checklist

- [ ] **Category 1**: Empty section headers - always output `-- Aggregates` and `-- Fun map`
- [ ] **Category 2**: Library globals - filter out `__stdout`, `__stderr`, `__stdin`
- [ ] **Category 3**: ccall argument order - swap to `ccall(type, pe, args...)`
- [ ] **Category 4**: Function argument naming - preserve original symbol names
- [ ] **Category 5**: Integer types - use `signed short`/`signed long` not `short`/`long`
- [ ] **Category 6**: ichar types - use `ichar` for Ichar basic type
- [ ] **Category 7**: Struct symbol names - use symbol ID (e.g., `T_502`) not tag name
- [ ] **Category 8**: Atomic spacing - add space after `_Atomic`
- [ ] **Category 9**: Function declarations - omit return type for declarations without body
- [ ] **Category 10**: Struct order - match Cerberus ordering
- [ ] **Category 11**: store_lock - output `store_lock` when lock flag is set
- [ ] **Category 12**: const qualifier - strip const in certain type contexts
- [ ] **Category 13**: Expression parens - add parens around `Ivmax(...) + 1`

---

## Category 1: Section Headers for Empty Sections

**Impact**: High (affects many files)

**Issue**: Cerberus outputs section headers even when sections are empty, Lean omits them.

**Examples**:
```
Cerberus: -- Aggregates       -- Fun map proc main ...
Lean:     proc main ...

Cerberus: -- Aggregates -- Globals glob glob1 ...
Lean:     -- Globals glob glob1 ...
```

**Affected files**: 0009-cond-pointer, 0058-pointer_zero_init, 0338-cast-pointer-to-_Bool, 0341-misaligned_pointer, and others

**Fix needed**: In Lean pretty-printer, always output `-- Aggregates` and `-- Fun map` headers, even when empty. Cerberus uses multiple spaces as separators between empty sections.

---

## Category 2: Library Globals (__stdout, __stderr, __stdin)

**Impact**: High (affects many files)

**Issue**: Lean outputs libc globals (`__stdout`, `__stderr`, `__stdin`) that Cerberus omits.

**Examples**:
```
Cerberus: -- Globals glob i: pointer ...
Lean:     -- Globals glob __stdout: pointer [ail_ctype = 'struct _IO_FILE*']
          glob __stderr: pointer [ail_ctype = 'struct _IO_FILE*']
          glob __stdin: pointer [ail_ctype = 'struct _IO_FILE*']
          glob i: pointer ...
```

**Affected files**: 0057-std_footnote_118, 0067-band1, 0068-bor1, 0072-example03, 0073-example03, 0077-register_arg, 0082-OK1, 0083-array_initializers, 0105-incr, 0109-promotion_lt, 0112-call_in_label, 0116-enum_constants, 0119-block_array_init_rec, 0126-duff_device

**Fix needed**: Either filter out these library globals in Lean, or determine how Cerberus filters them (possibly by symbol name starting with `__`).

---

## Category 3: ccall Argument Order

**Impact**: High (affects all function calls)

**Issue**: The arguments to `ccall` are in different order.

**Examples**:
```
Cerberus: ccall('signed int (*) (void)', a_511)
Lean:     ccall(a_511, 'signed int (*) (void)')

Cerberus: ccall('void (*) (void)', a_508)
Lean:     ccall(a_508, 'void (*) (void)')
```

**Affected files**: 0045-global_postinit, 0049-void_return_empty, 0050-void_return_arith, 0051-global_non_startup, 0061-cond_call_e, 0062-cond_call_e2, 0074-fun_returns, 0129-function-pointer-wrong-args, 0307-incr_atomic, 0309-comma_void_operand

**Fix needed**: Change Lean pretty-printer to output `ccall(type, pe, args...)` instead of `ccall(pe, type, args...)`.

---

## Category 4: Function Call Argument Naming

**Impact**: Medium (affects files with function calls with arguments)

**Issue**: Lean names function call argument temporaries as `arg_0`, `arg_1`, etc., while Cerberus uses the original symbol names like `a_519`.

**Examples**:
```
Cerberus: let strong a_519: pointer = let a_521: ctype = ...
Lean:     let strong arg_0: pointer = let a_521: ctype = ...
```

**Affected files**: 0021-fact, 0030-call_arith, 0053-recursive_factorial5, 0054-while_factorial5, 0076-odd_even, 0127-function-pointer, 0128-function-pointer-void-cast, 0310-funcall_sequencing

**Fix needed**: Preserve original symbol names for ccall argument bindings instead of renaming to `arg_N`.

---

## Category 5: Integer Type Printing (signed short/long)

**Impact**: Medium (affects files using short/long types)

**Issue**: Cerberus prints `'signed short'` and `'signed long'`, while Lean prints `'short'` and `'long'`.

**Examples**:
```
Cerberus: create(Ivalignof('signed short'), 'signed short')
Lean:     create(Ivalignof('short'), 'short')

Cerberus: conv_int('signed long', a_506)
Lean:     conv_int('long', a_506)
```

**Affected files**: 0056-unary_plus, 0108-shifts, 0308-struct_global_with_dep, 0333-shifts_non_representable, 0334-non_decimal_long_int_constants, 0335-non_decimal_unsigned_long_int_constants

**Fix needed**: In Ctype pretty-printing, use `signed short` instead of `short` and `signed long` instead of `long`.

---

## Category 6: Integer Type Printing (signed/unsigned ichar)

**Impact**: Low (affects files using ichar types)

**Issue**: Cerberus prints `'signed ichar'` and `'unsigned ichar'`, while Lean prints `'signed char'` and `'unsigned char'`.

**Examples**:
```
Cerberus: kill('unsigned ichar', x)
Lean:     kill('unsigned char', x)

Cerberus: Unspecified('signed ichar')
Lean:     Unspecified('signed char')
```

**Affected files**: 0019-arith_promotion, 0122-incr_overflow, 0123-decr_underflow

**Fix needed**: In Ctype pretty-printing, use `ichar` instead of `char` for the `Ichar` basic type. Note: This appears to be a distinction between the `Ichar` type and actual `char`.

---

## Category 7: Struct Type Printing (symbol vs tag name)

**Impact**: Medium (affects files with struct types)

**Issue**: In `loaded struct` types, Cerberus uses the symbol number (`T_502`), while Lean uses the tag name (`T`).

**Examples**:
```
Cerberus: let strong a_540: loaded struct T_502 = ...
Lean:     let strong a_540: loaded struct T = ...

Cerberus: loaded struct s_502 = ...
Lean:     loaded struct s = ...
```

**Affected files**: 0317-compound-literal-lifetime, 0329-rvalue-temporary-lifetime, 0331-modifying-rvalue-temporary-lifetime, 0332-rvalue-temporary-lifetime-pointer-zap

**Fix needed**: In core_base_type printing for `BTy_storable` with struct type, use the symbol identifier (e.g., `a_502`) instead of just the tag name.

---

## Category 8: Atomic Type Spacing

**Impact**: Low (affects files using _Atomic)

**Issue**: Cerberus prints `_Atomic (T)` with a space, Lean prints `_Atomic(T)` without a space.

**Examples**:
```
Cerberus: ail_ctype = '_Atomic (signed int)']
Lean:     ail_ctype = '_Atomic(signed int)']

Cerberus: Unspecified('_Atomic (struct T)')
Lean:     Unspecified('_Atomic(struct T)')
```

**Affected files**: 0297-atomic_memberof, 0298-atomic_memberofptr, 0324-atomics

**Fix needed**: Add space after `_Atomic` in Ctype pretty-printing.

---

## Category 9: Function Declaration Format

**Impact**: Low (affects files with function declarations)

**Issue**: For function declarations (without body), Cerberus omits the return type annotation, Lean includes it.

**Examples**:
```
Cerberus: proc f ()
Lean:     proc f (): eff loaded integer

Cerberus: proc printf (pointer)
Lean:     proc printf (pointer): eff loaded integer
```

**Affected files**: 0077-register_arg, 0101-sym_cfunction, 0328-indeterminate_block_declaration

**Fix needed**: When printing function declarations (Proc where body is empty/unit), omit the return type annotation.

---

## Category 10: Struct Definition Order

**Impact**: Low (affects files with multiple structs)

**Issue**: The order of struct definitions differs between Cerberus and Lean.

**Examples**:
```
Cerberus: def struct T1 := ... def struct T2 := ... def struct __cerbty_unnamed_tag_504 := ...
Lean:     def struct T1 := ... def struct __cerbty_unnamed_tag_504 := ... def struct T2 := ...
```

**Affected files**: 0042-struct_namespace

**Fix needed**: Ensure struct definitions are printed in the same order as Cerberus (likely declaration order in the source file, or sorted by symbol ID).

---

## Category 11: store_lock vs store

**Impact**: Low (affects const globals)

**Issue**: Cerberus uses `store_lock` for const globals, Lean uses `store`.

**Examples**:
```
Cerberus: store_lock('signed int', a_530, ...)
Lean:     store('signed int', a_530, ...)
```

**Affected files**: 0295-global_const_int, 0296-global_const_array

**Fix needed**: Check if the memory action is `Store` with a lock flag, and output `store_lock` instead of `store` when appropriate.

---

## Category 12: Const Qualifier in Types

**Impact**: Low (affects files with const pointers)

**Issue**: Cerberus drops `const` from pointer types, Lean preserves it.

**Examples**:
```
Cerberus: kill('signed int*', q)
Lean:     kill('const signed int*', q)
```

**Affected files**: 0299-qualified_ptrdiff

**Fix needed**: Review how qualifiers are printed in Ctype; may need to strip `const` in certain contexts.

---

## Category 13: Parentheses in Expressions

**Impact**: Very Low (affects edge cases)

**Issue**: Different parenthesization in some expressions.

**Examples**:
```
Cerberus: rem_t (Ivmax('unsigned int') + 1)
Lean:     rem_t Ivmax('unsigned int') + 1
```

**Affected files**: 0340-shl_promotion_to_signed

**Fix needed**: Review operator precedence and add parentheses where Cerberus does.

---

## Priority Order for Fixes

1. **Category 1 (Section Headers)** - Simple fix, high impact
2. **Category 3 (ccall Order)** - Simple fix, high impact
3. **Category 2 (Library Globals)** - Medium fix, high impact (need to investigate Cerberus filtering)
4. **Category 5 (signed short/long)** - Simple fix, medium impact
5. **Category 4 (Argument Naming)** - Medium fix, medium impact
6. **Category 7 (Struct Symbol Names)** - Simple fix, medium impact
7. **Categories 6, 8, 9, 10, 11, 12, 13** - Low priority, can be done incrementally

---

## Notes

- Test run: 243 files attempted, 121 Cerberus succeeded, 62 matched, 59 mismatched
- Cerberus compact mode (`--pp_core_compact`) is used for comparison
- The Lean comparison tool ignores whitespace differences
