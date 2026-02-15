# Coverage Test Suite (`tests/coverage/`)

Created: 2026-02-15

## Context

We have Cerberus OCaml coverage instrumentation working (bisect_ppx). Current coverage from our existing test suites (260 tests):

| Key file | Coverage | Expressions |
|----------|----------|-------------|
| `impl_mem.ml` | **38.15%** | 787/2063 |
| `core_eval.ml` | **51.84%** | 409/789 |
| `core_reduction.ml` | **58.88%** | 504/856 |
| **Project total** | **29.60%** | 12,559/42,432 |

Goal: write targeted C programs that exercise uncovered Cerberus code paths. We only care about running these through **Cerberus** (`--exec`) — CerbLean is not involved. The point is to find bugs by covering more of the Cerberus semantics we'll eventually need to mirror.

**Bug filing**: If we discover bugs in Cerberus itself (crashes, incorrect results, unexpected UB detection), that's valuable — we'll file those upstream at https://github.com/rems-project/cerberus/issues.

## Approach

Simple: each test is a C file. We run the instrumented Cerberus binary on each one (`--exec --batch`). Some tests produce defined results, some trigger UB — we don't care about matching, only that Cerberus executes the relevant code paths.

The coverage script (`scripts/test_coverage.sh`) runs the coverage tests directly through the instrumented Cerberus binary. Non-libc tests use `--nolibc`, libc tests don't.

## Directory Structure

```
tests/coverage/
├── mem/          # Memory model operations (impl_mem.ml)
├── conv/         # Type conversions (core_eval.ml PEconv_int, PEwrapI)
├── ptr/          # Pointer operations (impl_mem.ml + core_eval.ml)
├── ctrl/         # Control flow patterns (core_reduction.ml)
├── expr/         # Expression evaluation edge cases (core_eval.ml)
├── struct/       # Struct/union/compound operations
└── libc/         # Tests requiring libc (malloc, free, memcpy, etc.)
```

Naming: `category-NNN-description.c` (matching `tests/debug/` convention).

## Test Categories

### 1. `mem/` — Memory Model (target: impl_mem.ml)

| Test | Cerberus path exercised |
|------|------------------------|
| `mem-001-store-load-char.c` | Byte-level store/load |
| `mem-002-store-load-short.c` | 2-byte store/load, endianness handling |
| `mem-003-type-pun-char.c` | Read int via `char*` (well-defined), byte extraction |
| `mem-004-type-pun-write.c` | Write bytes via `char*` then read as int |
| `mem-005-readonly-const.c` | Write to const — exercises store read-only check |
| `mem-006-uninitialized-read.c` | Read uninitialized local — exercises load uninit check |
| `mem-007-zero-size-array.c` | Zero-length allocation edge case |
| `mem-008-large-struct.c` | Struct with many members, sizeof/layout calculations |
| `mem-009-packed-access.c` | Access struct members at various alignments |
| `mem-010-flexible-array.c` | Struct with flexible array member |

### 2. `conv/` — Type Conversions (target: core_eval.ml PEconv_int/PEwrapI)

| Test | Cerberus path exercised |
|------|------------------------|
| `conv-001-signed-to-unsigned.c` | Negative int → unsigned int (value wrapping) |
| `conv-002-unsigned-to-signed.c` | Large unsigned → signed (impl-defined) |
| `conv-003-narrow-int.c` | int → char (truncation) |
| `conv-004-widen-char.c` | signed char → int (sign extension) |
| `conv-005-unsigned-char-widen.c` | unsigned char → int (zero extension) |
| `conv-006-long-to-int.c` | long → int (narrowing) |
| `conv-007-int-to-long.c` | int → long (widening, signed) |
| `conv-008-bool-from-int.c` | int → _Bool (zero/nonzero) |
| `conv-009-bool-from-ptr.c` | pointer → _Bool |
| `conv-010-enum-underlying.c` | enum ↔ int conversions |
| `conv-011-implicit-arith.c` | Integer promotion rules in arithmetic |
| `conv-012-unsigned-overflow.c` | Unsigned wrapping (well-defined) |
| `conv-013-signed-overflow.c` | Signed overflow — exercises PEcatch_exceptional_condition |
| `conv-014-cast-chain.c` | Multiple chained casts: char→int→long→short |
| `conv-015-float-to-int-trunc.c` | float → int truncation |
| `conv-016-int-to-float-round.c` | Large int → float (precision loss) |
| `conv-017-double-to-float.c` | double → float (narrowing) |
| `conv-018-float-to-unsigned.c` | float → unsigned int |

### 3. `ptr/` — Pointer Operations (target: impl_mem.ml pointer paths)

| Test | Cerberus path exercised |
|------|------------------------|
| `ptr-001-subtract-same-array.c` | Pointer subtraction within array |
| `ptr-002-compare-same-array.c` | Pointer relational comparison in array |
| `ptr-003-compare-equality.c` | Pointer equality (==, !=) |
| `ptr-004-null-compare.c` | Compare pointer to NULL |
| `ptr-005-one-past-end-compare.c` | Compare one-past-end pointer |
| `ptr-006-void-ptr-cast.c` | Cast to/from void* |
| `ptr-007-func-ptr-compare.c` | Function pointer equality |
| `ptr-008-cross-alloc-compare.c` | Relational comparison of unrelated pointers |
| `ptr-009-ptr-to-int-roundtrip.c` | ptr → intptr_t → ptr roundtrip |
| `ptr-010-null-ptr-to-int.c` | NULL → integer conversion |
| `ptr-011-array-decay.c` | Array-to-pointer decay in expressions |
| `ptr-012-multidim-ptr.c` | Pointer arithmetic on multidimensional arrays |

### 4. `ctrl/` — Control Flow (target: core_reduction.ml Eif/Ecase/Elet)

| Test | Cerberus path exercised |
|------|------------------------|
| `ctrl-001-nested-switch.c` | Switch inside switch (Ecase nesting) |
| `ctrl-002-switch-many-cases.c` | Switch with many cases (large dispatch) |
| `ctrl-003-goto-forward.c` | Forward goto, skipping declarations |
| `ctrl-004-goto-backward.c` | Backward goto (manual loop) |
| `ctrl-005-goto-nested.c` | Goto across nested scopes |
| `ctrl-006-nested-if-deep.c` | 5+ levels of nested if (Eif reduction depth) |
| `ctrl-007-loop-break-continue.c` | Loop with both break and continue paths |
| `ctrl-008-do-while-zero.c` | do-while that executes body once (false condition) |
| `ctrl-009-for-empty-parts.c` | for(;;) with break, for with empty init/cond/step |
| `ctrl-010-early-return.c` | Multiple return paths in function |
| `ctrl-011-nested-scope-vars.c` | Many nested scopes with same-named variables |
| `ctrl-012-multi-decl.c` | Multiple declarations in one statement |

### 5. `expr/` — Expression Evaluation (target: core_eval.ml PEop/PEnot/PEctor)

| Test | Cerberus path exercised |
|------|------------------------|
| `expr-001-compound-literal.c` | Compound literal `(int[]){1,2,3}` (PEctor) |
| `expr-002-designated-init.c` | Designated initializers `{.x = 1, .y = 2}` |
| `expr-003-nested-ternary.c` | Chained ternary `a ? b : c ? d : e` |
| `expr-004-comma-complex.c` | Comma operator in various positions |
| `expr-005-sizeof-expr.c` | `sizeof` on various expressions |
| `expr-006-cast-in-expr.c` | Casts as subexpressions in arithmetic |
| `expr-007-bitfield-ops.c` | Bitfield read/write/arithmetic |
| `expr-008-enum-arith.c` | Arithmetic on enum values |
| `expr-009-negative-shift.c` | Shift by negative amount (UB) |
| `expr-010-large-shift.c` | Shift >= width of type (UB) |
| `expr-011-sequence-point.c` | Complex well-ordered expressions |
| `expr-012-logical-shortcircuit.c` | Side effects in `&&`/`||` short-circuit |

### 6. `struct/` — Struct/Union Operations (target: core_eval.ml PEstruct/PEunion/PEmemberof)

| Test | Cerberus path exercised |
|------|------------------------|
| `struct-001-nested-struct.c` | Struct containing struct (nested PEmember_shift) |
| `struct-002-nested-access.c` | `s.inner.field` chains |
| `struct-003-struct-array-member.c` | Struct with array member |
| `struct-004-union-type-pun.c` | Write one union member, read another |
| `struct-005-struct-copy.c` | Struct assignment (bulk copy) |
| `struct-006-struct-return.c` | Return struct from function |
| `struct-007-struct-param.c` | Pass large struct by value |
| `struct-008-anon-struct.c` | Anonymous struct/union members |
| `struct-009-init-partial.c` | Partial struct initialization (rest zero) |
| `struct-010-bit-field-layout.c` | Bitfield struct layout and access |

### 7. `libc/` — Libc-Requiring Tests (target: impl_mem.ml alloc/free/memcpy)

| Test | Cerberus path exercised |
|------|------------------------|
| `libc-001-malloc-free.c` | Basic malloc/free cycle |
| `libc-002-calloc.c` | calloc (zeroed allocation) |
| `libc-003-realloc.c` | realloc (resize allocation) |
| `libc-004-free-null.c` | `free(NULL)` — defined no-op |
| `libc-005-double-free.c` | Double free (UB) |
| `libc-006-use-after-free.c` | Read after free (UB) |
| `libc-007-free-stack.c` | Free a stack pointer (UB) |
| `libc-008-memcpy-basic.c` | memcpy basic usage |
| `libc-009-memcpy-struct.c` | memcpy of a struct |
| `libc-010-memcmp.c` | memcmp equal and unequal |
| `libc-011-memset.c` | memset to zero and nonzero |
| `libc-012-strlen.c` | strlen on string literals |
| `libc-013-malloc-large.c` | Large allocation |
| `libc-014-write-after-free.c` | Write after free (UB) |

## Verification

1. All tests complete (Cerberus runs without crashing, or detects UB as expected)
2. Coverage report shows improvement over baseline
