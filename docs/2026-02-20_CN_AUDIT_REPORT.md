# CN Implementation Audit Report — 2026-02-20

## Overview

Comprehensive audit of our Lean CN type checker implementation against the original CN OCaml implementation (`cn/lib/`). Five parallel audit agents examined:

1. **Types & Infrastructure** — Base.lean, Term.lean, Constraint.lean, ArgumentTypes.lean, Resource.lean, Spec.lean, Monad.lean, Context.lean, Simplify.lean, DerivedConstraints.lean
2. **Type Checking Core** — Expr.lean, Action.lean, Pexpr.lean, GhostStatement.lean, Check.lean
3. **Resource Inference + SMT** — Inference.lean, SmtLib.lean, SmtSolver.lean
4. **Parser & Resolution** — Parser.lean, Resolve.lean, Params.lean, Spine.lean
5. **Antipattern Sweep** — All CN files, all categories

**Scope**: Predicate-free fragment of CN (built-in Owned/Block, function specs, loop invariants, ghost statements, array ownership, pointer operations, SMT solving). Excludes: user-defined predicates, logical functions, lemmas, datatypes, type synonyms, Coq export.

**Current state**: 103/103 tests passing (100%). 17 DIVERGES-FROM-CN markers. 0 FIXME markers.

---

## Summary

| Severity | Count | Description |
|----------|-------|-------------|
| **BUG** | 15 | Incorrect behavior that can produce wrong verification results |
| **GAP** | 22 | Missing CN features that could cause failures on valid programs |
| **QUALITY** | 12 | Code quality issues, performance, or fragile patterns |

---

## Findings

### BUG-1: WrapI treated as identity instead of bitvector cast
- **File**: `SmtLib.lean:877-885`
- **CN ref**: `solver.ml:949-953` (bv_cast)
- **Impact**: WrapI wraps an integer value to a target bitvector width. CN translates this as `bv_cast` (sign/zero extend or truncate). We pass the value through unchanged. If source width differs from target (e.g., i64 wrapped to i32), the SMT query has a width mismatch — a 64-bit value where a 32-bit term is expected.
- **Fix**: Translate WrapI as bv_cast: determine target BT from `Memory.bt_of_sct (Integer ity)`, then apply sign_extend/zero_extend/extract based on source and target widths, matching `solver.ml:557-569`.

### BUG-2: Integer Rem uses "mod" instead of "rem"
- **File**: `SmtLib.lean:651`
- **CN ref**: `solver.ml:721`, `simple_smt.ml:176` — `num_rem = "rem"`
- **Impact**: For integer (non-bitvector) Rem, CN uses SMT-LIB's `rem` (truncated, sign follows dividend). We use `mod` (Euclidean, always non-negative). `rem(-7,3) = -1` but `mod(-7,3) = 2`.
- **Fix**: Change `mkBinApp "mod"` to `mkBinApp "rem"` in the `.rem` integer case.

### BUG-3: Clause.subst does NOT substitute in resources
- **File**: `Spec.lean:78`
- **CN ref**: `logicalReturnTypes.ml:25-40` (LRT.subst Resource case)
- **Impact**: The TODO comment says "subst in resource if needed" and passes the resource through unchanged. If a postcondition resource references the return symbol (e.g., `Owned<int>(return)`), substituting the actual return value will NOT propagate into the resource, potentially making the postcondition vacuously true for that resource.
- **Fix**: Substitute in `r.request` and `r.output.value`, and alpha-rename the bound name if it conflicts with the substitution.

### BUG-4: getNumZ doesn't normalize Bits values
- **File**: `Simplify.lean:173-177`
- **CN ref**: `indexTerms.ml:390-394` — `get_num_z` normalizes via `BT.normalise_to_range`
- **Impact**: CN normalizes Bits constants to their canonical range before returning. We return the raw value. Constant folding on out-of-range Bits values (e.g., `Bits(Signed, 8)` with value 200 should be -56) produces wrong results.
- **Fix**: In `getNumZ`, normalize: `| .const (.bits sign width v) => some (normaliseToRange sign width v)`

### BUG-5: Pointer comparisons produce .lt/.le instead of .ltPointer/.lePointer
- **File**: `Resolve.lean:559-563`
- **CN ref**: `compile.ml:506-517` (mk_binop with Loc type)
- **Impact**: CN distinguishes integer comparison (LT/LE) from pointer comparison (LTPointer/LEPointer). When left operand has type `Loc`, CN produces the pointer variants. We always produce `.lt`/`.le`. While both map to the same SMT comparison on addresses, the term structure diverges from CN.
- **Fix**: Check if the operation is `.lt`/`.le`/`.gt`/`.ge` and left operand has type `.loc`, and produce `.ltPointer`/`.lePointer`/etc.

### BUG-6: array_shift element type defaults to signed int
- **File**: `Resolve.lean:621-623`
- **CN ref**: `compile.ml:634-666` (infer_scty) — CN fails with "Cannot tell C-type of pointer"
- **Impact**: When `tryGetPointeeCtype` returns `none`, we silently use `signed int`. Pointer arithmetic on `char*`, `struct foo*`, etc. would use the wrong stride (4 bytes instead of 1 or sizeof(struct)), producing **incorrect offset calculations**.
- **Fix**: Throw an error instead of defaulting.

### BUG-7: `each` resource step type defaults to signed int
- **File**: `Parser.lean:688-689`
- **CN ref**: `compile.ml:1113-1120` (split_pointer_linear_step) — CN extracts step from ArrayShift
- **Impact**: When the predicate in `each` is not `Owned(some ct)`, the step type defaults to `signed int`. Resolution doesn't update the step field. Wrong step type causes incorrect array stride calculations.
- **Fix**: Either extract from ArrayShift during resolution, or fail when step type cannot be inferred.

### BUG-8: Fence action returns unit instead of failing
- **File**: `Expr.lean:525`, `Action.lean:524-526`
- **CN ref**: `check.ml:1900` — `Fence _mo -> Cerb_debug.error "todo: Fence"`
- **Impact**: CN errors on Fence; we silently succeed with unit. Could hide unverified code paths.
- **Fix**: Change to `TypingM.fail (.other "Fence not yet supported")`.

### BUG-9: Eunseq with single expression returns value directly instead of 1-tuple
- **File**: `Expr.lean:688-692`
- **CN ref**: `check.ml:2020-2029` — CN always wraps in `tuple_ [v]`
- **Impact**: Changes BaseType from `tuple [bt]` to `bt`. Downstream code expecting a tuple (e.g., `let weak (a: loaded integer) = unseq(load(...))`) may fail with a type mismatch.
- **Fix**: Remove the `es.length == 1` special case — always construct a tuple.

### BUG-10: conv_int Bool: comparison zero uses wrong type
- **File**: `Pexpr.lean:1039-1044`
- **CN ref**: `check.ml:414-420` — zero uses arg's type (`bt = IT.get_bt arg`), not target type
- **Impact**: CN creates zero with the ARG's type for comparison, then uses TARGET type for result. We use `targetBt` for both, creating a type mismatch in the EQ comparison.
- **Fix**: Use `argVal.bt` for the zero in the comparison, and `targetBt` for the result.

### BUG-11: conv_int for non-Bits target passes through unchanged
- **File**: `Pexpr.lean:1290-1291`
- **CN ref**: `check.ml:395` — `assert (match expect with BT.Bits _ -> true | _ -> false)`
- **Impact**: CN asserts the target MUST be Bits. We silently pass the value through for non-Bits targets, allowing incorrect type conversions.
- **Fix**: Fail for non-Bits target types.

### BUG-12: Ghost statement parse errors silently dropped
- **File**: `Expr.lean:423-426`
- **CN ref**: N/A (CN doesn't have this parse step — it uses muCore)
- **Impact**: A syntax error in a ghost statement (e.g., `cn_have(x = y)` with single `=`) produces NO error — the constraint is simply not checked. **Extremely dangerous** for a verification tool.
- **Fix**: Track whether any parser claims the magic text. If none does, warn or fail.

### BUG-13: Ghost arg parse failure silently skipped
- **File**: `Expr.lean:603`
- **Impact**: If a ghost argument annotation has a syntax error, it's silently ignored. The function call proceeds with missing ghost arguments.
- **Fix**: Distinguish "not a ghost arg annotation" from "parse failure".

### BUG-14: Shift operators accepted in CN specs but not in CN
- **File**: `Parser.lean:567-573`
- **CN ref**: `cerberus/frontend/model/cn.lem:43-61` (cn_binop) — `<<`/`>>` not in cn_binop
- **Impact**: CN's parser rejects `<<`/`>>` in spec expressions. We accept them. Programs using these in specs would pass our checker but be rejected by CN.
- **Fix**: Remove `<<`/`>>` from the CN spec parser, or mark as DIVERGES-FROM-CN extension.

### BUG-15: binopPrec defaults to 0 for unknown operators
- **File**: `Parser.lean:574`
- **Impact**: An unrecognized binary operator gets precedence 0 (lowest) instead of being rejected. This causes silent misparsing.
- **Fix**: Return `Option Nat` and fail on unknown operators.

---

### GAP-1: QPredicate.subst missing alpha-rename for quantified variable
- **File**: `Resource.lean:154-158`
- **CN ref**: `request.ml:111-125`
- **Impact**: Variable capture bug: if substitution's range contains the quantified variable, permission/iargs terms will incorrectly reference it after substitution.
- **Fix**: If `σ.relevant.contains qp.q.fst.id`, alpha-rename the QPredicate before substituting.

### GAP-2: ReturnType.subst missing alpha-rename for return sym
- **File**: `ArgumentTypes.lean` (ReturnType.subst)
- **CN ref**: `returnTypes.ml:9-13`
- **Impact**: If the substitution maps to an expression containing `rt.sym`, this causes variable capture in the LRT.
- **Fix**: Add alpha-renaming for `rt.sym` matching CN's `suitably_alpha_rename`.

### GAP-3: freeVarIds for match_ over-approximates
- **File**: `Term.lean:384-385`
- **CN ref**: `indexTerms.ml:101-118`
- **Impact**: Does not subtract pattern-bound variables from case body free vars. Over-approximation is conservative but could cause unnecessary alpha-renaming.
- **Fix**: Filter out pattern-bound variable IDs from each case body's free vars.

### GAP-4: qpredicateRequest missing movable_indices handling
- **File**: `Inference.lean:567`
- **CN ref**: `resourceInference.ml:317-363`
- **Impact**: Cannot extract individual elements from a QPredicate using concrete index values from the context.
- **Fix**: Track movable_indices in TypingState; implement iteration from CN.

### GAP-5: qpredicateRequest missing cases_to_map
- **File**: `Inference.lean:567`
- **CN ref**: `resourceInference.ml:62-97`
- **Impact**: Cannot combine multiple partial Q resources to satisfy a single Q request.
- **Fix**: Implement the General.cases mechanism.

### GAP-6: qpredicateRequest missing permission intersection
- **File**: `Inference.lean:567`
- **CN ref**: `resourceInference.ml:285-305`
- **Impact**: Cannot partially consume Q resources. We consume the entire Q or nothing.
- **Fix**: Implement permission intersection logic.

### GAP-7: qpredicateRequest missing nothing_more_needed check
- **File**: `Inference.lean:567`
- **CN ref**: `resourceInference.ml:365-375`
- **Impact**: Returns success as soon as one matching Q is found, without verifying full permission coverage.
- **Fix**: Add `forall q, not(needed)` check at the end.

### GAP-8: predicateRequestScan SMT slow path — single candidate only
- **File**: `Inference.lean:319`
- **CN ref**: `resourceInference.ml:169-226`
- **Impact**: If multiple resources match syntactically but require SMT to distinguish, we fail if there's more than one candidate. CN tries each candidate sequentially.
- **Fix**: Iterate over candidates in the slow path, returning the first that works.

### GAP-9: mapConst missing CVC5 Default workaround
- **File**: `SmtLib.lean:1200-1213`
- **CN ref**: `solver.ml:892-903`
- **Impact**: CVC5 rejects `(as const ...)` on non-literal values (CVC5 issue #11485). CN works around this for `Default` values.
- **Fix**: When value is `Const(Default t)`, translate as `Default(Map(keyBt, t))` instead.

### GAP-10: recordMember/recordUpdate unsupported
- **File**: `SmtLib.lean:1165-1166`
- **CN ref**: `solver.ml:837-859`
- **Impact**: Record types in specs (e.g., multi-output functions) will produce `.unsupported`.
- **Fix**: Implement as CN_Tuple selector/constructor operations.

### GAP-11: Missing check_live_alloc_bounds (4 locations)
- **Files**: `Expr.lean:208-229` (PtrLt/Gt/Le/Ge), `Expr.lean:148-157` (PtrArrayShift), `Expr.lean:236-257` (Ptrdiff), `Expr.lean:335-343` (CopyAllocId)
- **CN ref**: `check.ml:1597-1763`
- **Impact**: Pointers that are out-of-bounds (but same provenance) are not flagged. Already marked DIVERGES-FROM-CN.
- **Fix**: Add Alloc.History tracking and bounds checks. Requires Alloc predicate support.

### GAP-12: Simplified split_case ghost statement
- **File**: `GhostStatement.lean:282-288`
- **CN ref**: `check.ml:2251-2279`
- **Impact**: We just add the constraint as an assumption. CN forks into two branches (true/false) and verifies both. We may miss errors in the negated branch. Already marked DIVERGES-FROM-CN.
- **Fix**: Implement two-branch exploration.

### GAP-13: substStoreValues catch-all skips many term forms
- **File**: `Resolve.lean:946`
- **Impact**: Store value substitution doesn't traverse into `.mapGet`, `.mapSet`, `.apply`, `.good`, `.let_`, `.match_`, etc. Ghost statements using these in stored variables won't be substituted.
- **Fix**: Add explicit cases for all term constructors, or use a generic traversal.

### GAP-14: addr_eq is plain EQ, missing addr extraction
- **File**: `Resolve.lean:602-607`
- **CN ref**: `builtins.ml:139-145` (addr_eq = eq(addr(p), addr(q)))
- **Impact**: `addr_eq(p, q)` should compare numeric addresses only; we compare whole pointers (including provenance). Semantically different.
- **Fix**: Extract address via `addr_` before comparing.

### GAP-15: Missing `remove_a` function
- **File**: `Context.lean`
- **CN ref**: `context.ml:114-121`
- **Impact**: CN moves computational variables to logical scope when they go out of scope, preserving constraints. Without this, constraints may reference out-of-scope variables.
- **Fix**: Implement `remove_a` that moves bindings from computational to logical scope.

### GAP-16: Simplifier missing symbol value substitution
- **File**: `Simplify.lean:207`
- **CN ref**: `simplify.ml:221-225`
- **Impact**: CN replaces symbols with known constant values from the simplification context. We don't, reducing constant folding effectiveness.
- **Fix**: Accept a value context parameter.

### GAP-17: Simplifier missing WrapI constant folding
- **File**: `Simplify.lean:559-566`
- **CN ref**: `simplify.ml:559-566`
- **Impact**: `wrapI(ity, constant)` is not folded to a normalized constant.
- **Fix**: Check if child is numeric constant and fold via `numLitNorm`.

### GAP-18: Simplifier missing Cast identity elimination
- **File**: `Simplify.lean:567-569`
- **CN ref**: `simplify.ml:567-569`
- **Impact**: Identity casts (source == target type) are not eliminated. Already marked DIVERGES-FROM-CN.
- **Fix**: Implement BEq for BaseType.

### GAP-19: Simplifier missing Struct identity detection
- **File**: `Simplify.lean`
- **CN ref**: `simplify.ml:496-508`
- **Impact**: `{ .a = s.a, .b = s.b }` not simplified to `s`.
- **Fix**: Detect when all struct fields are member accesses from the same source.

### GAP-20: SizeOf not evaluated to constant
- **File**: `Simplify.lean:585`
- **CN ref**: `simplify.ml:585`
- **Impact**: `sizeof(T)` stays symbolic instead of being resolved to a concrete integer. Already marked DIVERGES-FROM-CN.
- **Fix**: Pass memory layout information to the simplifier.

### GAP-21: Eif branch state handling diverges from CN
- **File**: `Expr.lean:461-502`
- **CN ref**: `check.ml:1985-2002`, `typing.ml:67-72` (pure)
- **Impact**: CN's `pure` discards BOTH branches' state changes — neither's resource operations survive. Our `tryBranch` preserves the successful branch's resource state. For asymmetric resource patterns across branches, this could be unsound.
- **Fix**: Consider implementing CN's `pure` semantics (discard both branches' state, keep only obligations).

### GAP-22: resolveAnnotTerm CHECK mode doesn't verify expected type
- **File**: `Resolve.lean:513-514`
- **CN ref**: `wellTyped.ml:567`
- **Impact**: When resolving a Z literal with a non-Bits, non-Integer expected type, we return `.integer` without verifying the expected type matches.
- **Fix**: Error if `expectedBt` is `some bt` and `bt` is not `.bits` and not `.integer`.

---

### QUALITY-1: Spine.lean:174 — Ghost arg type comparison uses Repr string comparison
- **CN ref**: `check.ml:1175`
- **Fix**: Implement BEq for BaseType.

### QUALITY-2: Params.lean:292 — Loop variable output symbol: `sym.id + 10000`
- **CN ref**: CN uses proper fresh counter
- **Fix**: Use freshCounter or larger offset. Fragile for large programs.

### QUALITY-3: Params.lean:222,275 — Invariant parse/resolution errors silently dropped
- **Fix**: Accumulate and report errors instead of filterMap with `| .error _ => none`.

### QUALITY-4: Monad.lean:265 — freshSym counter starts at 0, may collide with parser symbols
- **Fix**: Initialize to max of all parsed program symbol IDs + 1.

### QUALITY-5: SmtLib.lean:1094-1148 — Struct SMT terms built via string interpolation
- **CN ref**: `solver.ml:805-827`
- **Fix**: Use Term.appT / Term.mkApp for proper AST construction.

### QUALITY-6: SmtLib.lean:296 — Struct declarations silently skip unsupported field types
- **Fix**: Return error or warning instead of silently skipping.

### QUALITY-7: Parser.lean:184 — `char` defaults to signed (implementation-defined)
- **Fix**: Document as matching Cerberus's choice, or check ABI setting.

### QUALITY-8: Resolve.lean:654 — mapGet fallback uses map's own type on non-map
- **Fix**: Throw error when `m'.bt` is not `.map`.

### QUALITY-9: Params.lean:257 — saveArgCTypes lookup defaults to empty list
- **Fix**: Fail or warn when expected C types are missing for a loop label.

### QUALITY-10: Params.lean:486, Resolve.lean:826 — Missing global silently skipped
- **Fix**: Fail immediately with clear error.

### QUALITY-11: Check.lean:289 — parseAndCheckBool returns false on error
- **Fix**: Return richer type or log the error.

### QUALITY-12: Pexpr.lean:485 — Pattern type falls back to value type
- **Fix**: Acceptable fallback but should log a warning.

---

## Work Packages

Findings are grouped into independent work packages (WP) that can be executed in parallel by agent teams. Each WP touches different files to avoid conflicts.

### WP-A: SMT Encoding Fixes (SmtLib.lean)

**Priority**: HIGH — BUG-1 and BUG-2 directly produce wrong SMT semantics.

| ID | Finding | Effort |
|----|---------|--------|
| BUG-1 | WrapI → bv_cast | Medium |
| BUG-2 | Rem "mod" → "rem" | Trivial |
| GAP-9 | mapConst CVC5 Default workaround | Small |
| GAP-10 | recordMember/recordUpdate | Medium |
| QUALITY-5 | Struct terms: string interpolation → proper AST | Medium |
| QUALITY-6 | Struct decl: report unsupported fields | Small |

**Files**: `SmtLib.lean` only.

### WP-B: Resolution & Type Safety (Resolve.lean)

**Priority**: HIGH — BUG-5 and BUG-6 affect pointer and array correctness.

| ID | Finding | Effort |
|----|---------|--------|
| BUG-5 | .lt → .ltPointer for Loc operands | Small |
| BUG-6 | array_shift: fail instead of default int | Trivial |
| GAP-13 | substStoreValues: exhaustive traversal | Medium |
| GAP-14 | addr_eq: extract addr before comparing | Small |
| GAP-22 | resolveAnnotTerm: verify expected type | Small |
| QUALITY-8 | mapGet: fail on non-map | Trivial |
| QUALITY-10 | Missing global: fail immediately | Trivial |

**Files**: `Resolve.lean` only.

### WP-C: Parser Hardening (Parser.lean)

**Priority**: MEDIUM — BUG-7 and BUG-14/15 affect parsing correctness.

| ID | Finding | Effort |
|----|---------|--------|
| BUG-7 | each step type: fail instead of default int | Small |
| BUG-14 | Remove << >> from CN spec parser | Trivial |
| BUG-15 | binopPrec: fail on unknown operator | Small |
| QUALITY-7 | char signedness: document decision | Trivial |

**Files**: `Parser.lean` only.

### WP-D: Expression Checker Fixes (Expr.lean, Pexpr.lean)

**Priority**: HIGH — BUG-8/9/10/11/12/13 affect verification correctness.

| ID | Finding | Effort |
|----|---------|--------|
| BUG-8 | Fence: fail instead of succeed | Trivial |
| BUG-9 | Eunseq: always construct tuple | Trivial |
| BUG-10 | conv_int Bool: fix zero type | Small |
| BUG-11 | conv_int: fail on non-Bits target | Small |
| BUG-12 | Ghost stmt parse error: warn/fail | Medium |
| BUG-13 | Ghost arg parse error: warn/fail | Small |

**Files**: `Expr.lean`, `Pexpr.lean`.

### WP-E: Type Substitution & Alpha-Renaming (Spec.lean, Resource.lean, ArgumentTypes.lean, Term.lean)

**Priority**: HIGH — BUG-3 and GAP-1/2 can cause variable capture bugs.

| ID | Finding | Effort |
|----|---------|--------|
| BUG-3 | Clause.subst: substitute in resources | Medium |
| GAP-1 | QPredicate.subst: alpha-rename q variable | Medium |
| GAP-2 | ReturnType.subst: alpha-rename return sym | Small |
| GAP-3 | freeVarIds: subtract pattern-bound vars in match_ | Small |

**Files**: `Spec.lean`, `Resource.lean`, `ArgumentTypes.lean`, `Term.lean`.

### WP-F: Simplifier Improvements (Simplify.lean)

**Priority**: LOW — Performance optimizations, not correctness. SMT handles these.

| ID | Finding | Effort |
|----|---------|--------|
| BUG-4 | getNumZ: normalize Bits values | Small |
| GAP-16 | Symbol value substitution | Medium |
| GAP-17 | WrapI constant folding | Small |
| GAP-18 | Cast identity elimination (needs BEq) | Medium |
| GAP-19 | Struct identity detection | Medium |
| GAP-20 | SizeOf → concrete constant | Medium |

**Files**: `Simplify.lean` (plus `Base.lean` for BEq).

### WP-G: Resource Inference Hardening (Inference.lean, Monad.lean)

**Priority**: MEDIUM — Only needed for programs that exercise QPredicate partial consumption.

| ID | Finding | Effort |
|----|---------|--------|
| GAP-4 | movable_indices handling | Large |
| GAP-5 | cases_to_map for multiple Q matches | Large |
| GAP-6 | Permission intersection | Large |
| GAP-7 | nothing_more_needed check | Small |
| GAP-8 | SMT slow path: iterate candidates | Small |

**Files**: `Inference.lean`, `Monad.lean`.

### WP-H: Infrastructure & Miscellaneous (Various files)

**Priority**: LOW — Quality improvements and minor gaps.

| ID | Finding | Effort |
|----|---------|--------|
| GAP-15 | remove_a function | Small |
| GAP-21 | Eif: pure semantics (complex, risky) | Large |
| GAP-12 | split_case: two-branch exploration | Medium |
| QUALITY-1 | BEq for BaseType (shared with WP-F) | Medium |
| QUALITY-2 | Loop sym: use fresh counter | Trivial |
| QUALITY-3 | Invariant error reporting | Small |
| QUALITY-4 | freshSym counter initialization | Small |
| QUALITY-9 | saveArgCTypes: warn on missing | Trivial |
| QUALITY-11 | parseAndCheckBool error handling | Small |
| QUALITY-12 | Pattern type fallback: add warning | Trivial |

**Files**: `Context.lean`, `Expr.lean`, `GhostStatement.lean`, `Monad.lean`, `Params.lean`, `Check.lean`, `Pexpr.lean`, `Base.lean`.

---

## Recommended Execution Order

```
Phase 1 — High priority, parallel (WP-A, WP-B, WP-C, WP-D, WP-E)
  These are independent and touch different files.
  Fix all BUGs and critical gaps.

Phase 2 — Medium priority, parallel (WP-F, WP-G, WP-H)
  Performance and completeness improvements.
  WP-F and WP-H share BEq dependency — coordinate.
  WP-G is large and only needed for QPredicate edge cases.
```

After each phase: `make lean && make test-cn-nolibc` — no regressions.

---

## Out of Scope

The following are intentional design divergences (not bugs):

| Divergence | Rationale |
|-----------|-----------|
| Hybrid inline+post-hoc solver | Architecturally clean |
| Lazy muCore transformation | Simpler than two AST types |
| `Loc` type parameter dropped | Matches CN BaseTypes.Unit |
| `ResourceName.owned` has `Option Ctype` | Pre-resolution state |
| `LCSet` as List | Duplicates harmless |
| No Coq export | Replaced by Lean proofs |
| No predicates/functions/lemmas | Will use Lean proof system |
| SeqRMW type checking | Extension for Core IR compat |
| Fresh solver per obligation | Simpler than persistent |
| PtrEq simplified ambiguous case | Sound, skips rare case |
| `have` ghost statement implemented | Forward-compatible extension |
| Context uses List not Map | O(n) acceptable for small programs |
| Global state in TypingState not Context | Architectural choice |

---

## Appendix: Existing DIVERGES-FROM-CN Markers

```
grep -rn "DIVERGES-FROM-CN" lean/CerbLean/CN/
```

17 markers across: Inference.lean (6), Expr.lean (4), Action.lean (2), GhostStatement.lean (2), Params.lean (1), DerivedConstraints.lean (1), SmtLib.lean (1).

All are intentional simplifications that are internally consistent. None produce incorrect results for the test suite.
