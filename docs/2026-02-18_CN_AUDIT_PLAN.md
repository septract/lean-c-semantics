# CN Comprehensive Audit & Alignment Plan — Team Execution

**Created**: 2026-02-18
**Last updated**: 2026-02-19
**Status**: Waves 0–2 complete, Wave 3 in progress

## Context

Our Lean CN implementation targets the **predicate-free fragment** of CN's OCaml verification system (~29,500 lines, ~97 files). Goal: close all gaps to match CN's verification capability for built-in `Owned`/`Block` resources, function specs, loop invariants, ghost variables, array ownership, and SMT-based constraint solving.

**Excluded**: User-defined predicates, logical functions, lemmas, recursive definitions, Coq export.

**CN source**: `tmp/cn/` (main branch) | **Lean source**: `lean/CerbLean/CN/`

### Current Test Results (2026-02-19)

| Suite | Pass | Fail | Total |
|-------|------|------|-------|
| Unit tests (parser/typecheck) | 9 | 0 | 9 |
| Unit tests (obligations) | 7 | 0 | 7 |
| Unit tests (SMT) | 3 | 0 | 3 |
| Integration (nolibc) | 84 | 6 | 90 |

**6 Failing integration tests** (down from initial 3 of 78; 12 new tests added):
- `044-pre-post-increment.c`: Resource tracking bug (Kill after increment in RMW context)
- `091-array-owned.c`: Missing resource — array QPredicate matching not finding resource
- `097-ghost-extract.c`: Spec parsing failure (extract syntax not parsed)
- `098-loop-invariant.c`: `Too many arguments provided` — label spec processing broken
- `099-global-access.c`: `unbound variable: g` — global variable support not implemented
- `100-ghost-params.c`: Spec parsing failure (ghost parameter syntax not parsed)

### Type System Audit Results (2026-02-18)

All type definitions match CN exactly:
- Base types: 16/16 constructors
- Constants: 11/11
- Unary operators: 7/7
- Binary operators: 31/31
- Term constructors: 40/40
- Resource types: all match
- LogicalConstraint: 2/2

Minor deviations (acceptable):
- `Loc` type parameter dropped (matches CN's `BaseTypes.Unit` module)
- `ResourceName.owned` has `Option Ctype` (pre-resolution)
- `LCSet` is a List not a Set (duplicates harmless)
- `LogicalConstraint.subst` skips alpha-renaming (marked DIVERGES-FROM-CN)

---

## Execution Architecture

The top-level agent (leader) coordinates work across **3 waves** of parallel work packages. Each package owns specific files to avoid conflicts. Agents within a wave run concurrently.

```
Wave 0: Write plan + audit tests (parallel, read-only/test-only)       ✅ DONE
   │
Wave 1: Foundation fixes (parallel, independent files)                  ✅ DONE
   │    ├─ WP-A: SMT Encoding (SmtLib.lean, SmtSolver.lean)            ✅ DONE
   │    ├─ WP-B: Constraint Simplification (Simplify.lean)             ✅ DONE
   │    ├─ WP-C: Derived Constraints (DerivedConstraints.lean)         ✅ DONE
   │    ├─ WP-D: Alpha-renaming fix (Constraint.lean, Term.lean)       ⚠️  DEFERRED
   │    └─ WP-E: New test development (tests/cn/)                      ✅ DONE
   │
Wave 2: Core capabilities (parallel, depends on Wave 1)                ✅ DONE
   │    ├─ WP-F: Resource Inference expansion (Inference.lean)          ✅ DONE (partial)
   │    ├─ WP-G: Pointer memops + RMW fix (Expr.lean, Action.lean)     ✅ DONE (partial)
   │    ├─ WP-H: Pure expression cases (Pexpr.lean)                    ✅ DONE (partial)
   │    ├─ WP-I: Ghost statements (GhostStatement.lean)                ✅ DONE
   │    └─ WP-J: Ghost parameters (Parser.lean, Spec.lean, Spine.lean) ❌ NOT DONE
   │
Wave 3: Extended features (parallel, depends on Wave 2)                🔄 IN PROGRESS
        ├─ WP-K: Loop invariants (Params.lean, Check.lean Erun path)   ❌ NOT DONE
        ├─ WP-L: wellTyped checking (WellTyped.lean)                   ❌ NOT DONE
        └─ WP-M: Global variables + accesses (Parser.lean, Check.lean) ❌ NOT DONE
```

---

## Wave 0: Plan & Audit — ✅ COMPLETE

### WP-0A: Write Plan Document — ✅
Written to `docs/2026-02-18_CN_AUDIT_PLAN.md`

### WP-0B: Audit Existing Tests for Spurious Passes — ✅
Report: `docs/2026-02-18_TEST_AUDIT_REPORT.md`

Key findings:
- 5 trivially-passing tests (no annotations or all-trusted)
- 8 tests with weak postconditions
- ~33 genuinely non-trivial tests
- `*NoSMT` bug was in dead code (no impact on existing tests)

---

## Wave 1: Foundation Fixes — ✅ COMPLETE

Completed in commit `3ce7320` (2026-02-18).

### WP-A: SMT Encoding Correctness — ✅ DONE

**Completed tasks:**
1. ✅ `*NoSMT` → uninterpreted functions (`mul_uf_<sort>`, `div_uf_<sort>`, etc.) for all base types
2. ✅ Solver preamble: `cn_tuple_N` (N=0..15), `cn_list`, `cn_option`, `mem_byte`, pointer ADTs
3. ✅ MemByte → `mem_byte` ADT sort
4. ✅ `solverBasicsPreamble` replaces `pointerPreamble` in SmtSolver.lean

**Remaining (incremental, low priority):**
- CType → `Int` encoding via CTypeMap
- EachI unrolling to conjunction
- Additional term encodings: min/max, exp, bwClz/bwCtz, good, List/Map/Set/Option ops, Record encoding, full Match compilation, representable/good for struct/array

### WP-B: Constraint Simplification — ✅ DONE
`Simplify.lean` created (755 lines) with:
- Recursive term simplifier
- Constant folding, boolean simplification, equality reduction
- Accessor reduction (StructMember of Struct → field)
- Cast folding, SizeOf evaluation
- Integrated into Monad.lean

### WP-C: Derived Constraints — ✅ DONE
`DerivedConstraints.lean` created (180 lines) with:
- `derivedLc1`: hasAllocId, address bounds for Owned resources
- `derivedLc2`: non-overlap/separation constraints for pairs
- Integrated into Monad.lean:addR

### WP-D: Alpha-Renaming Fix — ⚠️ DEFERRED
Not yet implemented. Marked DIVERGES-FROM-CN in:
- `Inference.lean:519` (qpredicateRequest skips alpha-renaming)
- `LogicalConstraint.subst` still skips rename on clash

No current test exercises this path. Will become relevant when forall-quantified constraints appear in QPredicate permission expressions.

### WP-E: Test Development — ✅ DONE
12 new test files added (090–100), bringing suite from 78 to 90:
- `090-nosmt-operations.smt-fail.c` — NoSMT uninterpreted functions
- `091-array-owned.c` — array ownership (FAILING)
- `092-separation.c` / `092-separation.fail.c` — pointer non-overlap
- `093-padding-struct.c` — struct with padding
- `094-ptr-comparison.c` — pointer equality
- `095-ptr-to-int.c` — intFromPtr
- `096-ghost-have.c` — `have` ghost statement (**PASSING** as of 2026-02-19)
- `097-ghost-extract.c` — `extract` from `each` (FAILING — requires spec parser changes)
- `098-loop-invariant.c` — while loop with invariant (FAILING)
- `099-global-access.c` — global variable (FAILING)
- `100-ghost-params.c` — ghost function parameters (FAILING — requires spec parser)

---

## Wave 2: Core Capabilities — ✅ COMPLETE (with partial items)

Completed across commits `b86e2b2` (2026-02-18), `e950a7c` (2026-02-19), `9da903b` (2026-02-19).

### WP-F: Resource Inference Expansion — ✅ DONE (partial)

**Completed:**
1. ✅ `qpredicateRequest` — simplified version (name/step/pointer matching, full consumption)
2. ✅ `unpackArrayResource` — `Owned<T[N]>` → QPredicate
3. ✅ `tryRepackArray` — QPredicate → `Owned<T[N]>`
4. ✅ `addResourceWithUnfold` extended to chain struct → array unpacking

**Remaining (marked DIVERGES-FROM-CN):**
- Padding handling in struct unpack/repack (3 DIVERGES-FROM-CN markers)
- `check_live_alloc` (allocation liveness checking)
- Multi-candidate SMT slow path in resource matching
- `do_unfold_resources` fixpoint loop
- Alpha-renaming in qpredicateRequest

### WP-G: Pointer Memops + RMW Fix — ✅ DONE (partial)

**Completed:**
- ✅ PtrEq (simplified: skips ambiguous provenance case)
- ✅ PtrNe (simplified: negated PtrEq)
- ✅ IntFromPtr (simplified representability check)
- ✅ SeqRMW type checking with lazy muCore param slot handling

**Remaining (explicit `fail` stubs):**
- PtrLt, PtrGt, PtrLe, PtrGe — require `check_both_eq_alloc` + `check_live_alloc_bounds`
- Ptrdiff
- PtrFromInt
- CopyAllocId
- Fix test 044 (Kill resource lifecycle in RMW context)

### WP-H: Pure Expression Cases — ✅ DONE (partial)

**Completed:**
- ✅ Cnil (empty list constructor)
- ✅ Ccons (list cons constructor)
- ✅ ctype_width (bit width computation)
- ✅ PEmemberof (struct member access — was already present)

**Remaining:**
- Carray (array constructor)
- ByteFromInt / IntFromByte

### WP-I: Ghost Statements — ✅ DONE

Fully implemented across `GhostStatement.lean` (350 lines), `Expr.lean`, `Resolve.lean`, `Annot.lean`, `Parser.lean`:

- ✅ Ghost statement detection in Esseq (cerb::magic attribute parsing)
- ✅ Ghost statement text parsing (CN/Parser.lean)
- ✅ Symbol resolution against typing context (`resolveContextFromTypingContext`)
- ✅ Store value substitution for stack slot variables (`substStoreValues`)
- ✅ `have` handler (addC + requireConstraint)
- ✅ `assert` handler (requireConstraint only)
- ✅ `splitCase` handler (addC, simplified vs CN)
- ✅ `print` handler (no-op)
- ✅ `instantiate`/`extract` stubs (explicit fail — require QPredicate support)
- ✅ Predicate-dependent stubs (pack/unpack/unfold/apply/inline/toFromBytes)
- ✅ Test 096-ghost-have PASSING

### WP-J: Ghost Parameters — ❌ NOT DONE

Ghost parameters (`/*@ ghost int g @*/` in function signatures) are not yet supported:
- Spine.lean:165 skips ghost args in function type processing
- Parser.lean does not parse ghost parameter declarations
- No test coverage (100-ghost-params.c fails at spec parse)

**Blocked by**: Requires spec parser extension + Spine.lean changes

---

## Wave 3: Extended Features — 🔄 IN PROGRESS

### WP-K: Loop Invariants — ❌ NOT DONE
**Status**: Test 098-loop-invariant.c fails with "Too many arguments provided" — label spec processing is broken
**Files**: `CN/TypeChecking/Params.lean`, `CN/TypeChecking/Check.lean`
**Depends on**: WP-I (ghost statement infrastructure)

**Tasks**:
1. Parse loop invariant annotations from label definitions (cerb::magic on Esave nodes)
2. Process loop labels like function specs (resources + constraints)
3. At `Erun`, verify invariant holds on entry
4. At loop body, assume invariant, verify it's maintained
**CN ref**: `core_to_mucore.ml:931-1026`

### WP-L: wellTyped Checking — ❌ NOT DONE (deprioritized)
**Status**: Functionality distributed across Check.lean, Inference.lean, Pexpr.lean
**Assessment**: Not needed as a separate module. Type checking is embedded in the existing checking pipeline. The remaining gaps (inferTerm, checkTerm for complex terms) can be added incrementally to Pexpr.lean when needed.

**Recommendation**: Remove as standalone WP. Address specific gaps as they surface in test failures.

### WP-M: Global Variables + `accesses` — ❌ NOT DONE
**Status**: Test 099-global-access.c fails with "unbound variable: g"
**Files**: `CN/Parser.lean`, `CN/TypeChecking/Check.lean`
**Depends on**: Wave 2 complete

**Tasks**:
1. Parse `accesses x` clause in function annotations
2. Generate implicit `Owned` resource for global variable
3. Look up global symbol in Core file's global declarations
**CN ref**: `core_to_mucore.ml:718-723`

---

## Remaining Known Divergences from CN

12 `DIVERGES-FROM-CN` markers across the codebase:

| File | Description | Impact |
|------|-------------|--------|
| Inference.lean (×4) | Padding resources skipped in struct unpack/repack | Internally consistent; padding not tracked |
| Inference.lean (×1) | qpredicateRequest: no alpha-renaming or permission widening | Could mis-match resources with quantifier name collisions |
| GhostStatement.lean (×2) | split_case: simplified to just addC | Sound but less precise |
| Expr.lean (×3) | PtrEq/PtrNe simplified, IntFromPtr simplified representability | Skips ambiguous provenance cases |
| Spine.lean (×2) | gargs_opt handling differs (ghost params not supported) | Blocks ghost parameter tests |
| Simplify.lean (×2) | SizeOf not constant-folded, cast reduction differs | Minor optimization gap |
| DerivedConstraints.lean (×1) | Missing VIP allocation bounds | Minor completeness gap |
| Action.lean (×1) | SeqRMW: CN asserts error, we type-check | Extension beyond CN |

0 `FIXME` markers — all known issues are either fixed or marked as intentional divergences.

---

## Leader Integration Points

**After Wave 1** — ✅ DONE:
- ✅ Monad.lean patched: `Simplify.simplify` integrated
- ✅ Monad.lean patched: `deriveConstraints` integrated in `addR`
- ✅ TypeChecking.lean aggregator updated
- ✅ Tests verified: 83/90 → progressed to 84/90

**After Wave 2** — ✅ DONE:
- ✅ GhostStatement.lean integrated into Expr.lean Esseq path
- ✅ Symbol resolution + store value substitution working
- ✅ Module imports updated
- ✅ Tests verified: 84/90 (96-ghost-have now PASSING)

**After Wave 3** (remaining):
- Integrate loop invariant processing into Params.lean/Check.lean
- Add global variable resource generation
- Final `make test-cn` pass
- Update CLAUDE.md with new capabilities

---

## Revised Priority (Remaining Work)

**High Impact — Unblocks failing tests:**

| Priority | Task | Test Unblocked | Effort |
|----------|------|----------------|--------|
| 1 | **WP-K: Loop invariants** | 098-loop-invariant.c | Medium (label spec parsing + invariant checking) |
| 2 | **WP-J: Ghost parameters** | 100-ghost-params.c | Medium (spec parser + Spine.lean) |
| 3 | **WP-M: Global variables** | 099-global-access.c | Small (parser + resource generation) |
| 4 | **Fix 044 RMW bug** | 044-pre-post-increment.c | Small (Kill lifecycle in RMW) |
| 5 | **Fix 091 array QPredicate matching** | 091-array-owned.c | Small (debug resource matching) |

**Medium Impact — Correctness improvements:**

| Priority | Task | Description |
|----------|------|-------------|
| 6 | WP-D: Alpha-renaming | Fix constraint substitution for forall-bound vars |
| 7 | PtrLt/Gt/Le/Ge memops | Require allocation liveness checks |
| 8 | PtrFromInt / Ptrdiff / CopyAllocId | Remaining pointer memops |
| 9 | Padding in struct unpack/repack | Close 4 DIVERGES-FROM-CN markers |
| 10 | qpredicateRequest strengthening | Alpha-renaming + permission analysis |

**Low Impact — Incremental SMT completeness:**

| Priority | Task |
|----------|------|
| 11 | EachI unrolling, CType encoding |
| 12 | min/max/exp term encodings |
| 13 | List/Map/Set/Option SMT ops |
| 14 | Full Match compilation |
| 15 | ByteFromInt/IntFromByte, Carray |

---

## Design Differences to KEEP

| Difference | Rationale |
|-----------|-----------|
| Hybrid inline+post-hoc solver | Architecturally clean; inline guides, post-hoc certifies |
| Lazy muCore transformation | Simpler than maintaining two AST types; equivalent semantics |
| `Loc` type parameter dropped | Matches CN's `BaseTypes.Unit` module; no information loss |
| `ResourceName.owned` has `Option Ctype` | Represents pre-resolution state; resolved before type checking |
| `LCSet` as List | Duplicates don't affect correctness, minor perf cost |
| No Coq export | Replaced by Lean proofs (project goal) |
| No user-defined predicates/functions/lemmas | Will use Lean's own proof system |

---

## Changelog

- **2026-02-18**: Initial plan created. Waves 0–1 executed.
- **2026-02-18**: Wave 2 executed (commits b86e2b2, e950a7c). Test suite expanded from 78 → 90 files.
- **2026-02-19**: Ghost statement symbol resolution + SMT preamble fix (commit 9da903b). Test 096-ghost-have now passes. Pass rate: 84/90 (93%).
