# CN Comprehensive Audit & Alignment Plan — Team Execution

**Created**: 2026-02-18
**Status**: Approved, execution in progress

## Context

Our Lean CN implementation (~10,333 lines, 27 files) targets the **predicate-free fragment** of CN's OCaml verification system (~29,500 lines, ~97 files). Current: 75/78 (96%) nolibc tests pass. Goal: close all gaps to match CN's verification capability for built-in `Owned`/`Block` resources, function specs, loop invariants, ghost variables, array ownership, and SMT-based constraint solving.

**Excluded**: User-defined predicates, logical functions, lemmas, recursive definitions, Coq export.

**CN source**: `tmp/cn/` (main branch) | **Lean source**: `lean/CerbLean/CN/`

### Current Test Results (2026-02-18)

| Suite | Pass | Fail | Total |
|-------|------|------|-------|
| Unit tests (parser/typecheck) | 9 | 0 | 9 |
| Unit tests (obligations) | 7 | 0 | 7 |
| Unit tests (SMT) | 3 | 0 | 3 |
| Integration (nolibc) | 75 | 3 | 78 |

**3 Failing integration tests**:
- `044-pre-post-increment.c`: Resource tracking bug (Kill after increment)
- `066-null-to-int.c`: `intFromPtr` memop not implemented
- `070-increments.c`: `SeqRMW` not supported (interpreter-level)

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
- `LogicalConstraint.subst` skips alpha-renaming (to be fixed)

---

## Execution Architecture

The top-level agent (leader) coordinates work across **3 waves** of parallel work packages. Each package owns specific files to avoid conflicts. Agents within a wave run concurrently.

```
Wave 0: Write plan + audit tests (parallel, read-only/test-only)
   │
Wave 1: Foundation fixes (parallel, independent files)
   │    ├─ WP-A: SMT Encoding (SmtLib.lean, SmtSolver.lean)
   │    ├─ WP-B: Constraint Simplification (NEW Simplify.lean)
   │    ├─ WP-C: Derived Constraints (NEW DerivedConstraints.lean + Monad.lean patch)
   │    ├─ WP-D: Alpha-renaming fix (Constraint.lean, Term.lean)
   │    └─ WP-E: New test development (tests/cn/)
   │
Wave 2: Core capabilities (parallel, depends on Wave 1)
   │    ├─ WP-F: Resource Inference expansion (Inference.lean)
   │    ├─ WP-G: Pointer memops + RMW fix (Expr.lean, Action.lean)
   │    ├─ WP-H: Pure expression cases (Pexpr.lean)
   │    ├─ WP-I: Ghost statements (NEW GhostStatement.lean)
   │    └─ WP-J: Ghost parameters (Parser.lean, Spec.lean, Spine.lean)
   │
Wave 3: Extended features (parallel, depends on Wave 2)
        ├─ WP-K: Loop invariants (Params.lean, Check.lean Erun path)
        ├─ WP-L: wellTyped checking (NEW WellTyped.lean)
        └─ WP-M: Global variables + accesses (Parser.lean, Check.lean)
```

---

## Wave 0: Plan & Audit (Immediate)

### WP-0A: Write Plan Document
**Owner**: Leader
**Task**: Write this plan to `docs/2026-02-18_CN_AUDIT_PLAN.md`

### WP-0B: Audit Existing Tests for Spurious Passes
**Owner**: Agent (read-only)
**Task**: For each of the 75 passing CN tests, verify the pass is genuine by checking:
1. Does the test exercise the feature it claims to test?
2. Could it pass with a trivially-broken type checker?
3. Do the SMT obligations generated look correct?
**Output**: Report listing any tests that may be passing spuriously

---

## Wave 1: Foundation Fixes (Parallel)

All packages in this wave touch **different files** and can run fully concurrently.

### WP-A: SMT Encoding Correctness
**Files owned**: `CN/Verification/SmtLib.lean`, `CN/Verification/SmtSolver.lean`
**Depends on**: Nothing
**Estimated scope**: ~400 lines changed/added

**Tasks** (execute sequentially within this package):

1. **CRITICAL: Fix `*NoSMT` as uninterpreted functions**
   - `SmtLib.lean:377-401` wrongly translates `mulNoSMT` as `bvmul`
   - CN ref: `solver.ml:703,710,716,723,730`
   - Emit `declare-fun mul_uf_<sort> (<sort> <sort>) <sort>` on demand
   - Map `*NoSMT` terms to applications of these uninterpreted functions

2. **Add missing ADT declarations to solver preamble**
   - `cn_list<T>` with `cn_nil`/`cn_cons(head,tail)` — CN ref: `solver.ml:58-80`
   - `cn_option<T>` with `cn_none`/`cn_some(cn_val)` — CN ref: `solver.ml:91-98`
   - `cn_tuple_N<T1..TN>` for N=2..8 (0 exists already) — CN ref: `solver.ml:58-78`
   - `mem_byte` with `AiV(alloc_id: option<AllocId>, value: BitVec 8)` — CN ref: `solver.ml:83-87`

3. **Fix MemByte → `mem_byte` ADT sort** (depends on task 2)

4. **Add CType → `Int` encoding via CTypeMap**
   - CN ref: `solver.ml:113-130, 419`

5. **Fix EachI: unroll to conjunction instead of quantify**
   - CN ref: `solver.ml:785-796`

6. **Add missing term encodings** (can be done incrementally):
   - `min`/`max` → `ite` desugaring
   - `exp` → constant-fold for concrete args
   - `bwClzNoSMT`/`bwCtzNoSMT` → ite-tree (CN ref: `solver.ml:575-591`)
   - `bwFfsNoSMT`/`bwFlsNoSMT` → desugar to CTZ/CLZ
   - `good` → `good_value` helper for int/ptr/struct types
   - List ops → `cn_list` ADT selectors
   - Map ops → SMT `Array` (`store`/`select`/`as const`)
   - Set ops → CVC5 `Set` theory
   - Option ops → `cn_option` ADT
   - Multi-element tuple → `cn_tuple_N` selectors
   - Record → encode as positional tuple
   - Full `Match` → nested ite/let/is-Con compilation
   - `representable`/`good` for struct/array → recursive decomposition

### WP-B: Constraint Simplification
**Files owned**: NEW `CN/TypeChecking/Simplify.lean`
**Depends on**: Nothing (new file, no conflicts)
**Estimated scope**: ~300-400 lines new

**Tasks**:
1. Create `CN/TypeChecking/Simplify.lean` with:
   - `simplifyTerm : AnnotTerm → AnnotTerm` — recursive term simplifier
   - `simplifyConstraint : LogicalConstraint → LogicalConstraint`
2. Implement simplification rules (ordered by impact):
   - Constant folding (arithmetic identities)
   - Boolean simplification
   - Equality simplification (`Eq(x,x)->true`)
   - Accessor reduction (`StructMember(Struct(...), m) -> field`)
   - Cast folding
   - SizeOf evaluation to concrete literal
   - Struct eta-reduction
3. **Integration point** (coordinate with leader): Add `simplify` call in `Monad.lean:provable` before solver query.

**CN ref**: `simplify.ml` (~696 lines)

### WP-C: Derived Constraints (pointer_facts)
**Files owned**: NEW `CN/TypeChecking/DerivedConstraints.lean`
**Depends on**: Nothing (new file)
**Estimated scope**: ~150-200 lines new

**Tasks**:
1. Create `CN/TypeChecking/DerivedConstraints.lean` with:
   - `derivedLc1 : Resource → List LogicalConstraint` — single-resource facts
     - For `Owned(ct)(ptr)`: `hasAllocId(ptr)`, `addr(ptr) <= addr(ptr) + sizeof(ct)`
   - `derivedLc2 : Resource → Resource → List LogicalConstraint` — pair facts
     - For two `Owned`: `upper(p2) <= addr(p1) || upper(p1) <= addr(p2)` (non-overlap/separation)
   - `deriveConstraints : Resource → List Resource → List LogicalConstraint`
2. **Integration point** (coordinate with leader): Patch `Monad.lean:addR` to call `deriveConstraints`.

**CN ref**: `resource.ml:25-71`, `typing.ml:415-427`

### WP-D: Alpha-Renaming Fix
**Files owned**: `CN/Types/Constraint.lean`, `CN/Types/Term.lean`
**Depends on**: Nothing
**Estimated scope**: ~30-50 lines changed

**Tasks**:
1. Add `Term.freshSym` or `Term.alphaRename` utility to `Term.lean`
2. Fix `LogicalConstraint.subst` in `Constraint.lean:44-46` to alpha-rename forall-bound variable when it clashes with substitution domain
**CN ref**: `IT.suitably_alpha_rename`

### WP-E: Test Development
**Files owned**: `tests/cn/` (new test files only)
**Depends on**: Nothing (tests written before features land)
**Estimated scope**: ~20-30 new test files

**Tasks**:
1. Add tests for each gap being fixed (see test list in Execution Architecture)
2. Cross-reference CN's test suite in `tmp/cn/tests/` for additional coverage
3. Mark tests with `.fail.c` / `.smt-fail.c` suffixes appropriately

---

## Wave 2: Core Capabilities (Parallel, After Wave 1)

All packages touch **different files** and can run concurrently.

### WP-F: Resource Inference Expansion
**Files owned**: `CN/TypeChecking/Inference.lean`
**Depends on**: WP-A (SMT encoding), WP-C (derived constraints)
**Estimated scope**: ~300 lines changed/added

**Tasks**:
1. **QPredicate support**: `qpredicateRequest` (CN ref: `resourceInference.ml:253-375`)
2. **Array unpack**: `unpackArrayResource` (CN ref: `pack.ml:24-39`)
3. **Array repack**: `tryRepackArray` (CN ref: `pack.ml:47-51`)
4. **Padding handling**: Extend struct unpack/repack (CN ref: `pack.ml:66-124`)
5. **check_live_alloc**: Alloc liveness (CN ref: `resourceInference.ml:515-570`)
6. **Strengthen SMT slow path**: Multiple candidates + solver iargs (CN ref: `resourceInference.ml:175-221`)
7. **do_unfold_resources fixpoint**: Loop until stable (CN ref: `typing.ml:548-657`)

### WP-G: Pointer Memops + RMW Fix
**Files owned**: `CN/TypeChecking/Expr.lean`, `CN/TypeChecking/Action.lean`
**Depends on**: WP-A, WP-F
**Estimated scope**: ~200-250 lines added

**Tasks**: PtrEq/PtrNe, PtrLt/Gt/Le/Ge, Ptrdiff, IntFromPtr, PtrFromInt, Copy_alloc_id, Fix test 044

### WP-H: Pure Expression Cases
**Files owned**: `CN/TypeChecking/Pexpr.lean`
**Depends on**: WP-A
**Estimated scope**: ~100-150 lines added

**Tasks**: Carray, Cnil/Ccons, ByteFromInt/IntFromByte, ctype_width, PEmemberof

### WP-I: Ghost Statements (Predicate-Free)
**Files owned**: NEW `CN/TypeChecking/GhostStatement.lean`
**Depends on**: WP-F
**Estimated scope**: ~200-250 lines new

**Tasks**: `have`, `assert`, `instantiate`, `extract`, `split_case`, `print`
Fail explicitly for: `pack`/`unpack`/`unfold`/`apply`/`inline`/`to_from_bytes`

### WP-J: Ghost Parameters
**Files owned**: `CN/Parser.lean`, `CN/Types/Spec.lean`, `CN/TypeChecking/Spine.lean`
**Depends on**: Nothing structurally
**Estimated scope**: ~100-150 lines changed

**Tasks**: Extend FunctionSpec, parse ghost params, handle in spine, parse at call sites

---

## Wave 3: Extended Features (Parallel, After Wave 2)

### WP-K: Loop Invariants
**Files owned**: `CN/TypeChecking/Params.lean`, `CN/TypeChecking/Check.lean`
**Depends on**: WP-I
**Tasks**: Parse loop invariants, verify on entry, maintain through body

### WP-L: wellTyped Checking
**Files owned**: NEW `CN/TypeChecking/WellTyped.lean`
**Depends on**: WP-A
**Tasks**: ensureBaseType, inferTerm/checkTerm, checkMemValue/checkObjectValue

### WP-M: Global Variables + `accesses`
**Files owned**: `CN/Parser.lean`, `CN/TypeChecking/Check.lean`
**Depends on**: Wave 2
**Tasks**: Parse `accesses` clause, generate implicit Owned for globals

---

## Leader Integration Points

**After Wave 1**:
- Patch `Monad.lean:provable` to call `Simplify.simplify` (from WP-B)
- Patch `Monad.lean:addR` to call `deriveConstraints` (from WP-C)
- Update module imports in `TypeChecking.lean` aggregator
- Run `make test-cn` to verify

**After Wave 2**:
- Integrate `GhostStatement.lean` into `Expr.lean` Esseq path (from WP-I)
- Update module imports
- Run `make test-cn` to verify expanded coverage

**After Wave 3**:
- Final integration and test pass
- Update `CLAUDE.md` with new capabilities
- Run full `make test-cn` and verify all expected tests pass

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

## Execution Priority (If Resource-Constrained)

1. **WP-A task 1** (NoSMT fix) — Critical correctness bug
2. **WP-C** (pointer_facts) — Core separation logic
3. **WP-A tasks 2-6** (SMT encoding) — Foundation for everything
4. **WP-B** (simplification) — Performance enabler
5. **WP-F** (resource inference) — Verification power
6. **WP-G** (pointer memops) — Test coverage
7. **WP-D** (alpha-renaming) — Correctness fix
8. **WP-H, WP-I** (pexpr, ghost stmts) — Feature expansion
9. **WP-J, WP-K** (ghost params, loops) — Common C patterns
10. **WP-L, WP-M** (wellTyped, globals) — Completeness
