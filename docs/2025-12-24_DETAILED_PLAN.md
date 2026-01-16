# Lean C Semantics - Implementation Plan

## Project Goal
Translate C code into Lean 4 code that captures C semantics, enabling formal reasoning about C programs in Lean.

## Research Summary

### Cerberus Architecture (from codebase exploration)
- **Core IR**: Defined in `frontend/ott/core-ott/core.ott` (~600 lines) with embedded Lem code
- **Operational Semantics**:
  - `frontend/model/core_run.lem` (~1655 lines) - main execution
  - `frontend/model/core_eval.lem` (~1198 lines) - expression evaluation
  - `frontend/model/mem_common.lem` (~705 lines) - memory model interface
- **Memory Models**: Multiple implementations in `memory/` (concrete ~3015 LoC, vip ~1441 LoC)
- **Sequentialization Pass**: `frontend/model/core_sequentialise.lem` converts concurrent Core to sequential
- **Existing Coq Work**: `coq/` directory contains Lem-generated Coq for CHERI memory model
- **Tests**: 5500+ C test files in `tests/`

### Key Cerberus Files for Core AST
```
cerberus/frontend/ott/core-ott/core.ott     # Core AST grammar (Ott + embedded Lem)
cerberus/frontend/model/core.lem            # Core AST Lem types
cerberus/ocaml_frontend/pprinters/pp_core.ml # Core pretty-printer
```

### Tooling Status
- **Ott**: Has backends for Coq, HOL4, Isabelle, OCaml, LaTeX. No Lean backend.
- **Lem**: Has backends for Coq, HOL4, Isabelle, OCaml. No Lean backend. Note: "The Coq backend isn't used much because the Lem language isn't a great match for Coq."
- **Cerberus**: Can output pretty-printed Core via `--pp-core-out`

---

## Approach Evaluation

### Option A: Create Lem Backend for Lean 4
**Pros**: Maximizes code reuse; directly translates existing semantics
**Cons**: Large undertaking; Lem-to-Coq experience suggests poor fit; Lem not actively developed

### Option B: Create Ott Backend for Lean 4
**Pros**: Gets Core AST types automatically; Ott is simpler than Lem
**Cons**: Only handles AST, not semantics; still need to port operational semantics manually

### Option C: Manual Translation with Cerberus as Oracle (Recommended)
**Pros**:
- Full control over Lean code quality and idioms
- Can use Lean 4 best practices (Std.Do, etc.)
- Decoupled from Cerberus toolchain
- Can start with sequential fragment
- Validation via differential testing against Cerberus

**Cons**: More initial work; potential for translation errors

### Option D: Translate Coq to Lean
**Pros**: Some types already in Coq (from existing CHERI work)
**Cons**: Coq code is auto-generated and non-idiomatic; limited coverage

## Recommended Approach: Option C

### Rationale
1. Project goals emphasize being "totally decoupled from Cerberus"
2. Lem/Ott backends are significant work for uncertain benefit
3. Manual translation allows idiomatic Lean 4 code
4. Can leverage `core_sequentialise.lem` pass to focus on sequential semantics first
5. Differential testing against Cerberus provides validation

---

## Implementation Roadmap

### Phase 0: Infrastructure Setup
1. Initialize Lean 4 project structure in `lean/` directory
2. Set up build system (Lake)
3. Create test harness for differential testing

### Phase 1: Core AST in Lean
**Goal**: Define Core AST types in Lean 4

**Key types to translate from `core.ott`**:
- `core_object_type` - C object types (integer, floating, pointer, array, struct, union)
- `core_base_type` - Core base types (unit, boolean, ctype, list, tuple, object, loaded)
- `binop` - Binary operators
- `value` - Core values
- `generic_pexpr` - Pure expressions
- `generic_expr` - Effectful expressions
- `generic_file` - Core program file

**Files to create**:
```
lean/CerbLean/Core/Types.lean      # Basic types
lean/CerbLean/Core/Expr.lean       # Expression AST
lean/CerbLean/Core/Value.lean      # Value representations
lean/CerbLean/Core/File.lean       # Program structure
```

### Phase 2: Core JSON Export & Parser
**Goal**: Add JSON export to Cerberus and parse it in Lean

**Approach**: Add JSON serialization to Cerberus Core types using yojson/ppx_deriving_yojson

**Cerberus modifications** (in `cerberus/` submodule):
1. Add `[@@deriving yojson]` to Core AST types in `ocaml_frontend/generated/core.ml`
2. Add `--json-core-out` flag to driver
3. Serialize Core file to JSON format

**Lean implementation**:
```
lean/CerbLean/Parser/Json.lean     # JSON parsing utilities
lean/CerbLean/Parser/Core.lean     # Core-specific JSON parsing
lean/CerbLean/Pretty/Core.lean     # Pretty-printer matching Cerberus format
```

**Validation approach**:
Round-trip validation via pretty-printing:
1. Run `cerberus --json-core-out=out.json --pp-core-out=expected.core input.c`
2. Parse `out.json` in Lean → Lean AST
3. Pretty-print Lean AST → `actual.core`
4. Assert `expected.core == actual.core`

This validates both the parser and AST structure are correct without needing to run the interpreter.

### Phase 3: Memory Model Interface
**Goal**: Define abstract memory model with smooth upgrade path

**Design for incremental complexity**:

```
                    ┌─────────────────────────────────┐
                    │     Memory Interface (class)     │
                    │  - alloc, free, load, store     │
                    │  - pointer arithmetic           │
                    └─────────────────────────────────┘
                                    │
                    ┌───────────────┼───────────────┐
                    │               │               │
              ┌─────▼─────┐  ┌─────▼─────┐  ┌─────▼─────┐
              │  Simple   │  │ Concrete  │  │   PNVI    │
              │ (no prov) │  │ (alloc ID)│  │ (full)    │
              └───────────┘  └───────────┘  └───────────┘
```

**Level 1 - Simple Memory** (initial target):
- Pointers are just integers (addresses)
- No provenance tracking
- UB on out-of-bounds access

**Level 2 - Concrete Memory** (matches Cerberus default):
- Allocation IDs for provenance
- Spatial bounds checking
- Dangling pointer detection

**Level 3 - PNVI** (future, if needed):
- Full provenance-not-via-integers semantics
- Exposure tracking

**Key operations from `mem_common.lem`**:
- `create` / `alloc` - allocate memory
- `kill` - deallocate memory
- `load` - read from memory
- `store` - write to memory
- Pointer arithmetic, comparison, casting

**Files to create**:
```
lean/CerbLean/Memory/Interface.lean  # Type class defining memory operations
lean/CerbLean/Memory/Simple.lean     # Level 1: integer addresses
lean/CerbLean/Memory/Concrete.lean   # Level 2: allocation-ID provenance
```

**Upgrade strategy**: Code using the `Memory` type class works with all implementations. Start proofs with Simple, upgrade to Concrete when needed for specific UB detection.

### Phase 4: Core Interpreter in Lean
**Goal**: Implement operational semantics for sequential Core

**Key components from `core_run.lem` and `core_eval.lem`**:
- Pure expression evaluation
- Effectful expression evaluation (with memory operations)
- Pattern matching
- Procedure calls
- Control flow

**Approach**: Use a monadic interpreter (State + Error + IO)

**Files to create**:
```
lean/CerbLean/Semantics/Eval.lean      # Pure expression evaluation
lean/CerbLean/Semantics/Run.lean       # Effectful execution
lean/CerbLean/Semantics/State.lean     # Execution state
lean/CerbLean/Semantics/Monad.lean     # Execution monad
```

### Phase 5: Validation Framework
**Goal**: Differential testing against Cerberus

**Approach**:
1. Run Cerberus on C file, capture Core output and execution result
2. Parse Core in Lean interpreter
3. Execute in Lean interpreter
4. Compare results

**Start with**: `tests/ci/` test suite (simple tests like `0001-emptymain.c` through `0021-fact.c`)

**Files to create**:
```
lean/CerbLean/Test/Oracle.lean         # Run Cerberus as oracle
lean/CerbLean/Test/Compare.lean        # Compare execution results
lean/CerbLean/Test/Runner.lean         # Test harness
```

---

## Scope Limitations (Initial Version)

### In Scope
- Sequential Core only (use `core_sequentialise` pass)
- Basic memory model (concrete, no PNVI/CHERI)
- Core subset: arithmetic, pointers, arrays, structs
- Single translation unit

### Out of Scope (Future Work)
- Concurrent semantics (`Epar`, `Eunseq`, etc.)
- Complex memory models (PNVI, CHERI)
- Variadic functions
- Floating point (can stub)
- Full C standard library

---

## Validation Strategy

### Level 1: Unit Tests
- Test AST parsing on hand-crafted examples
- Test individual semantic operations

### Level 2: Differential Testing
- Run Cerberus CI tests through both interpreters
- Compare execution results (return value, UB detection)
- Target: Pass all `tests/ci/*.c` that don't involve concurrency

### Level 3: Cross-Validation
- Compare against CompCert semantics where applicable
- Manual review of key semantic rules

---

## Key Dependencies

### Lean 4 Libraries
- `Std` - Standard library, including `Std.Do` for monadic programming
- Possibly `Mathlib` for numeric reasoning

### External Tools
- Cerberus (via submodule, already added)
- C preprocessor (for C → Core pipeline)

---

## Success Criteria

1. **Parser**: Can parse Core output for all `tests/ci/*.c` files
2. **Interpreter**: Produces same results as Cerberus on 90%+ of sequential tests
3. **Documentation**: Clear mapping between Cerberus Core and Lean representation

---

## Decisions Made

1. **Core Export**: Add JSON export to Cerberus (modify Cerberus submodule)
2. **Memory Model**: Start simple, with type class abstraction for smooth upgrade to Concrete/PNVI
3. **Target Programs**: Focus on Cerberus test suite (~5500 tests)
