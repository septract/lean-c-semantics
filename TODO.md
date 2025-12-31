# TODO - C-to-Lean Project

## Current Phase: 4 - Core Interpreter (next)

### Phase 0 & 1 Complete
- [x] Initialize Lean 4 project in `lean/` directory
- [x] Set up Lake build system
- [x] Create basic project structure (Core, Parser, Memory, Semantics, Theorems, Test)

## Roadmap

### Phase 1: Core AST in Lean ✓
- [x] Define `ObjectType` (integer, floating, pointer, array, struct, union)
- [x] Define `BaseType` (unit, boolean, ctype, list, tuple, object, loaded)
- [x] Define `Binop` (arithmetic and logical operators)
- [x] Define `Value` types (ObjectValue, LoadedValue, Value)
- [x] Define `Pexpr` (pure expressions)
- [x] Define `Expr` (effectful expressions)
- [x] Define `File` (program structure)
- [x] Add pretty-printer for round-trip validation

### Phase 2: Core JSON Export & Parser
- [x] Create `json_core.ml` in Cerberus for JSON serialization
- [x] Add `--json_core_out` flag to Cerberus driver
- [x] Add `--pp_core_compact` flag to Cerberus for compact output (easier diffing)
- [x] Implement JSON parser in Lean (**100% success rate on 5500+ test files**)
- [x] Write pretty-printer in Lean matching Cerberus format (**99% match rate**)
- [x] Validate: JSON parse → pretty-print == Cerberus pretty-print (target: 90%+) ✓

#### Pretty-printer status:
Current match rate: **99%** (1809/1817 files on full test suite, 100% on CI tests)

Fixed issues:
- [x] NULL type formatting (no quotes around type)
- [x] memop formatting (`memop(PtrEq, ...)` not `PtrEq(...)`)
- [x] Struct field syntax (`=` not `:` separator)
- [x] Function pointer type printing (C declaration syntax)
- [x] ccall trailing comma
- [x] are_compatible spacing
- [x] Tag definition format (`def struct NAME :=`)
- [x] Object type format (`struct tag` not `struct(tag)`)

Remaining discrepancies: See `docs/PP_DISCREPANCIES.md` for full categorization and checklist.

### Phase 3: Memory Model Interface ✓
- [x] Define `MemoryOps` type class with core operations
- [x] Implement `Concrete` memory model (allocation-ID provenance)
- [x] Add memory model unit tests (`make test-memory`)

See `docs/MEMORY_MODEL.md` for design details.

### Phase 3.5: Test Infrastructure Cleanup ✓
- [x] Create `docs/TESTING.md` with unified test documentation
- [x] Reorganize test files into `CToLean/Test/` subdirectory
- [x] Add `make test-unit` target for Cerberus-independent testing
- [ ] Consider adding CI workflow (`.github/workflows/test.yml`) - deferred (private submodule)
- [ ] Prepare test harness for interpreter differential testing - Phase 5

### Phase 4: Core Interpreter
- [ ] Implement pure expression evaluation
- [ ] Implement effectful expression execution
- [ ] Implement pattern matching
- [ ] Implement procedure calls
- [ ] Handle control flow

### Phase 5: Validation Framework
- [ ] Create Cerberus oracle wrapper
- [ ] Implement result comparison
- [ ] Set up test runner for `tests/ci/`
- [ ] Target: 90%+ pass rate on sequential tests

### Phase 6: UB-Freeness Theorems
- [ ] Define `UBFree` predicate
- [ ] Implement theorem statement generator
- [ ] Create example theorems for simple programs

## Out of Scope (Future Work)
- Concurrent semantics (`Epar`, `Eunseq`)
- PNVI/CHERI memory models
- Variadic functions
- Floating point operations
- Full C standard library

## Low Priority
- [ ] Fix Cerberus `--pp_core_out` flag to work without requiring `--pp=core`
- [ ] Audit all type definitions for hacky special cases - use proper type system representations
  - Example: `FloatingValue` was changed from `{ val : Float }` to an inductive type with `nan`, `posInf`, `negInf`, `unspecified` constructors
  - Review: `IntegerValue`, `PointerValue`, `MemValue`, and any other types that may have special runtime values
- [ ] Serialize `mem_value` as structured JSON instead of string
  - Currently OVstruct/OVunion member values are serialized as pp_mem_value strings
  - Would require adding json_mem_value to Impl_mem interface and implementing in each memory model
  - For now, Lean parses the string representation which works for pretty-printing but loses structure

## Notes
- See `docs/DETAILED_PLAN.md` for full implementation details
- Using Cerberus as git submodule in `cerberus/`
- Focus on sequential Core fragment initially
