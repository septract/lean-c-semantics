# TODO - C-to-Lean Project

## Current Phase: 1 - Core AST in Lean

### Phase 0 Complete
- [x] Initialize Lean 4 project in `lean/` directory
- [x] Set up Lake build system
- [x] Create basic project structure (Core, Parser, Memory, Semantics, Theorems, Test)

## Roadmap

### Phase 1: Core AST in Lean
- [ ] Define `core_object_type` (integer, floating, pointer, array, struct, union)
- [ ] Define `core_base_type` (unit, boolean, ctype, list, tuple, object, loaded)
- [ ] Define `binop` (arithmetic and logical operators)
- [ ] Define `value` types
- [ ] Define `generic_pexpr` (pure expressions)
- [ ] Define `generic_expr` (effectful expressions)
- [ ] Define `generic_file` (program structure)

### Phase 2: Core JSON Export & Parser
- [ ] Add `[@@deriving yojson]` to Cerberus Core types
- [ ] Add `--json-core-out` flag to Cerberus driver
- [ ] Implement JSON parser in Lean
- [ ] Test on simple Core outputs

### Phase 3: Memory Model Interface
- [ ] Define `Memory` type class with core operations
- [ ] Implement `Simple` memory model (integer addresses)
- [ ] Implement `Concrete` memory model (allocation IDs)

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

## Notes
- See `docs/DETAILED_PLAN.md` for full implementation details
- Using Cerberus as git submodule in `cerberus/`
- Focus on sequential Core fragment initially
