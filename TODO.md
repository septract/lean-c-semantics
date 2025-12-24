# TODO - C-to-Lean Project

## Current Phase: 2 - Core JSON Export & Parser

### Phase 0 & 1 Complete
- [x] Initialize Lean 4 project in `lean/` directory
- [x] Set up Lake build system
- [x] Create basic project structure (Core, Parser, Memory, Semantics, Theorems, Test)

## Roadmap

### Phase 1: Core AST in Lean
- [x] Define `ObjectType` (integer, floating, pointer, array, struct, union)
- [x] Define `BaseType` (unit, boolean, ctype, list, tuple, object, loaded)
- [x] Define `Binop` (arithmetic and logical operators)
- [x] Define `Value` types (ObjectValue, LoadedValue, Value)
- [x] Define `Pexpr` (pure expressions)
- [x] Define `Expr` (effectful expressions)
- [x] Define `File` (program structure)
- [ ] Add pretty-printer for round-trip validation

### Phase 2: Core JSON Export & Parser
- [ ] Add `[@@deriving yojson]` to Cerberus Core types
- [ ] Add `--json-core-out` flag to Cerberus driver
- [ ] Implement JSON parser in Lean
- [ ] Write pretty-printer in Lean matching Cerberus format
- [ ] Validate: JSON parse → pretty-print == Cerberus pretty-print

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
