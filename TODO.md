# TODO - C-to-Lean Project

## Current Phase: 2 - Core JSON Export & Parser (nearly complete)

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
- [ ] Add pretty-printer for round-trip validation

### Phase 2: Core JSON Export & Parser
- [x] Create `json_core.ml` in Cerberus for JSON serialization
- [x] Add `--json_core_out` flag to Cerberus driver
- [x] Implement JSON parser in Lean (**100% success rate on 1817 test files**)
- [~] Write pretty-printer in Lean matching Cerberus format (in progress)
- [ ] Validate: JSON parse → pretty-print == Cerberus pretty-print

#### Pretty-printer remaining work:
1. ~~**Fill in JSON parser TODOs**~~ ✓ Complete - all TODOs in Parser.lean resolved:
   - Fixed `OVfloating` with proper `FloatingValue` type (nan, posInf, negInf, unspecified)
   - Fixed `OVpointer` to parse NULL, Cfunction, and concrete pointer strings
   - Fixed `OVstruct` to parse member arrays
   - Fixed `PEarray_shift` to parse ctype field

2. **Fix discrepancies in first 10 CI test files** (comparing Lean vs Cerberus output):
   - `unseq` separator: Lean uses ` ||| `, Cerberus uses `, ` inside `unseq(...)`
   - `0009-cond-pointer.c`: Cerberus outputs comments like `-- Aggregates --` we don't have
   - Some whitespace/indentation differences (may need closer inspection)
   - Current status: 3/10 passing (0001, 0004, 0006)

3. **Run on larger test set** - validate pretty-printer on full CI suite (~100+ files)

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
