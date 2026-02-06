# TODO - CerbLean Project

## Current Status (2026-02-05)

### Interpreter: 100% match rate
- Minimal test suite: 93 tests (91 runnable with --nolibc), 100% match
- Debug test suite: 86 tests, 100% match
- Unsequenced race detection: 16 tests, fully supported

### CN Type Checker: 16/28 tests passing
- 16 tests pass (simple owned, write, arithmetic, etc.)
- 9 tests fail (mostly SMT postcondition, struct access, conditional resources)
- 3 expected-fail tests: 2 pass, 1 fails (resource leak detection incomplete)

### Parser: 100% success rate on 5500+ files

### Pretty-Printer: 99% match rate on full test suite

## Known Issues

### CN Type Checker Gaps
- Struct member access not yet implemented
- Conditional resource handling incomplete
- Some SMT postcondition checks fail (return value reasoning)
- Resource leak detection not complete for all cases
- Quantified predicates not yet supported

### Interpreter Gaps
- `pure_memop` — 5 tests (cast_*_byte.exec)
- `builtin_printf` and other I/O builtins — ~80 tests
- `par` (parallel execution) — 4 tests
- Union active member tracking — type punning shows DIFF not MISMATCH

### Cerberus JSON Export
- All fields now properly serialized (symbol digest, PEconstrained, calling_convention, loop_attributes, visible_objects_env)
- `BEq Sym` matches CN's `symbolEqual` (digest + id)

### Cerberus Non-determinism
Tests pr34099 and pr52286 show non-deterministic behavior in Cerberus itself (not our bug).

## Future Work

### CN Type Checker Completion
- [ ] Struct member access (CN `memberShift` + `Owned` for struct fields)
- [ ] Conditional resource handling in branches
- [ ] SMT return value reasoning
- [ ] Resource leak detection (leftover resources at function exit)
- [ ] Quantified predicates (`each`)
- [ ] Predicate definitions and unfolding/packing

### Driver Layer & I/O Builtins
- [ ] Implement `Formatted.printf` with format string parsing
- [ ] Add filesystem state for stdout/stderr
- [ ] Support `builtin_vprintf`, `builtin_vsnprintf`, etc.
- **Affected tests:** ~80 tests that use printf

### Program Verification
- [ ] More verified programs via GenProof pipeline
- [ ] Symbolic reasoning for programs with inputs

### Out of Scope
- Concurrent semantics (`Epar`)
- PNVI/CHERI memory models
- Full C standard library

## Completed Phases

### Phase 1: Core AST in Lean ✓
- [x] Define all Core IR types
- [x] Add pretty-printer for round-trip validation

### Phase 2: Core JSON Export & Parser ✓
- [x] Create `json_core.ml` in Cerberus for JSON serialization
- [x] Implement JSON parser in Lean (100% success rate)
- [x] Write pretty-printer matching Cerberus format (99% match rate)
- [x] Symbol digest export and strict parsing

### Phase 3: Memory Model ✓
- [x] Concrete memory model with allocation-ID provenance
- [x] Memory model unit tests
- [x] Audit against Cerberus `impl_mem.ml`

### Phase 4: Core Interpreter ✓
- [x] Small-step interpreter with explicit stack/continuations
- [x] All Core expression types (Eaction, Ememop, Eccall, etc.)
- [x] Unsequenced race detection (Eunseq with neg transformation)
- [x] 100% match rate on minimal/debug suites

### Phase 5: Validation Framework ✓
- [x] Differential testing against Cerberus
- [x] Csmith fuzz testing
- [x] creduce minimization workflow

### Phase 6: CN Type System (In Progress)
- [x] CN types (base types, index terms, resources, specs)
- [x] CN spec parser (from magic annotations)
- [x] Typing monad with SMT integration
- [x] Resource inference (two-phase matching)
- [x] Basic type checking (16/28 tests)
- [ ] Struct access, conditional resources, full postcondition checking

## Test Commands

```bash
make test              # Quick tests: unit + 100 parser + 100 PP + interp + genproof
make test-cn           # CN verification tests (28 tests)
make test-cn-unit      # CN unit tests only (fast, no Cerberus)
make test-memory       # Memory model unit tests
make test-parser-full  # Full parser test (~5500 files)
make test-pp-full      # Full pretty-printer test
```

## Documentation
- `docs/2026-01-01_MEMORY_AUDIT.md` - Memory model Cerberus correspondence
- `docs/2025-12-31_TESTING.md` - Test infrastructure guide
- `docs/2026-01-20_CN_TYPECHECKING_AUDIT.md` - CN type checker audit
- `docs/2026-02-01_CN_ANTIPATTERN_AUDIT.md` - Antipattern audit (48 violations found)
- `CLAUDE.md` - Project overview and conventions
