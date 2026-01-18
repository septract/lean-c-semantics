# Lean C Semantics

A Lean 4 implementation of C semantics via [Cerberus](https://github.com/rems-project/cerberus). Cerberus compiles C to its Core intermediate representation; this project parses and executes Core in Lean, enabling formal reasoning about C programs.

> **Note**: This codebase was developed through AI-human collaboration using Claude Code. Review accordingly.

## Status

**Interpreter working.** Test results (2026-01-18):

| Test Suite | Match Rate |
|------------|------------|
| Minimal (76 tests) | 100% |
| Debug (65 tests) | 100% |
| Full CI (~760 tests) | 98% |

The remaining 2% are due to: unimplemented I/O builtins (printf), Cerberus-specific features, and expected semantic differences (unsequenced race detection).

## Components

- **JSON Parser**: Parses Cerberus Core IR into Lean AST (100% success on 5500+ test files)
- **Pretty-printer**: Reproduces Cerberus output format (99% match rate)
- **Memory model**: Concrete memory with allocation-ID provenance, bounds checking, UB detection
- **Interpreter**: Small-step interpreter matching Cerberus semantics

## Pipeline

```
C source → Cerberus → Core IR (JSON) → Lean Parser → Lean AST → Lean Interpreter
```

## Building

Requires: Lean 4 (via elan), OCaml 4.14.1 (for Cerberus), `timeout` command (for tests)

On macOS: `brew install coreutils` (provides `gtimeout` which is symlinked to `timeout`)

```bash
# First-time setup
make cerberus-setup  # Create OCaml switch and build Cerberus

# Build
make lean            # Build Lean project

# Test
make test            # Run quick tests (unit + interpreter)
```

## Documentation

- `CLAUDE.md` - Project overview and development guide
- `TODO.md` - Current status and known issues
- `docs/` - Design documents and audits
