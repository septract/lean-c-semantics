# C-to-Lean

> **Warning**: This project contains AI-generated code. Review carefully before use.

A tool for translating C code into Lean 4 for formal verification. Uses [Cerberus](https://github.com/rems-project/cerberus) as a C frontend to generate an intermediate representation, which is then parsed and interpreted in Lean.

## Status

**Work in progress.** Current functionality:

- **JSON Parser**: Parses Cerberus Core IR into Lean AST (100% success on 5500+ test files)
- **Pretty-printer**: Reproduces Cerberus output format (99% match rate)
- **Memory model**: Concrete memory with allocation-ID provenance, bounds checking, and UB detection
- **Interpreter**: Executes Core IR programs (100% match on minimal tests, 91% on CI suite)

## Pipeline

```
C source → Cerberus → Core IR (JSON) → Lean Parser → Lean AST
```

## Building

Requires: Lean 4, OCaml 4.14.1 (for Cerberus)

```bash
make lean      # Build Lean project
make cerberus  # Build Cerberus (requires opam)
make test      # Run tests
```

## License

See individual components for licensing.
