# Lean C Semantics

> ## ⚠️ This repository is archived
>
> This project has been superseded by **[OathTech/cerberus-lean](https://github.com/OathTech/cerberus-lean)**.
> cerberus-lean is a from-scratch successor, not a continuation of this code, and its design is
> fundamentally different:
>
> - **This repo** hand-translates the Core interpreter and memory model into Lean, and runs on Core IR
>   exported as JSON from a lightly patched Cerberus. Correspondence with Cerberus is maintained by
>   manual audit.
> - **cerberus-lean** is a fork of Cerberus itself. The Lean semantics are *generated* from the same Lem
>   model that produces the OCaml implementation, with hand-written "seam" files for the memory model,
>   non-determinism runner, and implementation-defined behaviour. Only the C parser stays in OCaml; the
>   Lean side performs desugaring, typing, elaboration to Core, and execution, and is validated
>   differentially against the OCaml engine.
>
> This repository is retained for reference only and will not receive further updates, bug fixes, or
> pull request reviews. Please direct new work, issues, and contributions to cerberus-lean.

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

## Quick Start (Docker)

The easiest way to use CerbLean is via Docker:

```bash
# Pull the image
docker pull ghcr.io/septract/lean-c-semantics:main

# Run on a C file
docker run --rm -v "$(pwd):$(pwd)" -w "$(pwd)" ghcr.io/septract/lean-c-semantics:main program.c
```

For convenience, add an alias to your shell config:

```bash
alias cerblean='docker run --rm -v "$(pwd):$(pwd)" -w "$(pwd)" ghcr.io/septract/lean-c-semantics:main'
```

Then use it like a regular command:

```bash
cerblean program.c              # Execute and show result
cerblean --batch program.c      # Machine-readable output
cerblean --cerberus program.c   # Run Cerberus only (for comparison)
cerblean --json program.c       # Output Core IR as JSON
cerblean --help                 # Show all options
```

## Building from Source

Requires: Lean 4 (via elan), OCaml (for Cerberus, version configured in Makefile), `timeout` command (for tests)

On macOS: `brew install coreutils` (provides `gtimeout` which is symlinked to `timeout`)

```bash
# First-time setup
make cerberus-setup  # Create OCaml switch and build Cerberus

# Build
make lean            # Build Lean project

# Test
make test            # Run quick tests (unit + interpreter)
```

### Building the Docker Image Locally

```bash
docker build -t cerblean .
docker run --rm -v "$(pwd):$(pwd)" -w "$(pwd)" cerblean program.c
```

## Documentation

- `CLAUDE.md` - Project overview and development guide
- `TODO.md` - Current status and known issues
- `docs/` - Design documents and audits
