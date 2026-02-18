# Cerberus Code Coverage Instrumentation

Created: 2026-02-14

## Motivation

We want to measure which parts of Cerberus's OCaml code are exercised by our test suites (`tests/minimal/`, `tests/debug/`, `tests/float/`, and the Cerberus CI suite). This tells us which interpreter paths, memory model branches, and evaluation cases are untested — enabling targeted test development.

The primary focus is OCaml coverage of the **original Cerberus** code, not our Lean code, because we need to ensure our test suite covers the Cerberus semantics we're mirroring.

## Tool: bisect_ppx

**bisect_ppx** is the only maintained OCaml code coverage tool. Key properties:

- **Expression-level** coverage (more granular than line coverage — multiple expressions per line are tracked independently)
- Clean dune integration via `(instrumentation (backend bisect_ppx))` stanzas
- HTML reports with source-level highlighting
- Cobertura XML output for CI integration
- Natural multi-run merging via uniquely-named `.coverage` files
- Zero impact on normal builds when `--instrument-with` is not passed

**How it works**: bisect_ppx is a PPX preprocessor that inserts counter-increment calls into the AST at instrumentation points (`if/then/else` branches, `match` arms, `try/with`, sequence points). At program exit (`at_exit`), accumulated hit counts are written to `.coverage` files. The `bisect-ppx-report` tool generates reports from these files.

**Alternatives considered**: There are no other maintained OCaml coverage tools. The OCaml compiler has no built-in coverage support (unlike GCC's gcov). Landmarks (already partially integrated in Cerberus) is a profiling tool (time spent), not coverage.

## Implementation Plan

### Step 1: Install bisect_ppx in the Cerberus opam switch

```bash
cd cerberus && opam install --switch=. bisect_ppx
```

If this fails due to ppxlib version constraints (bisect_ppx 2.8.3 requires `ppxlib >= 0.28.0 & < 0.36.0`), pin to the master branch which has removed this upper bound:

```bash
cd cerberus && opam pin add bisect_ppx --dev-repo
```

### Step 2: Add instrumentation stanzas to Cerberus dune files

Add `(instrumentation (backend bisect_ppx))` to each library/executable:

| File | Library/Executable | What it covers |
|------|--------------------|----------------|
| `cerberus/ocaml_frontend/dune` | `cerb_frontend` | core_eval, core_reduction, all Lem-generated semantics |
| `cerberus/memory/concrete/dune` | `mem_concrete` | impl_mem.ml (concrete memory model) |
| `cerberus/backend/common/dune` | `cerb_backend` | Backend utilities |
| `cerberus/backend/driver/dune` | `main` executable | Main driver |
| `cerberus/util/dune` | `cerb_util` | Utility library |

Example change for `cerberus/ocaml_frontend/dune`:
```sexp
(library
 (name cerb_frontend)
 (public_name cerberus-lib.frontend)
 (synopsis "Cerberus frontend")
 (flags (:standard -w @8@11@12-9-27-33-67))
 (modules :standard \ pp_naive_memory pp_symbolic pp_constraints pp_cmm pp_sb)
 (virtual_modules impl_mem)
 (libraries unix lem pprint cerb_util sibylfs)
 (instrumentation (backend bisect_ppx)))
```

When `--instrument-with bisect_ppx` is NOT passed to dune, this stanza is completely ignored — bisect_ppx doesn't even need to be installed for normal builds.

### Step 3: Create `cerberus/dune-workspace.coverage`

Following the existing `dune-workspace.profiling` pattern:

```sexp
(lang dune 3.13)

(context default)

(context
  (default
    (name coverage)
    (instrument_with bisect_ppx)))
```

### Step 4: Wire coverage into the Cerberus Makefile

Add a `COVERAGE` flag analogous to the existing `PROFILING` flag:

```makefile
ifdef COVERAGE
    DUNEFLAGS += --workspace=dune-workspace.coverage
endif
```

### Step 5: Create a coverage test script (`scripts/test_coverage.sh`)

This script:
1. Builds Cerberus with coverage instrumentation
2. Runs test suites through the instrumented binary
3. Generates HTML report and terminal summary

### Step 6: Add top-level Makefile targets

```makefile
cerberus-coverage:
	cd cerberus && $(OPAM_EXEC) dune build --workspace=dune-workspace.coverage ...

test-coverage: cerberus-coverage
	./scripts/test_coverage.sh
```

## Report Output

- **HTML report**: `_coverage/index.html` — interactive, expression-level highlighting
- **Terminal summary**: Per-file coverage percentages via `bisect-ppx-report summary --per-file`
- **Cobertura XML**: For CI integration via `bisect-ppx-report cobertura coverage.xml`

### Key files to examine in coverage reports

| Generated OCaml file | Source | Purpose |
|----------------------|--------|---------|
| `ocaml_frontend/generated/core_eval.ml` | `core_eval.lem` | Expression evaluation (~60K lines) |
| `ocaml_frontend/generated/core_reduction.ml` | `core_reduction.lem` | Small-step reduction (~70K lines) |
| `memory/concrete/impl_mem.ml` | (handwritten) | Concrete memory model (~3K lines) |

Coverage is reported against the **generated OCaml**, not the original Lem source. The mapping is straightforward since Lem generates readable OCaml.

## Environment Variables

| Variable | Default | Purpose |
|----------|---------|---------|
| `BISECT_FILE` | `bisect` | Prefix/directory for `.coverage` output files |
| `BISECT_SILENT` | `bisect.log` | Error logging: `YES` for silent, `ERR` for stderr |
| `BISECT_SIGTERM` | unset | When `yes`, writes coverage on SIGTERM (useful for killed processes) |

## Merging Coverage from Multiple Runs

bisect_ppx naturally supports merging. Each test run creates new uniquely-named `.coverage` files (`bisect0001.coverage`, `bisect0002.coverage`, etc.). When generating a report, all files are read together:

```bash
# Run different test suites
BISECT_FILE=_coverage/minimal ./run_minimal_tests
BISECT_FILE=_coverage/debug ./run_debug_tests
BISECT_FILE=_coverage/cerberus_ci ./run_cerberus_ci_tests

# Combined report from all runs
bisect-ppx-report html --coverage-path _coverage
bisect-ppx-report summary --per-file --coverage-path _coverage
```

## Excluding Code from Coverage

```ocaml
(* Exclude a single expression *)
[@coverage off]

(* Exclude a declaration *)
[@@coverage off]

(* Exclude a block of declarations *)
[@@@coverage off]
...
[@@@coverage on]

(* Exclude an entire file *)
[@@@coverage exclude_file]
```

Can also use `--exclusions` with a regex file for generated/test code we don't care about.

## Compatibility Notes

- **ppxlib constraint**: bisect_ppx 2.8.3 requires `ppxlib < 0.36.0`. If the Cerberus opam switch has a newer ppxlib, pin bisect_ppx to its dev repo (`opam pin add bisect_ppx --dev-repo`).
- **OCaml 5.4.0**: Supported (bisect_ppx requires >= 4.03.0).
- **dune 3.13**: Supported (bisect_ppx requires >= 2.7.0 for `--instrument-with`).
- **Performance**: Instrumented builds have moderate overhead from counter increments. Fine for testing, not for production.
