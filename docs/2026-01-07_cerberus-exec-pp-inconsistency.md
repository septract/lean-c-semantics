# Cerberus inconsistency: `--exec` succeeds where `--pp=core` fails

## Summary

Cerberus has three ways of handling problematic C programs:

1. **Static rejection**: Both `--exec` and `--pp=core` fail with an error (e.g., syntax errors, undeclared identifiers)
2. **Runtime UB detection**: Both modes succeed, with `--exec` reporting UB at runtime
3. **Inconsistent**: `--exec` succeeds (reporting UB) but `--pp=core` fails

Case 3 is unexpected and inconsistent.

## Case 1: Static rejection (both modes fail) - Consistent

`tests/debug/ub-static-reject.c`:
```c
int main() {
    return undefined_var;
}
```

```
$ cerberus --exec --batch test.c
error: use of undeclared identifier 'undefined_var'

$ cerberus --pp=core test.c
error: use of undeclared identifier 'undefined_var'
```

Both modes reject the program. This is consistent.

## Case 2: Runtime UB detection (both modes succeed) - Consistent

`tests/debug/ub-runtime-detect.c`:
```c
int main() {
    int x = 1;
    int y = 0;
    return x / y;
}
```

```
$ cerberus --exec --batch test.c
Undefined {ub: "UB045a_division_by_zero", ...}

$ cerberus --pp=core test.c
(Core IR output - succeeds)
```

Both modes accept the program. `--exec` detects UB at runtime. This is consistent.

## Case 3: Inconsistent (exec succeeds, pp fails) - BUG

`tests/debug/ub-inconsistent.c`:
```c
struct a {};
```

```
$ cerberus --exec --batch test.c
Undefined {ub: "UB061_no_named_members", stderr: "", loc: "<1:1--1:12>"}

$ cerberus --pp=core test.c
test.c:1:1: error: undefined behaviour: a structure or union is defined without any named members
struct a {};
^~~~~~~~~~~
```

`--exec` accepts the program and reports UB at runtime, but `--pp=core` rejects it at compile time. This is **inconsistent**.

## Why this matters

If `--exec` can run a program and report UB, we expect `--pp=core` to also succeed so we can inspect the Core IR. The inconsistency means some programs that Cerberus can execute cannot have their Core IR examined.

## Suggested fix

The issue is that some UB checks (like UB061) are treated as fatal compile-time errors in `--pp=core` mode but deferred to runtime in `--exec` mode.

Two options:

1. **Make `--pp=core` more lenient** (preferred): Generate Core IR for programs with these UB issues, inserting runtime UB checks as `--exec` does. This is more consistent with the C standard treating these as UB (runtime) rather than constraint violations (compile-time).

2. **Make `--exec` more strict**: Reject these programs at compile time, consistent with `--pp=core`.

Option 1 seems preferable since `--exec` already demonstrates it's possible to handle these cases by deferring UB detection to runtime.

## Environment

- Cerberus version: current main branch
- OS: macOS
- Minimal reproducer found using creduce from a csmith-generated test (seed 245474981)
