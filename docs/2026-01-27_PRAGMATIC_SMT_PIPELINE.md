# Pragmatic SMT Pipeline Plan

**Date**: 2026-01-27
**Status**: Proposal

## Goal

Get a working verification pipeline that:
1. Type checks CN-annotated C programs
2. Generates proof obligations
3. Calls an external SMT solver (z3) to discharge them
4. Reports success/failure

**Non-goal (for now)**: Foundational proofs in Lean. That's a separate research project.

## Current State

We have:
- `checkFunction : FunctionSpec → Core.AExpr → Loc → TypeCheckResult`
- `TypeCheckResult` contains `obligations : List Obligation`
- Each `Obligation` has `constraint : LogicalConstraint` and `assumptions : LCSet`

What's blocking the foundational approach:
- `checkFunction` computation is too expensive for Lean's kernel to normalize
- Can't use `simp` to reduce `allSatisfied [ob1, ob2, ...]` because the list is opaque
- Missing `DecidableEq` on `LogicalConstraint` (mutually recursive types)
- The pure-to-HeapValue soundness bridge has `sorry`s

## Pragmatic Pipeline

```
┌─────────────────────────────────────────────────────────────────┐
│  1. Type Check                                                   │
│     checkFunction spec program loc → TypeCheckResult            │
│     - Produces List Obligation                                  │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  2. Serialize to SMT-LIB2                                       │
│     obligations.map toSmtLib2 → List String                     │
│     - Each obligation becomes: (assert (=> assumptions goal))   │
│     - Check satisfiability of negation                          │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  3. Call External SMT                                           │
│     IO.Process.spawn "z3" ["-in"] with SMT-LIB2 input          │
│     - Parse output: sat/unsat/unknown                           │
│     - unsat = obligation discharged                             │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  4. Report Results                                              │
│     - All unsat: "Verification succeeded"                       │
│     - Any sat/unknown: "Obligation failed: <description>"       │
└─────────────────────────────────────────────────────────────────┘
```

## Implementation

### New Files

```
CN/Verification/
├── SmtLib.lean      # Serialization to SMT-LIB2 format
├── SmtSolver.lean   # External solver interface (IO)
└── Verify.lean      # Main verification entry point
```

### SmtLib.lean - Serialization

```lean
/-- Convert a Term to SMT-LIB2 s-expression -/
def Term.toSmtLib : Term → String
  | .const (.z n) => toString n
  | .const (.bool true) => "true"
  | .const (.bool false) => "false"
  | .sym s => s.name.getD s!"_sym{s.id}"
  | .binop .add l r => s!"(+ {l.term.toSmtLib} {r.term.toSmtLib})"
  | .binop .sub l r => s!"(- {l.term.toSmtLib} {r.term.toSmtLib})"
  | .binop .mul l r => s!"(* {l.term.toSmtLib} {r.term.toSmtLib})"
  | .binop .lt l r => s!"(< {l.term.toSmtLib} {r.term.toSmtLib})"
  | .binop .le l r => s!"(<= {l.term.toSmtLib} {r.term.toSmtLib})"
  | .binop .eq l r => s!"(= {l.term.toSmtLib} {r.term.toSmtLib})"
  | .binop .and_ l r => s!"(and {l.term.toSmtLib} {r.term.toSmtLib})"
  | .binop .or_ l r => s!"(or {l.term.toSmtLib} {r.term.toSmtLib})"
  | .binop .implies l r => s!"(=> {l.term.toSmtLib} {r.term.toSmtLib})"
  | .unop .not arg => s!"(not {arg.term.toSmtLib})"
  | .unop .negate arg => s!"(- {arg.term.toSmtLib})"
  | _ => "UNSUPPORTED"

/-- Convert a LogicalConstraint to SMT-LIB2 -/
def LogicalConstraint.toSmtLib : LogicalConstraint → String
  | .t it => it.term.toSmtLib
  | .forall_ (s, _bt) body =>
      s!"(forall (({s.name.getD "_"} Int)) {body.term.toSmtLib})"

/-- Collect free symbols from a term -/
def Term.freeSyms : Term → List Sym
  -- ... recursive collection

/-- Generate SMT-LIB2 for an obligation:
    (declare-fun x () Int)
    ...
    (assert (not (=> assumptions constraint)))
    (check-sat)
-/
def Obligation.toSmtLib2 (ob : Obligation) : String :=
  let syms := collectAllSyms ob
  let decls := syms.map fun s => s!"(declare-fun {symName s} () Int)"
  let assumptions := ob.assumptions.map (·.toSmtLib)
  let assumptionConj := if assumptions.isEmpty then "true"
                        else s!"(and {String.intercalate " " assumptions})"
  let goal := ob.constraint.toSmtLib
  let query := s!"(assert (not (=> {assumptionConj} {goal})))"
  String.intercalate "\n" (decls ++ [query, "(check-sat)"])
```

### SmtSolver.lean - External Interface

```lean
/-- Result of SMT solver call -/
inductive SmtResult where
  | unsat       -- Obligation discharged
  | sat         -- Counterexample exists
  | unknown     -- Solver couldn't decide
  | error (msg : String)
  deriving Repr, BEq

/-- Call z3 on SMT-LIB2 input -/
def callZ3 (smtLib : String) : IO SmtResult := do
  let child ← IO.Process.spawn {
    cmd := "z3"
    args := #["-in"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  child.stdin.putStr smtLib
  child.stdin.flush
  let stdout ← child.stdout.readToEnd
  let _ ← child.wait
  match stdout.trim with
  | "unsat" => return .unsat
  | "sat" => return .sat
  | "unknown" => return .unknown
  | other => return .error s!"Unexpected output: {other}"

/-- Check a single obligation -/
def checkObligation (ob : Obligation) : IO (Obligation × SmtResult) := do
  let smtLib := ob.toSmtLib2
  let result ← callZ3 smtLib
  return (ob, result)

/-- Check all obligations -/
def checkAllObligations (obs : List Obligation) : IO (List (Obligation × SmtResult)) :=
  obs.mapM checkObligation
```

### Verify.lean - Entry Point

```lean
/-- Verification result -/
structure VerificationResult where
  tcSuccess : Bool
  tcError : Option String
  obligations : List (Obligation × SmtResult)
  allDischarged : Bool

/-- Main verification function -/
def verify (spec : FunctionSpec) (prog : Core.AExpr) (loc : Loc) : IO VerificationResult := do
  let tcResult := checkFunction spec prog loc
  if !tcResult.success then
    return {
      tcSuccess := false
      tcError := tcResult.error
      obligations := []
      allDischarged := false
    }
  let obResults ← checkAllObligations tcResult.obligations
  let allDischarged := obResults.all (·.2 == .unsat)
  return {
    tcSuccess := true
    tcError := none
    obligations := obResults
    allDischarged
  }

/-- Pretty-print verification result -/
def VerificationResult.toString (r : VerificationResult) : String :=
  if !r.tcSuccess then
    s!"Type checking failed: {r.tcError.getD "unknown error"}"
  else if r.allDischarged then
    s!"Verification succeeded ({r.obligations.length} obligations discharged)"
  else
    let failed := r.obligations.filter (·.2 != .unsat)
    let failedStrs := failed.map fun (ob, res) =>
      s!"  - {ob.description}: {repr res}"
    s!"Verification failed:\n{String.intercalate "\n" failedStrs}"
```

## What to Keep vs. Cleanup

### Keep (useful for pragmatic pipeline)

| File | Why |
|------|-----|
| `Obligation.lean` | Core obligation structure |
| `TypeCheckResult` | Result type |
| `checkFunction` | Main type checker |
| All type checking machinery | Needed |

### Keep (useful for future foundational work)

| File | Why |
|------|-----|
| `PureDenote.lean` | Pure interpretation layer |
| `Denote.lean` | HeapValue interpretation |
| `Obligation.toProp` | Semantic meaning |
| `Obligation.pureToProp` | SMT-friendly semantics |
| `allSatisfied` simp lemmas | For computed lists |

### Cleanup (foundational attempts that didn't work)

| File | Action |
|------|--------|
| `SmtTest.lean` | Delete (exploration file) |
| `Discharge.lean` | Simplify - keep basic structure, remove complex tactic machinery |
| `PureDenoteSound.lean` | Keep structure, mark sorries clearly as "future work" |
| `PipelineDemo.lean` | Simplify - keep as documentation, remove sorry-based proofs |

### Move to Branch (preserve for reference)

Create `foundational-proofs` branch with current state before cleanup.

## Branch Strategy

```
main
  └── cn-types (current)
        ├── pragmatic-smt (new: implement above)
        └── foundational-proofs (new: preserve current exploration)
```

## Testing

```lean
-- In a test file
def testSpec : FunctionSpec := ...
def testProgram : Core.AExpr := ...

#eval do
  let result ← verify testSpec testProgram .unknown
  IO.println result.toString
```

## Future: Making it Foundational

If we later want foundational proofs:

1. **SMT certificate reconstruction**: z3 can produce proof certificates. We'd need to:
   - Parse the certificate
   - Reconstruct a Lean proof term
   - This is a significant project (lean-smt does some of this)

2. **Alternative: Reflection with DecidableEq**:
   - Add `BEq` and `DecidableEq` to all term types (tedious but mechanical)
   - Use native_decide to bridge Bool → Prop
   - This makes the "constraint in assumptions" case foundational

3. **Alternative: Generated proof obligations**:
   - Instead of computing obligations, generate them as separate `theorem` statements
   - Each theorem can be proved by SMT tactic directly
   - Macro/elaborator generates the glue code

## Summary

**Phase 1 (now)**: Pragmatic pipeline with external SMT
- Works end-to-end
- No Lean proofs, but useful for verification
- ~200 lines of new code

**Phase 2 (future)**: Pick one foundational approach
- Certificate reconstruction, OR
- DecidableEq + reflection, OR
- Generated proof obligations

The pragmatic pipeline is a solid foundation for Phase 2 - we're not throwing anything away, just deferring the hard part.
