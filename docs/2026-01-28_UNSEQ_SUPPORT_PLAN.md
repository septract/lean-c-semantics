# Plan: Proper Unsequenced Expression (Eunseq) Support

**Date:** 2026-01-28

## Summary

Implement proper unsequenced expression support in CerbLean to match Cerberus semantics exactly. This requires:
1. Non-deterministic interleaving of unsequenced expressions
2. Memory footprint tracking via dynamic annotations
3. Race detection (UB035) when unsequenced memory accesses overlap

## Current State

**Lean Implementation:**
- `Expr.unseq` exists but executes **deterministically left-to-right**
- `UB035_unsequencedRace` is defined but **never raised**
- Location: `lean/CerbLean/Semantics/Step.lean:625-657`

**CRITICAL: Reference Implementation is `core_reduction.lem`**

Per email from Cerberus team: `core_run.lem` is **DEPRECATED** and will be removed. The driver uses `core_reduction.lem` which has:
1. Cleaner decomposition into base + contextual reductions
2. Proper unsequenced race detection via footprint accumulation

**Key approach in `core_reduction.lem`:**

1. **Contextual decomposition via `get_ctx`** (lines 509-588):
   - Returns a list of ALL `(context, reducible-expr)` pairs
   - For `Eunseq`: `get_ctx_unseq_aux` finds ALL non-irreducible expressions, not just the first
   - This produces multiple pairs, enabling non-deterministic choice of which sub-expression to reduce

2. **Step function `step_ctx`** (lines 1073-1471):
   - Maps over ALL contexts from `get_ctx`
   - Returns `list core_step2` (multiple possible next steps)
   - Non-determinism handled by `Step_nd2` constructor

3. **Race detection at `Eunseq` completion** via `one_step_unseq_aux` (lines 244-261):
   - Called when ALL operands of `Eunseq` are irreducible (values or `{A}v`)
   - Accumulates footprints while checking for races
   - Returns `Nothing` if race detected → triggers `UNSEQUENCED_RACE`
   - Returns `Just (fps, cvals)` if no race → tuple value with combined annotations

4. **Memory ops wrap results in `Eannot`** (lines 689-734):
   - Store creates: `Expr [] (Eannot [DA_neg/DA_pos excl_id [] fp] (mk_value_e Vunit))`
   - Load creates: `Expr [] (Eannot [DA_neg/DA_pos excl_id [] fp] (mk_value_e cval))`
   - Annotations record footprint AND exclusion ID for sequencing

5. **Exclusion mechanism for sequencing** (lines 925-944, 1286-1324):
   - `add_exclusion n ctx` adds `n` to all annotations' exclusion sets in context
   - Negative actions (`Paction Neg act`) create fresh exclusion ID
   - Strong sequences (`Esseq`) use `break_at_sseq` to manage sequencing boundaries

## Architecture: Controlled Non-determinism

### Cerberus's Approach (What We Must Match)

**`core_reduction.lem` uses contextual decomposition:**

1. **`get_ctx`** (line 509): Returns `list (context * expr)` - ALL possible reduction points
2. **`step_ctx`** (line 1073): Maps step logic over ALL contexts, returning `list core_step2`
3. **`Step_nd2`** (line 127): Non-deterministic choice constructor in `core_step2`

For `Eunseq`, the key is `get_ctx_unseq_aux` (lines 576-588):
```lem
and get_ctx_unseq_aux annot acc es1 = function
  | [] -> acc
  | e :: es2 ->
      if is_irreducible e then
        get_ctx_unseq_aux annot acc (es1 ++ [e]) es2
      else
        let zs = List.map (fun (ctx, e) ->
            (Cunseq annot es1 ctx es2, e)
          ) (get_ctx e) in
        get_ctx_unseq_aux annot (zs ++ acc) (es1 ++ [e]) es2
```

This returns ALL `(context, expr)` pairs for ALL non-irreducible expressions in the unseq, enabling non-deterministic interleaving.

**Our implementation must match this exactly** - the step function returns all possible branches, not just one.

### Our Additional Layer: Choice Stream (CerbLean Extension)

On top of the Cerberus-matching semantics, we add a **choice stream** layer for controlled exploration. This is a CerbLean extension (not in Cerberus) that provides:
1. **Exhaustive exploration** - enumerate all paths to detect any race
2. **Replayable execution** - reproduce specific executions for debugging
3. **Random sampling** - test random interleavings without full enumeration

```lean
/-- A choice stream that determines non-deterministic decisions (CerbLean extension) -/
structure ChoiceStream where
  /-- Get choice for selecting among n options (0-indexed) -/
  choose : Nat → Nat
  /-- Advance to next decision point -/
  next : ChoiceStream

/-- Choice stream from explicit list (for replay) -/
def ChoiceStream.fromList (choices : List Nat) : ChoiceStream := ...

/-- Choice stream from PRNG seed (for random testing) -/
def ChoiceStream.fromSeed (seed : Nat) : ChoiceStream := ...

/-- Choice stream that always picks first option (deterministic, matches current behavior) -/
def ChoiceStream.leftToRight : ChoiceStream := ...
```

### Execution Modes (CerbLean Extension)

```lean
inductive NDMode where
  | exhaustive                    -- Explore ALL paths, detect any race (matches Cerberus default)
  | replay (choices : List Nat)   -- Replay specific path (CerbLean extension)
  | random (seed : Nat)           -- Random sampling (CerbLean extension)
  | deterministic                 -- Left-to-right (current behavior)
```

### StepResult (Matching Cerberus)

The step function must return ALL possible branches, matching Cerberus's `NDnd`:

```lean
inductive StepResult where
  | done (v : Value)
  | continue_ (st : ThreadState)
  | branches (options : List ThreadState)   -- ALL possible next states (matches Cerberus NDnd)
  | race (ub : UB) (loc : Option Loc)
  | error (err : InterpError)
```

### Trace Recording

For debugging, record the choices made during execution:

```lean
structure ExecutionTrace where
  /-- Sequence of (numOptions, chosenIndex) at each decision point -/
  choices : List (Nat × Nat)
  /-- Final result -/
  result : NDResult
```

This allows:
- **Replay**: Given a trace, re-run with `ChoiceStream.fromList trace.choices.map (·.2)`
- **Shrinking**: For property testing, minimize failing traces
- **Diffing**: Compare traces between Cerberus and Lean

---

## Implementation Phases

### Phase 1: Foundation Types

**Files to modify:**
- `lean/CerbLean/Memory/Types.lean` (new types)
- `lean/CerbLean/Core/Annot.lean` (new types)

**Add:**
```lean
-- Memory footprint (matches impl_mem.ml:523-525)
inductive AccessKind where | read | write

structure Footprint where
  kind : AccessKind
  base : Nat
  size : Nat

-- Dynamic annotation (matches core.lem:300-302)
inductive DynAnnotation where
  | neg (id : Nat) (exclusionSet : List Nat) (footprint : Footprint)
  | pos (exclusionSet : List Nat) (footprint : Footprint)

abbrev DynAnnotations := List DynAnnotation
```

### Phase 2: Race Detection

**New file:** `lean/CerbLean/Semantics/Race.lean`

Implement race detection matching `cerberus/frontend/model/core_reduction.lem:200-227`:

```lean
-- Two reads never race; otherwise check address overlap
def Footprint.overlaps (fp1 fp2 : Footprint) : Bool :=
  match fp1.kind, fp2.kind with
  | .read, .read => false
  | _, _ => not (fp1.base + fp1.size <= fp2.base || fp2.base + fp2.size <= fp1.base)

-- Check if annotations indicate a race
def doRace (xs1 xs2 : DynAnnotations) : Bool := ...
```

### Phase 3: Eannot Expression

**Files to modify:**
- `lean/CerbLean/Core/Expr.lean`
- `lean/CerbLean/Parser.lean`
- `lean/CerbLean/PrettyPrint.lean`

Add `Eannot` constructor (matches core.lem:339):
```lean
| annot (dynAnnots : DynAnnotations) (e : AExpr)
```

### Phase 4: Memory Footprint Tracking

**Files to modify:**
- `lean/CerbLean/Memory/Concrete.lean`
- `lean/CerbLean/Semantics/Monad.lean`

Add footprint-returning variants:
```lean
def loadWithFootprint (ty : Ctype) (ptr : PointerValue) : ConcreteMemM (MemValue × Footprint)
def storeWithFootprint (ty : Ctype) (ptr : PointerValue) (mval : MemValue) : ConcreteMemM Footprint
```

Add exclusion ID state:
```lean
structure InterpState where
  ...
  nextExclusionId : Nat := 0
```

### Phase 5: Context Types and Operations

**New file:** `lean/CerbLean/Semantics/Context.lean`

Implement evaluation contexts matching `core_reduction.lem`:

```lean
/-- Evaluation context (matches core_reduction.lem context type) -/
inductive Context where
  | ctx                                                    -- CTX (hole)
  | unseq (annots : Annots) (before : List AExpr) (inner : Context) (after : List AExpr)  -- Cunseq
  | wseq (annots : Annots) (pat : APattern) (inner : Context) (e2 : AExpr)               -- Cwseq
  | sseq (annots : Annots) (pat : APattern) (inner : Context) (e2 : AExpr)               -- Csseq
  | annot_ (annots : Annots) (dynAnnots : DynAnnotations) (inner : Context)              -- Cannot
  | bound (annots : Annots) (inner : Context)                                            -- Cbound

/-- Apply a context to an expression (matches apply_ctx, lines 591-606) -/
def applyCtx : Context → AExpr → AExpr

/-- Get all (context, reducible-expr) pairs (matches get_ctx, lines 509-588) -/
def getCtx : AExpr → List (Context × AExpr)

/-- Get contexts for unseq operands (matches get_ctx_unseq_aux, lines 576-588) -/
def getCtxUnseqAux (annots : Annots) (acc : List (Context × AExpr))
    (before : List AExpr) : List AExpr → List (Context × AExpr)
```

**NOTE**: We do NOT need `pickWith` from `utils.lem` - the contextual decomposition approach in `core_reduction.lem` replaces it with `getCtx`/`getCtxUnseqAux`.

### Phase 6: Non-deterministic Eunseq Handling

**Files to modify:**
- `lean/CerbLean/Semantics/State.lean`
- `lean/CerbLean/Semantics/Step.lean`

**CRITICAL: Match `core_reduction.lem` approach**

The key insight from Cerberus is:
1. **Don't use continuation frames for unseq** - use contextual decomposition
2. **Return multiple next states** when there are multiple reducible sub-expressions
3. **Check races only when ALL operands are values**

Update `StepResult`:
```lean
inductive StepResult where
  | done (v : Value)
  | continue_ (st : ThreadState)
  | branches (states : List ThreadState)   -- NEW: multiple possible next states
  | error (err : InterpError)
```

**NOTE**: No separate `race` result needed - races trigger `InterpError.ub UB035_unsequenced_race`

**Key functions to implement (matching `core_reduction.lem`):**

1. **`isIrreducible`** (matches lines 181-194):
```lean
def isIrreducible : AExpr → Bool
  | ⟨_, .pure ⟨_, _, .val _⟩⟩ => true                    -- v
  | ⟨_, .annot _ ⟨_, .pure ⟨_, _, .val _⟩⟩⟩ => true      -- {A}v
  | _ => false
```

2. **`oneStepUnseqAux`** (matches lines 244-261):
```lean
/-- Accumulate values and check for races. Returns none if race detected. -/
def oneStepUnseqAux (fpsAcc : DynAnnotations) (cvalsAcc : List Value)
    : List AExpr → Option (DynAnnotations × List Value)
  | [] => some (fpsAcc, cvalsAcc.reverse)
  | ⟨_, .pure ⟨_, _, .val cval⟩⟩ :: xs =>
      oneStepUnseqAux fpsAcc (cval :: cvalsAcc) xs
  | ⟨_, .annot fps ⟨_, .pure ⟨_, _, .val cval⟩⟩⟩ :: xs =>
      if doRace fps fpsAcc then none  -- Race detected!
      else oneStepUnseqAux (combineDynAnnotations fps fpsAcc) (cval :: cvalsAcc) xs
  | _ => panic! "oneStepUnseqAux: non-value in unseq"
```

3. **`getCtx` / `getCtxUnseqAux`** (matches lines 509-588):
   - Returns all `(Context × AExpr)` pairs for reducible expressions
   - For Eunseq: finds ALL non-irreducible expressions, accumulates contexts

4. **Eunseq handling in step function**:
```lean
| .unseq es =>
    if es.all isIrreducible then
      -- All operands ready: check races and combine
      match oneStepUnseqAux [] [] es with
      | none =>
          pure (.error (.ub .ub035_unsequencedRace loc))
      | some (fps, cvals) =>
          -- Return {fps}(cval1, ..., cvaln)
          let result := mkAnnotExpr fps (mkTupleValue cvals)
          pure (.continue_ { state with expr := result })
    else
      -- Not all ready: return branches for all reducible sub-expressions
      let branches := getCtxUnseq es |>.map fun (ctx, e) =>
        { state with expr := applyCtx ctx (stepOne e) }
      pure (.branches branches)
```

### Phase 7: Non-deterministic Driver

**New files:**
- `lean/CerbLean/Semantics/NDDriver.lean` - Exhaustive exploration (matches Cerberus)
- `lean/CerbLean/Semantics/ChoiceStream.lean` - Replayable execution (CerbLean extension)

#### Part A: Exhaustive Exploration (Matches Cerberus)

```lean
/-- Result of exhaustive exploration -/
inductive NDResult where
  | allSucceeded (values : List Value)        -- All paths completed successfully
  | raceDetected (ub : UB) (loc : Option Loc) -- At least one path had a race
  | someError (err : InterpError)             -- At least one path had an error

/-- Exhaustive exploration: try ALL paths, detect any race
    This matches Cerberus's default behavior of exploring all interleavings -/
partial def exploreAll (state : ThreadState) (fuel : Nat) : NDResult :=
  match step state with
  | .done v => .allSucceeded [v]
  | .race ub loc => .raceDetected ub loc
  | .branches states =>
    -- Explore ALL branches (matches Cerberus NDnd semantics)
    -- If ANY branch has a race, return race
    ...
  | .error e => .someError e
```

#### Part B: Choice Stream (CerbLean Extension for Replayability)

```lean
/-- Choice stream for controlled non-determinism (CerbLean extension, not in Cerberus) -/
structure ChoiceStream where
  choose : Nat → Nat        -- Given n options, return index 0..(n-1)
  next : Unit → ChoiceStream

def ChoiceStream.leftToRight : ChoiceStream where
  choose _ := 0
  next _ := ChoiceStream.leftToRight

def ChoiceStream.fromList : List Nat → ChoiceStream
  | [] => ChoiceStream.leftToRight
  | c :: cs => { choose := fun _ => c, next := fun _ => fromList cs }

def ChoiceStream.fromSeed (seed : Nat) : ChoiceStream where
  choose n := seed % n
  next _ := fromSeed ((seed * 1103515245 + 12345) % (2^31))

/-- Run with a specific choice stream, recording trace for replay -/
partial def runWithChoices (state : ThreadState) (choices : ChoiceStream)
    (fuel : Nat) (trace : List Nat := []) : PathResult := ...
```

**Key insight**: The `trace` is just a `List Nat` - the sequence of indices chosen at each branch point. To replay, use `ChoiceStream.fromList trace`.

### Phase 8: Weak/Strong Sequencing Annotation Propagation

**Files to modify:**
- `lean/CerbLean/Semantics/Step.lean` (Ewseq/Esseq handling)

- `Ewseq`: Creates DA_neg with fresh exclusion ID
- `Esseq`: Creates DA_pos, propagates exclusion sets

---

## Critical Files Summary

| File | Changes |
|------|---------|
| `Memory/Types.lean` | `Footprint`, `AccessKind`, `Footprint.overlaps` ✅ Done |
| `Core/DynAnnot.lean` | New: `DynAnnotation`, `DynAnnotations` ✅ Done |
| `Core/Expr.lean` | Add `Expr.annot` constructor ✅ Done |
| `Semantics/Race.lean` | New: `doRace`, `checkRacePair` ✅ Done |
| `Semantics/Context.lean` | New: `Context`, `getCtx`, `applyCtx`, `getCtxUnseqAux` |
| `Semantics/State.lean` | Update `StepResult` with `.branches` |
| `Semantics/Step.lean` | Rewrite to use contextual decomposition, `oneStepUnseqAux` |
| `Semantics/ChoiceStream.lean` | New: `ChoiceStream`, replay/random modes (CerbLean extension) |
| `Semantics/NDDriver.lean` | New: `exploreAll`, trace recording |
| `Memory/Concrete.lean` | Add footprint tracking to load/store |
| `Parser.lean` | Parse `Eannot` ✅ Done |
| `PrettyPrint.lean` | Print `Eannot` |

---

## Cerberus Reference Files

**CRITICAL: Use `core_reduction.lem` NOT `core_run.lem`** (per email from Cerberus team)

### Primary Reference: `core_reduction.lem`
| Lines | Content |
|-------|---------|
| 181-194 | `is_irreducible` - check if expression is a value or annotated value |
| 200-227 | `do_race` - race detection between annotation sets |
| 229-231 | `combine_dyn_annotations` |
| 234-241 | `one_step` result type |
| 244-261 | `one_step_unseq_aux` - accumulate footprints, detect races |
| 266-439 | `one_step` - base reductions for effectless expressions |
| 509-574 | `get_ctx` - contextual decomposition |
| 576-588 | `get_ctx_unseq_aux` - find all reducible sub-expressions in unseq |
| 591-606 | `apply_ctx` - plug expression into context |
| 621-801 | `step_action` - memory action handling with footprint wrapping |
| 925-944 | `add_exclusion` - add exclusion ID to all annotations in context |
| 1073-1471 | `step_ctx` - main step function |

### Other Reference Files
- `cerberus/frontend/model/core.lem:300-312` - `dyn_annotation` type
- `cerberus/frontend/model/core.lem:339` - `Eannot` constructor
- `cerberus/memory/concrete/impl_mem.ml:523-532` - `footprint` type, `overlapping`

---

## Testing Strategy

1. **Unit tests:**
   - `Footprint.overlaps` (read/read, read/write, write/write cases)
   - `doRace` with various annotation combinations
   - `pickWith` correctness

2. **Integration tests:**
   - All 7 "ko" tests should detect UB035: `tests/ci/030[0-6]-unseq_race_ko*.undef.c`
   - All 4 "ok" tests should succeed: `tests/ci/031[0-3]-*.c`
   - C standard tests: `tests/examples/6.5-2.1.c`, `6.5-2.2.c`

3. **Differential testing:**
   ```bash
   ./scripts/test_interp.sh cerberus/tests/ci/030*.c -v
   ```
   Expected: All tests should now MATCH Cerberus (currently they show DIFF)

---

## Verification

After implementation, run:
```bash
# Build
make lean

# Unit tests
make test-memory

# Specific unseq tests
./scripts/test_interp.sh cerberus/tests/ci/0300-unseq_race_ko01.undef.c -v
./scripts/test_interp.sh cerberus/tests/ci/0311-unseq_race_ok01.c -v

# All unseq tests
./scripts/test_interp.sh cerberus/tests/ci/030*.c cerberus/tests/ci/031*.c -v
```

Expected results:
- ko tests: Both Cerberus and Lean report `UB035_unsequenced_race`
- ok tests: Both return concrete values without UB

---

## Replayability Use Cases

### 1. Debugging a Race

```bash
# Run exhaustive exploration, find a race
./cerblean --mode=exhaustive program.c
# Output: "Race detected! Trace: [1, 0, 2]"

# Replay the exact path that caused the race
./cerblean --mode=replay --trace="1,0,2" program.c
# Deterministically reproduces the race
```

### 2. Differential Testing with Traces

```bash
# Get Cerberus trace (if Cerberus exposes this)
cerberus --trace program.c > cerberus_trace.txt

# Replay same choices in Lean
./cerblean --mode=replay --trace-file=cerberus_trace.txt program.c
```

### 3. Fuzz Testing with Seeds

```bash
# Run 1000 random interleavings
for seed in $(seq 1 1000); do
  ./cerblean --mode=random --seed=$seed program.c || echo "FAIL seed=$seed"
done

# If seed 42 fails, replay it:
./cerblean --mode=random --seed=42 program.c -v
```

### 4. Shrinking Failing Traces

When a long trace causes a race, find the minimal trace:
```lean
-- Try progressively shorter prefixes/subsequences
def shrinkTrace (trace : List Nat) (test : List Nat → Bool) : List Nat := ...
```

---

## Cerberus Correspondence Summary

All references are to `core_reduction.lem` (the CURRENT implementation) unless otherwise noted.

| Component | Cerberus Reference | Notes |
|-----------|-------------------|-------|
| `Footprint` | `impl_mem.ml:523-525` | **Must match exactly** |
| `DynAnnotation` | `core.lem:300-302` | **Must match exactly** |
| `Eannot` | `core.lem:339` | **Must match exactly** |
| `doRace` | `core_reduction.lem:200-227` | **Must match exactly** |
| `combineDynAnnotations` | `core_reduction.lem:229-231` | **Must match exactly** |
| `isIrreducible` | `core_reduction.lem:181-194` | **Must match exactly** |
| `oneStepUnseqAux` | `core_reduction.lem:244-261` | **Must match exactly** |
| `Context` type | `core_reduction.lem` (context constructors) | **Must match exactly** |
| `getCtx` | `core_reduction.lem:509-574` | **Must match exactly** |
| `getCtxUnseqAux` | `core_reduction.lem:576-588` | **Must match exactly** |
| `applyCtx` | `core_reduction.lem:591-606` | **Must match exactly** |
| `stepCtx` | `core_reduction.lem:1073-1471` | **Must match exactly** |
| Store footprint wrapping | `core_reduction.lem:689-698` | **Must match exactly** |
| Load footprint wrapping | `core_reduction.lem:724-734` | **Must match exactly** |
| `addExclusion` | `core_reduction.lem:925-944` | **Must match exactly** |
| `StepResult.branches` | `Step_nd2` in `core_reduction.lem:127` | **Must match exactly** |
| `exploreAll` | Cerberus default exhaustive mode | **Must match exactly** |
| `ChoiceStream` | N/A | **CerbLean extension** |
| `runWithChoices` | N/A | **CerbLean extension** |
| Trace recording | N/A | **CerbLean extension** |

---

## Risk Mitigation

| Risk | Mitigation |
|------|------------|
| Performance (exponential paths) | Add fuel limit; early race detection; prune equivalent paths |
| Semantic mismatch | Careful audit against `core_reduction.lem`; extensive testing |
| Annotation propagation bugs | Unit tests for each sequencing operator |
| Non-reproducible failures | Choice stream architecture ensures full replayability |
