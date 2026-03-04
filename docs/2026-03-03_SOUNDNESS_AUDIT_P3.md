# Soundness Audit Phase 3: HasType vs Interpreter Fixes

Created: 2026-03-03

Third comprehensive audit of ProofSystem HasType rules against interpreter semantics.
Follows audits from 2026-03-01 and 2026-03-03.

## Changes Made

### P0-1: HeapValue float and array support (FIXED)

**Problem**: `heapValueOfMemValue` mapped `.floating` and `.array` MemValues to
`.uninitialized`, making store/load rules for these types unsatisfiable.

**Fix**:
- Added `| floating (fty : FloatingType) (fv : FloatingValue)` to `HeapValue` (Heap.lean)
- `heapValueOfMemValue` now maps `.floating fty fv` → `.floating fty fv`
- `heapValueOfMemValue` now recursively converts `.array` elements (with dummy Ctype)
- Added `| .floating _ _, .real => True` to `heapValueHasType` (Models.lean)
- Added `| .array _ elems, .list bt => ∀ elem, elem ∈ elems → heapValueHasType elem bt`

### P0-2: Store rules ct↔τ premise (FIXED)

**Problem**: `action_store` and `action_store_block` had no premise connecting the
Ctype `ct` (from the Owned resource) to the value type `τ`. The interpreter's
`memValueFromValue ct cval` pattern-matches both together.

**Fix**: Added `ctypeToBaseType ct = some τ` premise to both rules. Updated examples
(LoadStore.lean, Loop.lean) with `rfl` — reduces by definition for concrete types.

### P0-3: Load bridge lemma (STATED)

**Problem**: No bridge from HeapValue→Value for load soundness.

**Fix**: Stated `heapValueHasType_implies_loadedValueHasType` in PureHelpers.lean
(sorry'd). Uses `valueFromMemValue` from Eval.lean.

### P0-4: envValuationCompat removal (FIXED)

**Problem**: `envValuationCompat` used `∀ τ` bridge which was unprovable for integers.
Already superseded by `EnvCompat` in Defs.lean.

**Fix**: Removed `envValuationCompat`, `pexprEnvLookup`, and old
`pexprMatchesTerm_eval_compat` from HasType.lean. Updated Defs.lean and Pure.lean
to remove references.

### P1-1: pexprMatchesTerm_eval_compat strengthened (STATED)

**Problem**: Old formulation used `pexprEnvLookup` which only handled `Pexpr.sym`.
Useless for store soundness with computed value expressions.

**Fix**: New `pexprMatchesTerm_eval_compat'` in PureHelpers.lean uses `evalPexpr`
directly. Sorry'd — the proof requires case analysis on PexprMatchesTerm constructors.

### P1-2: condTermOfPexpr correctness (STATED)

**Problem**: No lemma connecting interpreter's boolean evaluation to the logical
constraint from `condTermOfPexpr`. Needed for `if_` rule soundness.

**Fix**: Stated `condTermOfPexpr_correct` in PureHelpers.lean (sorry'd).

## Sorry Count Delta

| File | Before | After | Delta | Notes |
|------|--------|-------|-------|-------|
| HasType.lean | 2 | 1 | -1 | Removed old pexprMatchesTerm_eval_compat |
| Models.lean | 10 | 10 | 0 | No change |
| PureHelpers.lean | 10 | 13 | +3 | New: load bridge, pexpr eval, condTerm |
| Pure.lean | 37 | 36 | -1 | Removed old pexprMatchesTerm_eval_compat |
| Statement.lean | 5 | 5 | 0 | No change |

Net: +1 sorry (3 new lemma statements, 2 old ones removed).

## Files Modified

- `lean/CerbLean/CN/Semantics/Heap.lean` — HeapValue `.floating` constructor, array conversion
- `lean/CerbLean/ProofSystem/Models.lean` — `heapValueHasType` float/array cases
- `lean/CerbLean/ProofSystem/HasType.lean` — Store rule premises, removed deprecated defs
- `lean/CerbLean/ProofSystem/Soundness/Defs.lean` — Cleaned open statement
- `lean/CerbLean/ProofSystem/Soundness/PureHelpers.lean` — New bridge lemmas
- `lean/CerbLean/ProofSystem/Soundness/Pure.lean` — Removed old pexpr compat
- `lean/CerbLean/ProofSystem/Examples/LoadStore.lean` — New `rfl` arg for ctypeToBaseType
- `lean/CerbLean/ProofSystem/Examples/Loop.lean` — New `rfl` arg for ctypeToBaseType
