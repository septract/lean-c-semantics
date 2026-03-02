# HasType / PureHasType Soundness Amenability Audit

Created: 2026-03-01

## Purpose

Audit the separation-logic type system in `lean/CerbLean/ProofSystem/HasType.lean`
for amenability to a future soundness proof with respect to the Core interpreter
in `lean/CerbLean/Semantics/`. The goal is to identify rules that are unsound
(admit programs that go wrong) or unprovably sound (correct but structured so a
proof would require non-trivial infrastructure that doesn't exist).

## Methodology

For each rule in `PureHasType` and `HasType`:

1. **Could I state the soundness lemma?** For `PureHasType Γ pe τ`: if the
   context is satisfied by a state/valuation, evaluating `pe` produces a value
   of type `τ`. For `HasType Γ H₁ e τ H₂`: if the heap satisfies `H₁`, then
   evaluating `e` does not trigger UB, returns a value of type `τ`, and the
   resulting heap satisfies `H₂`.

2. **Could I prove it?** Walk through what the interpreter does for each
   expression form. Does each premise of the typing rule correspond to something
   the interpreter checks or produces?

3. **Are implicit parameters constrained?** Look for universally quantified type
   variables that appear in the conclusion but are not determined by any premise.

## Verdict Key

- **SOUND**: Amenable to soundness proof with existing infrastructure
- **SOUND (with caveat)**: Amenable but requires a specific lemma or assumption
- **UNSOUND**: Admits programs that go wrong (counterexample given)
- **BLOCKED**: Rule is correct but proof requires missing infrastructure

---

## PureHasType Rules

### `PureHasType.val` — SOUND (with caveat)

The rule requires `valueHasType v τ`, which constrains the type claim.

**Caveat 1**: For `.loaded (.unspecified ct)`, `valueHasType` constrains `τ` via
`ctypeToBaseType ct`. The soundness proof needs: if the interpreter produces
`.loaded (.unspecified ct)` then `ctypeToBaseType ct = some τ` for some known
`τ`. Since `ctypeToBaseType` returns `none` for arrays, functions, atomics, this
requires a well-formedness invariant on the memory state.

**Caveat 2**: For arrays, `valueHasType` is very permissive:
`.loaded (.specified (.array _)), .list _ => True` — any array matches any list
type. Not unsound but gives weak types: can't distinguish `list int` from
`list loc`.

### `PureHasType.sym` — SOUND

Straightforward lookup. Requires standard context well-formedness invariant.

### `PureHasType.op` — SOUND (with caveat)

`opResultType` determines the result type. Arithmetic returns the left
operand's type.

**Caveat**: `opResultType` is incomplete — bitwise ops completely missing,
some operators absent. Expressions using those operators can't be typed.
Incompleteness, not unsoundness.

### `PureHasType.if_` — SOUND

Standard conditional: condition `bool`, branches agree. Matches interpreter.

### `PureHasType.not_` — SOUND

Bool → bool. Matches interpreter.

### `PureHasType.let_` — SOUND

Standard let binding. Only handles `base (some x) bty` patterns — incomplete
but not unsound.

### `PureHasType.arrayShift` — SOUND

Pointer arithmetic returns pointer. Index not type-checked in the rule, but
UB at runtime is caught by the soundness theorem's "does not trigger UB" clause.

### `PureHasType.memberShift` — SOUND

Pointer + field offset = pointer. Straightforward.

### `PureHasType.struct_` — SOUND

Each field individually typed, result is `struct_ tag`.

### `PureHasType.memberof` — SOUND (with caveat)

Requires `lookupTagDef`, field lookup, `ctypeToBaseType`.

**Caveat**: `ctypeToBaseType` incomplete for nested arrays (`int[10]` returns
`none`). For `union`, maps to `.struct_ tag` which may be imprecise but
consistent with CN-level representation.

### `PureHasType.convInt` — SOUND

Result type `intTypeToBaseType ity` is deterministic. Matches interpreter.

### `PureHasType.isScalar` / `isInteger` / `isSigned` / `isUnsigned` / `areCompatible` — SOUND

All return `bool`. Type predicates always produce booleans in interpreter.

### `PureHasType.case_` — SOUND

Pattern match, all branches same type. Standard.

### `PureHasType.wrapI` — SOUND

Wrapping arithmetic. Result from `intTypeToBaseType ity`. Same as `convInt`.

---

## HasType Rules

### `HasType.pure` — SOUND

Heap unchanged. Pure expression typed by `PureHasType`. Trivially sound.

### `HasType.let_` / `let_wild` — SOUND

Pure expression bound, body typed in extended context. Matches interpreter.

### `HasType.sseq` / `sseq_wild` / `wseq` / `wseq_wild` — SOUND

Heap threading `H₁ → H₂ → H₃`. For sequential execution, `wseq` and `sseq`
are equivalent. Matches interpreter.

### `HasType.if_` — SOUND (with caveat)

Condition bool, branches typed with path conditions via `condTermOfPexpr`.

**Caveat**: Soundness proof needs: if `condTermOfPexpr cond = some condTerm`
and `cond` evaluates to true, then `evalConstraint ρ (.t condTerm) = True`.
This is provable but requires showing `condTermOfPexpr`'s translation is
semantically correct (see helper analysis below).

### `HasType.case_` — SOUND

Pattern match, each branch typed with pattern bindings. Standard.

### `HasType.bound` / `HasType.annot` — SOUND

Transparent wrappers. No semantic effect.

### `HasType.excluded` — SOUND

Neg-action wrapper. Inner action has same typing. Transparent for our
type system (which doesn't model race detection).

### `HasType.action_load` — UNSOUND (via heapValueHasType)

The rule returns `val.bt` — the base type annotation on the value IndexTerm.
The `models` definition for `.owned` with `initState = .init` requires:
```
evalIndexTerm ρ val = some v ∧
valueMatchesType ct v ∧
heapValueHasType v val.bt
```

The `heapValueHasType v val.bt` premise IS checked. However,
`heapValueHasType` has unsound cases:
- `| _, .unit => True` — any value matches unit
- `| _, .bool => True` — any value matches bool
- `| _, .ctype => True` — any value matches ctype

**Counterexample**: Construct `Owned<int>(init, ptr, val)` where
`val = ⟨.sym s, .bool, default⟩`. Then `heapValueHasType v .bool = True`
for any `v`, so `models` is satisfiable even when the actual heap value is
an integer. The load rule returns type `.bool`, but the runtime value is an
arbitrary integer. Downstream pure operations expecting a boolean will fail.

Root cause: `heapValueHasType` in Models.lean:131-140.

### `HasType.action_store` — UNSOUND (valNew.bt unconstrained)

The rule does NOT require the stored value's type `τ` (from
`PureHasType Γ valPe τ`) to match `valNew.bt` (the annotation on the new
value term in the post-heap `Owned`). A derivation can claim arbitrary type
annotations on the post-heap `Owned` resource.

**Counterexample**: Store an integer but annotate `valNew.bt` as `.loc`.
Post-heap has `Owned<int>(init, ptr, valNew)` where `valNew.bt = .loc`.
A subsequent load claims the result is a pointer. UB when dereferenced.

### `HasType.action_store_block` — UNSOUND (same as action_store)

Same `valNew.bt` unconstrained issue.

### `HasType.action_create` — SOUND

`ptrSym` freshness concern is addressed by `star` disjointness:
two blocks with the same `ptrSym` would require two disjoint heap cells
at the same location, which is impossible.

### `HasType.action_kill_owned` / `action_kill_block` — SOUND

Consumes resource. `PexprMatchesTerm` connects pointer. Straightforward.

### `HasType.proc` — BLOCKED (models_subst_iff)

Soundness relies on `models_subst_iff` (sorry'd in Models.lean:454).
`SLProp.subst` calls `AnnotTerm.subst` which is `partial`, blocking
definitional reduction. The lemma statement is correct but the proof
requires reasoning about partial functions.

### `HasType.ccall` — UNSOUND (spec unconstrained) + BLOCKED

The function specification `spec` is universally quantified with no
connection to the actual function being called. Any spec can be used
for any function pointer call.

**Counterexample**: Call function `f` but supply spec for function `g`.
The derivation claims `g`'s postcondition while `f` runs.

Also BLOCKED on `models_subst_iff` like `proc`.

### `HasType.memop_ptrCmp` / `memop_ptrValid` / `memop_ptrArrayShift` / `memop_ptrMemberShift` — SOUND

Return appropriate types, heap unchanged. Match interpreter.

### `HasType.memop_intFromPtr` / `memop_ptrFromInt` / `memop_ptrdiff` — SOUND

Return appropriate fixed types, heap unchanged.

### `HasType.memop_memcpy` — UNSOUND (arbitrary post-heap)

Uses `SLProp.entails H₁ H₂` without connecting to memcpy's actual behavior.
A derivation can claim arbitrary post-heap transformations.

### `HasType.memop_memcmp` — SOUND

Returns `bits .signed 32`, heap unchanged.

### `HasType.save` — BLOCKED (models_subst_iff)

Same substitution dependency as `proc`.

### `HasType.run` — BLOCKED (models_subst_iff) + unconstrained post

Jump to label. Return type `τ` and post-heap `H₂` are unconstrained (correct
since `run` doesn't return). Same substitution dependency.

### `HasType.frame` — BLOCKED (heapFragmentOf + frame property)

Requires:
1. `heapFragmentOf` axiom to be faithful
2. Memory model frame property: operations only modify their footprint
Neither is established.

### `HasType.consequence` — SOUND

`SLProp.entails` is defined as `∀ ρ h, models ρ H₁ h → models ρ H₂ h`.
Universal quantification over all valuations is the standard definition.

---

## Helper Function Analysis

### `condTermOfPexpr`

Translates Core Pexpr conditions to CN IndexTerms:
- `.gt → .lt` with swapped operands: `a > b → b < a` — correct
- `.ge → .le` with swapped operands: `a >= b → b <= a` — correct
- `.eq`, `.lt`, `.le` → direct — correct

**Minor issue**: `pexprToIndexTerm` assigns `bt = .integer` for all symbols
(line 83), even pointer-typed ones. Doesn't affect path condition evaluation
(which ignores `bt`) but is imprecise.

### `valueHasType`

**UNSOUND cases**:
- `.loaded (.unspecified ct), τ` — delegates to `ctypeToBaseType`, correct
- `.loaded (.specified (.array _)), .list _` — too permissive but not exploitable

### `heapValueHasType`

**UNSOUND cases** (Models.lean:131-140):
- `| _, .unit => True` — any value matches unit
- `| _, .bool => True` — any value matches bool
- `| _, .ctype => True` — any value matches ctype

These propagate unsoundness through `models` for `.owned` resources.

### `ctypeToBaseType`

Incomplete: returns `none` for arrays, functions, atomics, `void`. Not unsound,
just blocks derivations for those types.

---

## Prioritized Issue List

### P0 — Critical (UNSOUND)

| # | Issue | Location | Impact |
|---|-------|----------|--------|
| 1 | `heapValueHasType` too permissive (`.unit`, `.bool`, `.ctype` accept any value) | Models.lean:131-140 | Propagates wrong types through `action_load` |
| 2 | `action_store` / `action_store_block`: `valNew.bt` unconstrained | HasType.lean:584-612 | Post-heap `Owned` can have arbitrary type annotation |
| 3 | `ccall` spec unconstrained (no connection to called function) | HasType.lean:681-696 | Can claim arbitrary postconditions |
| 4 | `memop_memcpy` post-heap via bare entailment | HasType.lean:741-745 | Can claim arbitrary post-heap |

### P1 — High (BLOCKED)

| # | Issue | Location | Impact |
|---|-------|----------|--------|
| 5 | `models_subst_iff` sorry'd, depends on `partial` Term.subst | Models.lean:451-455 | Blocks proc, ccall, save, run soundness |
| 6 | `heapFragmentOf` axiomatized | Models.lean:622 | Blocks all action rules + frame |
| 7 | Memory model frame property not established | (missing) | Blocks frame rule soundness |

### P2 — Medium

| # | Issue | Location | Impact |
|---|-------|----------|--------|
| 8 | `heapValueHasType` struct/record: no tag/field check | Models.lean:136 | Weak struct typing in models |
| 9 | `opResultType` incomplete (missing bitwise, shift) | HasType.lean:111-115 | Some valid programs can't be typed |
| 10 | `ctypeToBaseType` incomplete (arrays, functions, atomics) | HasType.lean:67-74 | memberof/unspecified blocked for some types |

### P3 — Low

| # | Issue | Location | Impact |
|---|-------|----------|--------|
| 11 | `condTermOfPexpr` assigns `bt = .integer` to all symbols | HasType.lean:83 | Imprecise but harmless |
| 12 | `valueHasType` arrays: `.list _` accepts any element type | HasType.lean:232 | Weak array typing |
| 13 | `PureHasType.let_` only handles named patterns | HasType.lean:357-363 | Incomplete but not unsound |
