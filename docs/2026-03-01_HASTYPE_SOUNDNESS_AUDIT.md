# HasType / PureHasType Soundness Amenability Audit

**Date**: 2026-03-01
**Scope**: `lean/CerbLean/ProofSystem/HasType.lean`, `Models.lean`, `SLProp.lean`
**Goal**: Identify rules that are unsound or unprovably sound, without writing proofs.

## Methodology

For each rule in `PureHasType` and `HasType`, three questions:

1. **Could I state the soundness lemma?** For `PureHasType Γ pe τ`: if the context
   is satisfied by a state/valuation, then evaluating `pe` produces a value of type τ.
   For `HasType Γ H₁ e τ H₂`: if the heap satisfies H₁, then evaluating `e` does not
   trigger UB, returns a value of type τ, and the resulting heap satisfies H₂.
2. **Could I prove it?** Does each premise correspond to something the interpreter
   checks or produces?
3. **Are implicit parameters constrained?** Universally quantified type variables that
   appear in the conclusion but aren't determined by any premise allow proving HasType
   at the wrong type.

## Verdicts

- **SOUND**: Amenable to soundness proof with existing infrastructure
- **SOUND (with caveat)**: Amenable but requires a specific lemma or assumption
- **UNSOUND**: Admits programs that go wrong
- **BLOCKED**: Rule is correct but proof requires infrastructure that doesn't exist

---

## PureHasType Rules

### `PureHasType.val` — SOUND (with caveat)

The `valueHasType` premise constrains the value-type relationship with explicit
matches for all Core value constructors. The integer→bits case is permissive (any
integer matches any bits width), and array→list doesn't check element types
(documented divergence). These are overapproximations that admit more programs
than CN would, but are fine for UB-freedom soundness.

**Caveat**: A soundness proof needs a bridge lemma:
`valueHasType v τ → heapValueHasType (heapValueOfCoreValue v) τ` connecting Core
`Value` to CN `HeapValue`. This doesn't exist yet.

### `PureHasType.sym` — SOUND

Standard variable lookup. Soundness maintains an invariant that the context agrees
with the interpreter environment.

### `PureHasType.op` — SOUND (with caveat)

`opResultType` determines the result type. For arithmetic ops, returns the left
operand type; for comparisons/logical ops, returns `.bool`.

**Caveat**: The interpreter's `evalBinop` may trigger UB (division by zero, signed
overflow). The typing rule doesn't check for UB — it assumes the operation succeeds.
Soundness proof needs: "if the interpreter evaluates the binop without UB, the result
has the claimed type."

### `PureHasType.if_` — SOUND

Standard conditional: condition must be bool, both branches same type τ.

### `PureHasType.not_` — SOUND

Logical NOT on bool returns bool.

### `PureHasType.let_` — SOUND

Standard let binding.

### `PureHasType.arrayShift` — SOUND (with caveat)

Returns `.loc` given a pointer input. The index expression `idx` has no type
constraint. Not unsound (pointer arithmetic is defined at the expression level;
UB is at the memory access level), but weaker than CN would enforce.

### `PureHasType.memberShift` — SOUND

Returns `.loc` given a pointer. Same analysis as arrayShift.

### `PureHasType.struct_` — SOUND

Each field is typed, result is `.struct_ tag`.

### `PureHasType.memberof` — SOUND

Requires `lookupTagDef`, finds the field's Ctype, converts via `ctypeToBaseType`.
`ctypeToBaseType` handles integer, floating, pointer, struct/union, void, array,
atomic types. Missing: function types, qualified types beyond atomic. The `Option`
return type means it fails explicitly for unhandled cases.

### `PureHasType.convInt` — SOUND (with caveat)

Result type is `intTypeToBaseType ity`, deterministic from the target integer type.

**Caveat**: Integer truncation/wrapping during cast may produce implementation-defined
behavior. The typing rule doesn't account for this.

### `PureHasType.isScalar/isInteger/isSigned/isUnsigned/areCompatible` — SOUND

All return `.bool`. Trivial.

### `PureHasType.case_` — SOUND

Standard case analysis with pattern bindings.

### `PureHasType.wrapI` — SOUND

Wrapping arithmetic: result type is `intTypeToBaseType ity`. Cannot UB by definition.

---

## HasType Rules

### `HasType.pure` — SOUND

Pure expression wrapped in `Expr.pure`. No heap change.

### `HasType.let_` / `HasType.let_wild` — SOUND

Standard let binding with heap threading.

### `HasType.sseq` / `HasType.sseq_wild` — SOUND

Standard sequencing: heap threads H₁ → H₂ → H₃.

### `HasType.wseq` / `HasType.wseq_wild` — SOUND

Same as sseq for sequential semantics.

### `HasType.if_` — SOUND (with caveat)

Both branches must produce the same type τ and post-heap H₂. Path conditions
added via `condTermOfPexpr`.

**Analysis of `condTermOfPexpr`**: Handles `.sym`, `.not_`, `.op` with eq/lt/le/gt/ge.
The gt→lt and ge→le flips correctly swap operands: `a > b ↔ b < a`.
`condTermOfPexpr` returns `none` for unhandled conditions, making the rule
inapplicable — restrictive but not unsound.

### `HasType.case_` — SOUND

Standard case with pattern bindings.

### `HasType.bound` / `HasType.annot` / `HasType.excluded` — SOUND

Transparent wrappers.

### `HasType.action_load` — SOUND (with caveats)

**Rule**: Consumes `Owned<ct>(init, ptr, val) ∗ R`, returns `val.bt`, same heap.

**Concern — `val.bt` as return type**: Is `val.bt` guaranteed to match the actual
heap value's type? Yes: `models` for `.owned ct .init ptr val` requires
`heapValueHasType v val.bt`, so `val.bt` correctly describes the value.

**Caveat**: Soundness proof needs the `heapFragmentOf` bridge (sorry'd) to connect
the interpreter's `loadImpl` return value to what `models` asserts.

### `HasType.action_store` / `HasType.action_store_block` — SOUND (with caveats)

**Rule**: Store consumes `Owned<ct>(init, ptr, valOld) ∗ R`, produces
`Owned<ct>(init, ptr, valNew) ∗ R`. `valNew.bt = τ` ensures the type annotation
matches.

**Caveat**: Soundness proof needs: if `cval` has type τ (via PureHasType) and
`memValueFromValue ty cval = some mval`, then `heapValueOfMemValue mval` has
type τ. This is the value-conversion bridge, not yet proven.

### `HasType.action_create` — SOUND

Produces `Block<ct>(⟨.sym ptrSym, .loc, default⟩) ∗ H`. The `ptrSym` is
existentially quantified. Could a derivation reuse the same `ptrSym` for two
creates? Syntactically yes, but `models` for `star` requires disjoint heap
fragments. Both would look up `ptrSym` in the same valuation, getting the same
location, violating disjointness. So the disjointness enforcement in `models`
prevents unsound reuse.

### `HasType.action_kill_owned` / `HasType.action_kill_block` — SOUND

Consumes the resource, leaves the frame. Returns `.unit`.

### `HasType.proc` — SOUND (with caveats)

Looks up spec, substitutes actual args into pre/post via `substTotal σ`.

**Caveat 1**: `models_substTotal_extend` is sorry'd — blocks the semantic bridge.

**Caveat 2**: Substitution-conversion commutativity not proven:
`SLProp.ofPrecondition (pre.substTotal σ) ≡ (SLProp.ofPrecondition pre).substTotal σ`.
Needed but not stated.

### `HasType.ccall` — SOUND (with caveats)

Same as `proc` but ties function pointer to known symbol via `PexprMatchesTerm`.

### `HasType.memop_ptrCmp` / `memop_ptrValid` — SOUND

Return `.bool`, heap unchanged.

### `HasType.memop_ptrArrayShift` / `memop_ptrMemberShift` — SOUND

Return `.loc`, heap unchanged.

### `HasType.memop_intFromPtr` / `memop_ptrFromInt` / `memop_ptrdiff` — SOUND

Fixed return types, heap unchanged.

### `HasType.memop_memcpy` — UNSOUND

**Rule claims `H → H` (heap unchanged) but the interpreter modifies the
destination.** If `H` contains an `Owned` resource at the memcpy destination,
the postcondition is false after execution.

**Example**: `H = Owned<int>(ptr, old_val)`. After `memcpy(ptr, src, 4)`,
the value at `ptr` is whatever was at `src`, not `old_val`. But the rule
claims H still holds, which asserts `old_val` is still there.

**Fix options**:
1. Consume destination resource and re-emit with existentially quantified value
2. Require the pre-heap to not contain Owned at the destination (hard to enforce)
3. Keep conservative but change to consume destination and re-emit as Block

### `HasType.memop_memcmp` — SOUND

Returns `.bits .signed 32`, heap unchanged. Read-only.

### `HasType.save` — SOUND (with caveats)

**Caveat**: `models_substTotal_extend` (sorry'd) is the key bridge.

### `HasType.run` — SOUND (with caveats)

Post-heap `H₂` and return type `τ` are unconstrained — correct because `run`
transfers control and doesn't return.

**Caveat**: Same `models_substTotal_extend` dependency.

### `HasType.frame` — SOUND (with caveat)

**Caveat**: Requires the frame property of the interpreter (each action only
modifies locations in its footprint). Stated but sorry'd:
`store_preserves_frame`, `kill_removes_cell`, `allocate_fresh`.

### `HasType.consequence` — SOUND

`SLProp.entails` quantifies over all valuations ρ, which is stronger than needed
but standard and compositional.

---

## Prioritized Issue List

### P0 — UNSOUND

| # | Issue | Location | Fix |
|---|-------|----------|-----|
| 1 | `memop_memcpy` claims heap unchanged but interpreter modifies destination | HasType.lean:754-756 | Consume destination Owned, re-emit with existential value |

### P1 — BLOCKED (sorry'd infrastructure)

| # | Issue | Location | Difficulty |
|---|-------|----------|------------|
| 2 | `models_substTotal_extend` sorry'd | Models.lean:472 | Medium |
| 3 | `heapFragmentOf` sorry'd | Models.lean:655 | High |
| 4 | Frame property lemmas sorry'd | Models.lean:679-704 | Medium-high |
| 5 | `models_substTotal_iff` sorry'd | Models.lean:477 | Medium |

### P2 — Missing bridge lemmas (needed but not yet stated)

| # | Issue | Status |
|---|-------|--------|
| 6 | `valueHasType v τ → heapValueHasType (heapValueOfCoreValue v) τ` | Not stated |
| 7 | `ofPrecondition (pre.substTotal σ) = (ofPrecondition pre).substTotal σ` | Not stated |
| 8 | `PexprMatchesTerm` correctness: eval pe ↔ evalIndexTerm it | Not stated |

### P3 — Design limitations (not unsound, but restrictive)

| # | Issue | Location |
|---|-------|----------|
| 9 | `substTotal` doesn't handle struct_, tuple, let_, match_, eachI, apply | Term.lean:648 |
| 10 | `SLProp.substTotal` returns `.each` unchanged | SLProp.lean:141 |
| 11 | `LogicalConstraint.substTotal` is identity on `.forall_` | SLProp.lean:122 |
| 12 | `models` returns `False` for `.pred` and `.each` | Models.lean:212-214 |

### P4 — Minor

| # | Issue | Location |
|---|-------|----------|
| 13 | `intTypeToBaseType .char` assumes unsigned | HasType.lean:47 |
| 14 | `ctype_ToBaseType .union_` maps to `.struct_ tag` | HasType.lean:63 |
| 15 | `valueHasType` for arrays has no element type checking | HasType.lean:233 |

---

## Resolutions (2026-03-01)

### Issue #1 (P0): `memop_memcpy` unsound `H → H` rule — FIXED

Replaced with CN-faithful byte-level `each` resource rule (HasType.lean).
The new rule:
- Pre-heap: `each(qpDst, dstOut) ∗ each(qpSrc, srcOut) ∗ R` where
  destination is `Owned<byte>(uninit)` and source is `Owned<byte>(init)`
- Post-heap: destination becomes `Owned<byte>(init)` with copied content,
  source unchanged
- Premises constrain QPredicate names, step types to `Ctype.byte`

### Issue #9 (P3): `substTotal` coverage — FIXED

Rewrote `Term.substTotal` (Term.lean) using well-founded recursion
(`termination_by sizeOf`) to handle ALL Term constructors:

- **Non-binding constructors** (~30): All handled with explicit pattern matches.
  Single-arg (head, tail, hasAllocId, cnSome, isSome, getOpt, good,
  representable, wrapI, mapConst, recordMember), two-arg (cons, aligned,
  copyAllocId, mapGet), three-arg (mapSet, structUpdate, recordUpdate).

- **List-arg constructors** (struct_, tuple, record, constructor, apply):
  Now fully handled via `List.map` with well-founded recursion. Uses
  projections (`at_.term`, `p.2.term`) instead of destructuring to help
  the termination prover. Custom helper lemmas `AnnotTerm.term_sizeOf_lt`
  and `AnnotTerm.term_sizeOf_lt_of_pair` provide the sizeOf chain.

- **Binding forms** (let_, eachI, mapDef): Now have real capture-avoiding
  substitution using `freshSymFor` for alpha-renaming, mirroring
  `SLProp.substTotal`'s `.ex` case.

- **match_**: Still `panic!` — needs `Pattern.boundVarIds` which is `partial`.

- **Identity fallback** (`| other => other`): only reached by truly zero-arg
  constructors (nil, sizeOf, offsetOf, cnNone) where identity is correct.

Note: well-founded recursion doesn't reduce definitionally, so proofs that
previously used `rfl` now use `simp` with `Term.substTotal` equation lemmas
(see Loop.lean examples).

### Issue #10 (P3): `SLProp.substTotal` identity for `.each` — FIXED

Replaced with real substitution (SLProp.lean):
```lean
| .each qp oarg => .each (qp.substTotal σ) (AnnotTerm.substTotal σ oarg)
```
Uses existing `QPredicate.substTotal` (Resource.lean:183-189).

### Issue #11 (P3): `LogicalConstraint.substTotal` identity for `.forall_` — FIXED

Replaced with capture-avoiding substitution (SLProp.lean), mirroring the
pattern from `SLProp.substTotal`'s `.ex` case and `LogicalConstraint.subst`
(Constraint.lean:44-48). Alpha-renames the bound variable when it conflicts
with the substitution's relevant set.

### Issue #12 (P3): `models` returns `False` for `.each` — FIXED

Replaced with real iterated separating conjunction semantics (Models.lean).
The `.each qp oarg` case now:
1. Existentially quantifies a list of indices and heap fragments
2. Requires each index satisfies the permission guard (`evalEachPermission`)
3. Requires fragments are pairwise disjoint (`pairwiseDisjoint`)
4. Requires the heap is the union of fragments (`concatFragments`)
5. Requires each fragment models the instantiated resource (`modelsEachEntry`)

`modelsEachEntry` is defined separately (not recursively through `models`)
to preserve structural termination. It inlines the `.owned` semantics
for Owned resources. User predicates (`.pname`) remain unsupported (`False`).

The `models_equiv` proof was updated for the new `.each` case (equiv
transfers through `HeapFragment.equiv_trans`).

### Issues #6, #7, #8 (P2): Missing bridge lemmas — STATED

Added sorry'd bridge lemma statements:

**In Models.lean:**
- `ofPrecondition_substTotal_comm`: substitution-conversion commutativity
  for preconditions (issue #7)
- `ofPostcondition_substTotal_comm`: same for postconditions (issue #7)

**In HasType.lean** (avoids circular dependency with Models.lean):
- `valueHasType_implies_heapValueHasType`: Core Value → HeapValue type
  preservation through memValueFromValue/heapValueOfMemValue (issue #6)
- `envValuationCompat`: compatibility definition for env/valuation pairs
- `pexprMatchesTerm_eval_compat`: PexprMatchesTerm correctness (issue #8)

### Issues #2-#5 (P1): Sorry'd infrastructure — UNCHANGED

Frame property lemma comments (issues #4) improved with detailed TODO
descriptions of intended real hypotheses and proof strategies:
- `store_preserves_frame`: needs `storeImpl ct false ptr mval st = .ok ((), st')`
- `kill_removes_cell`: needs `killImpl kind ptr st = .ok ((), st')`
- `allocate_fresh`: needs `createImpl align ct prefix_ st = .ok (ptr, st')`

`models_substTotal_extend` (#2), `heapFragmentOf` (#3), and
`models_substTotal_iff` (#5) remain sorry'd — no changes.

### Issues #13-#15 (P4): Minor — UNCHANGED

These are intentional simplifications/divergences, not incorrect.
