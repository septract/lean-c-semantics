# Proof System Audit: Stages 1-3 Implementation

*Created: 2026-02-27*
*Updated: 2026-02-27 (fixes applied)*
*Auditors: slprop-auditor, hastype-auditor, models-auditor*
*Files audited: SLProp.lean, HasType.lean, Models.lean, Convert.lean, Examples/ReturnLiteral.lean*

## Executive Summary

| Stage | Status | Assessment |
|-------|--------|------------|
| **Stage 1** (SLProp + Convert) | **95%** | Solid foundation, letBinding scoping still FIXME |
| **Stage 2** (HasType) | **85%** | 16 rules implemented, consequence still uses equality |
| **Stage 3** (Models) | **75%** | Heap equiv fixed, evalIndexTerm extended, 3 sorrys remain |
| **Stage 4** (Soundness) | 0% | Blocked by interpreter bridge + remaining sorrys |

---

## Blocking Issues (must fix before soundness work)

### B1: Heap-as-list breaks separation logic algebra
`HeapFragment.cells : List (Location x HeapValue)` is a list, not a set.
- `models_star_comm` is **unprovable** (`h1 ++ h2 != h2 ++ h1` for lists)
- `models_star_assoc_forward` is tedious but provable
- Duplicate locations are representable

**Fix options:**
1. Quotient type (commutativity becomes trivial)
2. `Finmap`/`RBMap` (canonical ordering)
3. Change `star` case in `models` to use set-theoretic composition:
   `h.equiv (h1.union h2)` where `equiv` means same lookups
4. Use `Multiset`

**Recommendation:** Option 3 (least disruptive — keep HeapFragment, fix `models`).

### B2: No interpreter bridge
`stateModels`, `heapFragmentOf`, `ctxModels` are all missing. Cannot state
soundness theorem. The interpreter's `MemState` uses byte-level storage
(`Std.HashMap Nat AbsByte`) while `HeapFragment` uses typed values. Bridging
requires deserialization.

### B3: evalConstraint degrades to True
Any constraint that isn't a simple integer comparison becomes `True`. This
makes soundness vacuously true for most programs — formally "sound" but
meaningless. At minimum need: pointer equality, boolean values, bitvector
comparisons.

---

## Critical Gaps

### G1: No memory action rules in HasType
The plan lists load/store/create/kill as rules 7-10. None are implemented.
Without these, the system cannot type any expression that touches memory.
The only derivable program is `return <literal>`.

### G2: Telescope scoping lost in Convert
`SLProp.ofClauses` maps each clause independently, losing CN's sequential
binding structure (`take v = Owned<int>(p); v > 0` — the `v` is unbound
in the second clause). Need `SLProp.ex` wrappers for resource outputs.

### G3: PureHasType.val has zero premises
Admits any value at any type. Makes the type system vacuously "sound" —
every expression can be typed at every type. Need a `valueHasType v tau`
side condition.

### G4: No proc rule
Cannot verify function calls. Blocks multi-function verification.

### G5: evalIndexTerm only handles 3 cases
Only `sym`, `pointer`, `null`. Missing: integer/bitvector/boolean constants,
binary ops, pointer arithmetic (arrayShift/memberShift). Limits what can
be meaningfully modeled.

### G6: Compatibility lemma missing
`models_ofResources_iff : models rho (SLProp.ofResources rs) h <-> interpResources rs rho h`
is not started. Also missing prerequisite `SLProp.ofResources`.

---

## Issues (implemented but wrong or too permissive)

### I1: if_ rules don't add path conditions
Both `HasType.if_` and `PureHasType.if_` use the same context for both
branches. Plan says to add `c = true` / `c = false` to context. The
infrastructure exists (`Ctx.addPathCond`) but isn't used. Blocks dead code
reasoning.

### I2: PureHasType.op has no operator typing
Result type is universally quantified with no relation to input types or
operator. `3 + 5` could be typed as `.bool`.

### I3: consequence uses equality, not entailment
Uses `H1' = H1` instead of `SLProp.entails H1' H1`. Blocks any real
resource rearrangement (star commutativity, existential instantiation).

### I4: block vs interpOwned inconsistency
`models` for `block` requires exactly `HeapValue.uninitialized ct`, while
`interpOwned` with `.uninit` accepts any value. Subtle semantic mismatch.

### I5: owned none -> emp in Convert
Silently drops unresolved resource. Should fail explicitly per
"fail, never guess" rule.

### I6: letBinding -> emp in Convert
Discards the name binding. Combined with G2, references to let-bound
names are dangling.

### I7: Pattern matching only handles base patterns with Some name
Both `let_` and `sseq` only match `Pattern.base (some x) bty`. Wildcards
and constructor patterns unsupported.

---

## What's Correct

- SLProp: all 8 constructors match plan exactly
- Convert: basic Resource/Clause/Spec -> SLProp mapping is correct
- HasType.pure, let_, sseq: heap threading logic is correct
- HasType.frame: standard separation logic frame rule, correctly stated
- models: structure matches plan, correct reuse of interpOwned
- models_emp, models_pure: fully proved
- pred/each returning False: correct per fail-never-guess
- SLProp.entails: correctly defined
- ReturnLiteral example: works (though trivially, due to I3/G3)

---

## Priority Action Items

### P0 (Fix before any further work)
1. ~~Fix heap representation for star commutativity (B1)~~ DONE
2. ~~Tighten PureHasType.val with valueHasType premise (G3)~~ DONE
3. ~~Add load/store/create/kill HasType rules (G1)~~ DONE

### P1 (Needed for meaningful proofs)
4. ~~Fix telescope scoping in Convert (G2)~~ DONE
5. ~~Extend evalIndexTerm: integer/boolean constants, equality (G5)~~ DONE (partial)
6. ~~Fix evalConstraint: boolean/pointer handling (B3)~~ DONE (partial)
7. Strengthen consequence to use SLProp.entails (I3) — REMAINING
8. ~~Add wseq rule (G4)~~ DONE
9. ~~Add proc rule (G4)~~ DONE
10. ~~Fix if_ to add path conditions (I1)~~ DONE (true branch only)

### P2 (Needed for Stage 4)
11. Define stateModels bridge (B2) — REMAINING
12. Define ctxModels (B2) — REMAINING
13. Prove models_ofResources_iff (G6) — STATED, sorry
14. ~~Add case_ rule~~ DONE, operator typing for PureHasType.op — REMAINING
15. ~~Write LoadStore.lean example: `*p = *p + 1`~~ DONE

### P3 (Future)
16. save/run rules for loops
17. Predicate fold/unfold mechanism
18. SMT oracle axiom
19. Extend evalIndexTerm for arrayShift/memberShift
20. Prove `union_lookup_comm` and `models_star_assoc_forward` (close sorrys)
21. Fix letBinding scoping in Convert (I6)

---

## Fixes Applied (2026-02-27)

### Fixed (Blocking)
- **B1** FIXED: `star` case in `models` now uses `HeapFragment.equiv` (lookup-based equivalence) instead of list equality. `models_star_comm` proved modulo `union_lookup_comm` (sorry).
- **B3** PARTIALLY FIXED: `evalConstraint` now handles pointer truthiness (non-null → True, null → False) and `evalIndexTerm` handles `.z`, `.bits`, `.bool` constants.

### Fixed (Critical Gaps)
- **G1** FIXED: Added `action_load`, `action_store`, `action_create`, `action_kill_owned`, `action_kill_block` to HasType.
- **G2** FIXED: `ofClausesScoped` replaces flat `ofClauses` — wraps resource outputs in `SLProp.ex` for telescope scoping.
- **G3** FIXED: `PureHasType.val` now requires `valueHasType v τ` premise.
- **G4** FIXED: Added `proc` rule to HasType (simplified — doesn't connect args to spec params).
- **G5** PARTIALLY FIXED: `evalIndexTerm` extended with `.z`, `.bits`, `.bool` cases. Binary ops and pointer arithmetic still missing.
- **G6** STATED: `models_ofResources_iff` theorem stated with sorry. `SLProp.ofResources` defined in Convert.lean.

### Fixed (Issues)
- **I1** PARTIALLY FIXED: `if_` true branch gets path condition via `Ctx.addPathCond`. False branch still lacks negated condition (needs `negateCondTerm`).
- **I4** FIXED: `block` case in `models` now delegates to `interpOwned` with `.uninit` for consistency.
- **I5** FIXED: `owned none` in Convert now produces unsatisfiable `pure(false)` instead of `emp`.
- **I7** FIXED: Added `let_wild`, `sseq_wild`, `wseq_wild` variants for wildcard patterns.

### Also Added
- `wseq` and `wseq_wild` rules (weak sequencing).
- `case_` rule (simplified — doesn't track pattern bindings).
- `bound` rule (transparent wrapper).
- `valueHasType` function relating Core values to CN base types.
- `HeapFragment.equiv` definition for lookup-based heap equivalence.
- `LoadStore.lean` example: typing derivation for `*p = *p + 1`.

### Remaining
- **B2** (interpreter bridge): Still missing — `stateModels`, `heapFragmentOf`, `ctxModels`.
- **I2** (operator typing): `PureHasType.op` still doesn't constrain result type.
- **I3** (consequence): Still uses equality, not `SLProp.entails`.
- **I6** (letBinding): Still skips name binding in `ofClausesScoped` (FIXME comment).
- 3 `sorry`s in Models.lean: `union_lookup_comm`, `models_star_assoc_forward`, `models_ofResources_iff`.

---

## Distance from `*p = *p + 1`

~~This minimal memory-touching program requires:~~
~~1. action_load (to read *p) — MISSING~~
~~2. PureHasType.op with proper typing (to add 1) — WEAK (no operator typing)~~
~~3. action_store (to write back) — MISSING~~
~~4. sseq to chain them — IMPLEMENTED~~
~~5. frame to carry extra resources — IMPLEMENTED~~
~~6. consequence with entailment for resource rearrangement — WEAK (equality only)~~

**DONE**: `Examples/LoadStore.lean` contains a complete typing derivation for
`*p = *p + 1` using `action_load`, `action_store`, `sseq`, and `pure`.
The derivation type-checks successfully.
