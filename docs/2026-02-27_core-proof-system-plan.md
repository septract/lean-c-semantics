# Core Proof System: Separation Logic Over Core AST

*Created: 2026-02-27*
*Branch: `mdd/core-proof-system` (off `cn-types`)*
*Code location: `lean/CerbLean/ProofSystem/`*

## Goal

Define a **separation logic type system** directly over the Cerberus Core AST,
where well-typedness implies memory safety. The key property:

```
Γ; H₁ ⊢ e : τ ⊣ H₂   →   interpreter(e) doesn't UB
```

This decouples **what is verified** (typing rules) from **how verification
works** (CN's proof search). CN becomes untrusted: it produces derivation trees
that Lean's kernel checks. The TCB is just the typing rules + soundness proof.

See `docs/2026-02-27_cn-as-type-system.md` for the design rationale.

---

## Existing Infrastructure to Reuse

We already have significant CN infrastructure on the `cn-types` branch and
partially on `origin/foundational-proofs`. The proof system should build on
these, not duplicate them.

### CN Types (reuse directly)
| File | What it provides | Use in proof system |
|------|-----------------|---------------------|
| `CN/Types/Term.lean` | `IndexTerm`, `Term`, `Const`, `BinOp`, `Subst` | Index terms in `SLProp`, `HasType` rules |
| `CN/Types/Base.lean` | `BaseType`, `Sign` | Type annotations in judgments |
| `CN/Types/Resource.lean` | `ResourceName`, `Init`, `Predicate`, `QPredicate`, `Resource` | Map CN resources ↔ `SLProp` |
| `CN/Types/Constraint.lean` | `LogicalConstraint`, `LCSet` | Pure constraints in `SLProp` |
| `CN/Types/Spec.lean` | `FunctionSpec`, `Clause`, `Precondition`, `Postcondition` | Function specs in typing context |

### CN Semantics (reuse/extend)
| File | What it provides | Use in proof system |
|------|-----------------|---------------------|
| `CN/Semantics/Heap.lean` | `Location`, `HeapValue`, `HeapFragment`, `Valuation` | Concrete heap model for `models` |
| `CN/Semantics/Interpretation.lean` | `interpOwned`, `interpResource`, `interpResources` | Semantic interpretation — basis for `models` |

### Foundational Proofs Branch (`origin/foundational-proofs`)
| File | What it provides | Relevance |
|------|-----------------|-----------|
| `CN/Verification/Obligation.lean` | `Obligation`, `ObligationSet`, `toProp` | May inform VC generation from typing rules |
| `CN/Semantics/PureDenoteSound.lean` | Soundness of pure denotation vs HeapValue | Reusable for pure expression soundness |
| `CN/Verification/PipelineDemo.lean` | End-to-end pipeline examples | Pattern for our examples |
| `docs/2026-01-22_CN_SOUNDNESS_PROOF_PLAN.md` | Earlier soundness proof plan | Shares goals; different architecture |

### CN Coq Formalization (`tmp/cn/coq/`)

The upstream CN repo contains a Coq (Rocq) formalization that validates CN's
resource inference via proof logging. Cloned to `tmp/cn/` for reference.

**Architecture:** CN's OCaml implementation emits a **proof log** — a trace of
resource inference decisions. The Coq code defines when each log entry is valid
and provides tactics to discharge the proofs automatically.

**Key files:**

| File | What it defines |
|------|-----------------|
| `coq/Cn/Request.v` | `init`, `name` (Owned/PName), `Predicate.t`, `QPredicate.t`, `subsumed` |
| `coq/Cn/Resource.v` | `output`, `Resource.t = Request.t × output`, `ResSet` |
| `coq/Cn/Context.v` | `basetype_or_value`, `Context.t`, `get_rs` |
| `coq/Cn/CNMem.v` | `provenance`, `location`, `pointer_value`, `mem_value` (VIP memory model) |
| `coq/Cn/Prooflog.v` | `log_entry` (PredicateRequest / UnfoldResources), `log` |
| `coq/Cn/CNProgs.v` | `CNProgs.t` — minimal program type (CLet load / Statement) |
| `coq/Reasoning/ResourceInference.v` | `log_entry_valid`, `unfold_one`, `unfold_all`, struct unfolding |
| `coq/Reasoning/ProofAutomation.v` | Ltac2 tactics for automated proof log validation |

**What it proves:** Each resource inference step is valid — the matched resource
exists in context, names are subsumed, struct unfolding produces the right field
resources. Three cases:
1. `simple_resource_inference_step` — non-struct: find matching resource, check
   subsumption + pointer/arg equality
2. `struct_resource_inference_step` — struct: unfold via `unfold_one`/`unfold_all`
3. `array_resource_inference_step` — array: placeholder (not yet implemented)

**What it does NOT prove:** No soundness theorem connecting to execution. No
`models` relation. No interpreter. The `CNMem` types are defined but unused
semantically. Pointer equality is shelved via a placeholder
`Inductive provable : ... := solvable_SMT : ...` that accepts everything.

**What we should port/adapt:**
- `unfold_one` / `unfold_all` — struct unfolding as inductive relations with
  computable equivalents and equivalence proofs. Well-proved pattern.
- `struct_piece_to_resource` — decomposing struct fields into per-field resources
- `bt_of_sct_rel` — base type / C type correspondence relation
- `subsumed` relation — `Owned<T>(Uninit)` subsumes `Owned<T>(Init)`

**How our approach differs:**

| | CN Coq (proof log validation) | Our proof system |
|--|-------------------------------|-----------------|
| **Scope** | Resource inference steps only | Full Core AST typing |
| **What it proves** | Each inference step is valid | Well-typed → no UB |
| **Interpreter** | Not referenced | Soundness w.r.t. interpreter |
| **Memory model** | `CNMem` types defined but unused | `models` connects to MemState |
| **SL structure** | Implicit (resource sets) | Explicit (`SLProp` with `star`, `emp`, `ex`) |
| **Core AST** | Only `CNProgs.t` (loads + statements) | Full Core `Expr`/`Pexpr`/`Action` |
| **SMT** | Placeholder `provable` (trusted) | Oracle lemmas (explicit in TCB) |
| **Prover** | Coq | Lean 4 |

The Coq formalization confirms our type definitions are correct (they match
almost exactly), and provides tested patterns for struct unfolding. But it
doesn't attempt what we're building: a compositional type system with a
soundness theorem connecting to execution semantics.

### Key Design Decision: SLProp vs CN's Resource Types

CN's `Resource` type (`CN/Types/Resource.lean`) represents individual resource
claims: `Request × Output`. This is a flat, syntactic representation used by
the algorithmic type checker.

`SLProp` is a **compositional formula language** for separation logic:
`emp`, `star P Q`, `ex x. P`, `pure c`, etc. It needs to exist as a separate
type because:
- CN's `Resource` has no `emp`, `star`, `ex`, `pure` constructors
- The typing rules need compositional heap assertions (e.g., `H₁ ∗ H₂`)
- `HasType` needs `SLProp` as pre/post conditions, not flat resource lists

But `SLProp` should be defined so there's a **clean mapping** between the two:
- `Resource` with `Predicate` → `SLProp.owned` or `SLProp.pred`
- `Resource` with `QPredicate` → `SLProp.each`
- `List Resource` → `SLProp.star` of individual translations
- `LogicalConstraint` → `SLProp.pure`
- `FunctionSpec.requires/ensures` → `SLProp` telescope

And `SLProp`'s semantic interpretation should be compatible with the existing
`interpResources` from `CN/Semantics/Interpretation.lean`.

---

## Scope

### In scope (sequential, no concurrency)
- Core control flow: `pure`, `let_`, `sseq`, `wseq`, `if_`, `case_`
- Memory actions: `create`, `kill`, `load`, `store`
- Procedure calls: `proc`, `ccall`
- Continuations: `save`/`run` (loops)
- Resources: `Owned<T>(p,v)`, `Block<T>(p)`, user predicates
- Iterated resources: `each`
- Pure constraints, existentials
- Soundness proof w.r.t. interpreter

### Out of scope (Phase 1)
- Concurrency: `par`, `unseq`, `wait`, `nd`
- Race detection / neg actions
- Floating point
- Connecting CN proof search to produce `HasType` derivations

---

## Architecture

```
lean/CerbLean/ProofSystem/
├── SLProp.lean             -- Stage 1: heap resource propositions
├── Convert.lean            -- Stage 1: CN Resource ↔ SLProp conversions
├── HasType.lean            -- Stage 2: typing rules (inductive)
├── Models.lean             -- Stage 3: semantic interpretation
├── Soundness/              -- Stage 4: soundness proof
│   ├── Pure.lean           --   pure expression lemmas
│   ├── Action.lean         --   memory action lemmas
│   ├── Expr.lean           --   effectful expression lemmas
│   └── Main.lean           --   top-level theorem
└── Examples/               -- Stage 2+: test derivations
    ├── ReturnLiteral.lean  --   simplest: main returns 0
    ├── LoadStore.lean      --   load then store
    └── Loop.lean           --   simple loop with invariant
```

This is **separate from** `CN/TypeChecking/`. The proof system defines the
declarative rules; `CN/TypeChecking/` is the algorithmic checker. They will be
connected later by having CN produce `HasType` proof terms.

### Dependencies

```
ProofSystem/SLProp.lean
  imports: CN.Types.{Term, Base, Resource, Constraint}
           Core.{Sym, Ctype}

ProofSystem/Convert.lean
  imports: ProofSystem.SLProp
           CN.Types.{Resource, Spec}

ProofSystem/HasType.lean
  imports: ProofSystem.SLProp
           Core.{Expr, Value, Types}
           CN.Types.Spec (for FunctionSpec)

ProofSystem/Models.lean
  imports: ProofSystem.SLProp
           CN.Semantics.{Heap, Interpretation}
           Memory.Concrete
           Semantics.{Monad, State}

ProofSystem/Soundness/
  imports: ProofSystem.{HasType, Models}
           Semantics.{Step, Eval}
```

Does NOT import `CN.TypeChecking.*` — independence from the checker is the
whole point.

---

## Staged Implementation Plan

### Stage 1: SLProp + Conversions

**Goal:** Define `SLProp` and its mapping to/from CN's existing resource types.

**Files:** `SLProp.lean`, `Convert.lean`

**Step 1a: Define `SLProp`.**

Reuses `IndexTerm` from `CN/Types/Term.lean`, `BaseType` from `CN/Types/Base.lean`,
`ResourceName` and `Init` from `CN/Types/Resource.lean`.

```lean
import CerbLean.CN.Types.Term
import CerbLean.CN.Types.Resource

inductive SLProp where
  | emp                                                       -- empty heap
  | owned (ct : Ctype) (init : Init)
          (ptr : IndexTerm) (val : IndexTerm)                 -- Owned<T>(p) = v
  | block (ct : Ctype) (ptr : IndexTerm)                      -- Block<T>(p)
  | pred (name : Sym) (ptr : IndexTerm)
         (iargs : List IndexTerm) (oarg : IndexTerm)          -- user predicate
  | star (P Q : SLProp)                                       -- P ∗ Q
  | each (qp : QPredicate) (oarg : IndexTerm)                 -- iterated ∗
  | pure (c : LogicalConstraint)                              -- pure constraint
  | ex (var : Sym) (ty : BaseType) (body : SLProp)            -- ∃x:τ. P
```

Note: `owned` includes `Init` (init/uninit) matching CN's `ResourceName.owned`.
The `each` case wraps CN's existing `QPredicate` rather than reinventing it.
`pure` wraps `LogicalConstraint` (which already handles `∀`).

**Step 1b: Conversions between CN types and `SLProp`.**

```lean
-- Single CN Resource → SLProp
def SLProp.ofResource : Resource → SLProp

-- CN Resource list → SLProp (separating conjunction)
def SLProp.ofResources : List Resource → SLProp

-- CN FunctionSpec → (SLProp precondition, SLProp postcondition)
def SLProp.ofSpec : FunctionSpec → (SLProp × SLProp)
```

**Step 1c: Basic operations.**
- `SLProp.flatten : SLProp → List SLProp` (flatten nested stars)
- `SLProp.starAll : List SLProp → SLProp` (list to star chain)
- `Repr`/`ToString` for debugging

**Deliverable:** `SLProp` compiles, conversions from CN types work, basic tests.

**Estimated effort:** Small. Mostly type definitions + straightforward mapping.

---

### Stage 2: Typing Rules

**Goal:** Define `HasType` — the inductive type whose constructors are the
typing rules. Each constructor corresponds to one Core expression form.

**File:** `HasType.lean`

**The judgment:**
```lean
inductive HasType : Ctx → SLProp → AExpr → BaseType → SLProp → Prop where
  -- Γ; H₁ ⊢ e : τ ⊣ H₂
```

where `Ctx` carries:
```lean
structure Ctx where
  vars : List (Sym × BaseType)       -- variable bindings
  pathConds : List LogicalConstraint  -- path conditions from branches
  funSpecs : Sym → Option FunSpec     -- function pre/post specs
  labelInvs : Sym → Option LabelInv  -- loop invariant per label
  tagDefs : TagDefs                   -- struct/union definitions
  implDefs : ImplDefs                 -- sizeof, alignof, ranges
```

Note: `FunSpec` is reused from `CN/Types/Spec.lean`. `LabelInv` is new
(loop invariant = SLProp parameterized by label arguments).

**Typing rules to define (in order of difficulty):**

1. **Pure** — `pure(pe)` doesn't change heap
2. **Let** — `let x = pe in e` binds a pure expression
3. **Strong seq** — `sseq x = e1 in e2` threads resources
4. **Weak seq** — same as strong (sequential subset)
5. **If/else** — branches from same pre-heap, join post-heaps
6. **Case** — generalized conditional
7. **Load** — consume `Owned<T>(p, v)`, return `v`, re-emit resource
8. **Store** — consume `Owned<T>(p, v_old)`, emit `Owned<T>(p, v_new)`
9. **Create** — emit `Block<T>(p)` for fresh `p`
10. **Kill** — consume `Owned<T>(p, v)` or `Block<T>(p)`
11. **Proc call** — consume pre-resources, emit post-resources
12. **Save/Run** — loop invariant checking
13. **Frame** — framing rule (admissible, but useful to state)

**Also needed:**
- `LabelInv` type (loop invariant as SLProp parameterized by args)
- `PureHasType` for `Pexpr` typing (simpler — no heap change)
- Entailment notion: `SLProp.entails H₁ H₂` (possibly just propositional, not
  decidable — entailment proofs come from the derivation)

**Example derivation (test that rules work):**

```lean
-- main() returns 0
-- Core: proc main() = pure(0)
example : HasType emptyCtx .emp (pure_zero_expr) .integer .emp :=
  .pure (PureHasType.val ...)
```

Write 2-3 example derivations in `Examples/` to validate the rules are usable.

**Deliverable:** `HasType` compiles, example derivations type-check.

**Estimated effort:** Medium. The typing rules are well-understood from the
design doc, but getting the Lean encoding right (especially for dependent
telescopes in function specs) will take iteration.

---

### Stage 3: Semantic Interpretation (`models`)

**Goal:** Define the `models` relation connecting `SLProp` to concrete memory
states from the interpreter.

**File:** `Models.lean`

This **extends** the existing `interpResources` from
`CN/Semantics/Interpretation.lean`. The existing code already defines:
- `interpOwned ct loc initState v h` — singleton heap for Owned
- `interpResource res ρ h` — single resource against a heap fragment
- `interpResources rs ρ h` — resource list as separating conjunction

We need to generalize this from `List Resource` to `SLProp`:

```lean
def models (ρ : Valuation) (H : SLProp) (h : HeapFragment) : Prop :=
  match H with
  | .emp => h = HeapFragment.empty
  | .owned ct init ptr val =>
      -- Reuse interpOwned after evaluating ptr/val via ρ
      ...
  | .star P Q =>
      ∃ h1 h2, h1.disjoint h2 ∧ h = h1 ++ h2 ∧
      models ρ P h1 ∧ models ρ Q h2
  | .pure c => constraintToProp ρ c ∧ h = HeapFragment.empty
  | .ex var ty body => ∃ v, models ((var, v) :: ρ) body h
  | ...
```

**Compatibility lemma:** For the conversion `SLProp.ofResources rs`:
```lean
theorem models_ofResources_iff :
  models ρ (SLProp.ofResources rs) h ↔ interpResources rs ρ h
```

This ensures the new system is compatible with the existing semantics.

**Bridge to interpreter:** We also need to connect `HeapFragment` (from CN
semantics) to `MemState` (from the interpreter). The existing code in
`CN/Semantics/Heap.lean` provides `Location`, `HeapValue`, `HeapFragment`.
We need:

```lean
def stateModels (σ : InterpState) (ρ : Valuation) (H : SLProp) : Prop :=
  ∃ h : HeapFragment,
    heapFragmentOf σ.memState = h ∧  -- extract heap from interpreter state
    models ρ H h
```

**Strategy:** Start with `models` over `HeapFragment` (reusing existing
infrastructure), then tackle the `InterpState ↔ HeapFragment` bridge
separately.

**Deliverable:** `models` defined for all `SLProp` constructors, compatibility
with `interpResources` proved, basic properties.

**Estimated effort:** Medium-hard. The `SLProp` → `HeapFragment` part reuses
existing code. The `InterpState` → `HeapFragment` bridge is new but scoped.

---

### Stage 4: Soundness Proof

**Goal:** Prove the main theorem:

```lean
theorem soundness :
  HasType Γ H₁ e τ H₂ →
  stateModels σ ρ H₁ →
  ctxModels σ ρ Γ →
  ∃ v σ',
    runInterp e σ = .ok (v, σ') ∧
    hasBaseType v τ ∧
    stateModels σ' ρ' H₂  -- ρ' extends ρ with new bindings
```

**Structure:** One lemma per typing rule constructor:

```
Soundness/
├── Pure.lean    -- pure expression evaluation preserves models
├── Action.lean  -- create/kill/load/store preserve models
├── Expr.lean    -- let/seq/if/case/call/run preserve models
└── Main.lean    -- top-level induction
```

**Strategy for tractability:**
- Start with a **subset**: prove soundness for `pure`, `let`, `sseq`, `load`,
  `store`, `create`, `kill`. This covers the core memory safety story.
- Add `if_`, `case_`, `proc`, `save`/`run` incrementally.
- Use `sorry` liberally at first to get the proof structure right, then fill.
- Reuse `PureDenoteSound.lean` lemmas from foundational-proofs where applicable.

**Deliverable:** Soundness theorem stated and proved for the core subset.

**Estimated effort:** Large. This is the bulk of the project.

---

### Stage 5: Connect to CN (future)

**Goal:** Have the CN type checker produce `HasType` derivation trees instead
of ad-hoc obligations.

This is NOT in scope for the initial implementation. The proof system should be
designed so this connection is possible, but building it requires the CN
checker to be mature enough.

**Sketch:**
- CN TypeChecking currently returns `Except String Unit` (pass/fail)
- Refactor to return `Except String (HasType Γ H₁ e τ H₂)` (proof term)
- Each resource inference step produces a proof witness
- SMT calls become oracle lemmas (trusted but explicit)

---

## Risk Assessment

| Risk | Mitigation |
|------|------------|
| `models` too complex | Build on existing `interpResources`; start without `star` splitting |
| Soundness proof too large | Prove core subset first; use `sorry` for arithmetic |
| Index term mismatch with interpreter | Test with concrete examples early (Stage 2) |
| CN types change under us | Only import `CN.Types.*` (stable); not `CN.TypeChecking.*` |
| `HasType` rules don't match interpreter | Write examples that exercise both paths |
| SMT/pointer equality gap | Same gap as CN Coq formalization; use explicit oracle axiom (in TCB) |

### The SMT Oracle

Both CN's Coq formalization and our proof system face the same fundamental gap:
pointer equality and arithmetic constraints require an SMT solver. The Coq code
uses a placeholder `provable` that accepts everything. We should be explicit:

```lean
-- Oracle axiom: SMT solver is correct
axiom smt_oracle : (lcs : LCSet) → (lc : LogicalConstraint) →
  smtCheck lcs lc = .sat → entails lcs lc
```

This axiom is in the TCB. It says: if the SMT solver says `lc` follows from
`lcs`, then it does. This is the standard approach (same as Dafny, Why3, F*).
The key property is that the axiom is **stated explicitly** — we know exactly
what we're trusting.

## Success Criteria

1. **Stage 1 done:** `SLProp` defined, converts to/from CN `Resource` types
2. **Stage 2 done:** `HasType` defined, 3+ example derivations type-check
3. **Stage 3 done:** `models` defined, compatible with `interpResources`
4. **Stage 4 done:** Soundness proved for {pure, let, sseq, load, store,
   create, kill}
5. **End state:** Well-typed programs provably don't UB (for the covered subset)

## What We Learn

Even if we only get through Stage 2, we learn:
- Whether the typing rules are expressible in Lean 4
- Whether they're usable (can we build derivations?)
- Whether they match the interpreter's behavior (via examples)

Stage 3-4 are where the real payoff is, but Stages 1-2 are valuable on their own
as a formal specification of "what CN verifies."
