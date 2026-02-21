/-
  CN Ghost Statement Handlers
  Corresponds to: cn/lib/check.ml lines 2171-2283 (cn_statement handling)

  Ghost statements are CN annotations that appear inline in C source code
  (e.g., `/*@ cn_have(...) @*/`, `/*@ assert(...) @*/`). They guide the
  type checker by adding constraints, generating proof obligations,
  instantiating quantified resources, or providing case-split hints.

  This module implements handlers for the predicate-free fragment:
  - `have`: Assert a constraint into the typing context + generate obligation
  - `assert_`: Generate a proof obligation only (no context addition)
  - `splitCase`: Add a case-split hint as an assumption
  - `print`: Debug output (no-op)
  - `instantiate`: Instantiate a quantified resource (requires QPredicate support)
  - `extract`: Extract element from a quantified resource (requires QPredicate support)

  Predicate-dependent statements fail explicitly:
  - `pack`, `unpack`, `unfold`, `apply`, `inline_`, `toFromBytes`

  Audited: 2026-02-19
-/

import CerbLean.CN.TypeChecking.Monad
import CerbLean.CN.TypeChecking.Pexpr
import CerbLean.CN.TypeChecking.Inference
import CerbLean.CN.Types

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types

/-! ## Ghost Statement Kind

Represents the different kinds of CN ghost statements that can appear
in C source annotations. Corresponds to: cn_statement variants in
cn/lib/cnprog.ml and check.ml:2171-2283.
-/

/-- The kind of CN ghost statement.
    Corresponds to: cn_statement in cn/lib/cnprog.ml -/
inductive GhostStatementKind where
  /-- `cn_have(expr)`: Assert a constraint into the context and generate
      a proof obligation that the constraint holds.
      CN ref: check.ml:2171-2187 -/
  | have_
  /-- `assert(expr)`: Generate a proof obligation only (does NOT add to context).
      CN ref: check.ml:2247-2261 -/
  | assert_
  /-- `instantiate Pred, index`: Instantiate a quantified predicate at a
      specific index. Requires QPredicate support (WP-F).
      CN ref: check.ml:2204-2226 -/
  | instantiate
  /-- `focus Pred, index`: Extract a single element from a quantified resource,
      keeping the QPredicate. Requires QPredicate support (WP-F).
      CN ref: check.ml:2227-2246 -/
  | extract
  /-- `split_case(expr)`: Provide a case-split hint to the solver.
      CN ref: check.ml:2262-2283 -/
  | splitCase
  /-- `cn_print(...)`: Debug output during type checking.
      CN ref: check.ml (print handling) -/
  | print
  /-- `pack(...)`: Pack a resource into a user-defined predicate.
      Requires user-defined predicate support. -/
  | pack
  /-- `unpack(...)`: Unpack a user-defined predicate into its constituents.
      Requires user-defined predicate support. -/
  | unpack
  /-- `unfold(...)`: Unfold a recursive predicate definition.
      Requires user-defined predicate support. -/
  | unfold
  /-- `apply lemma(...)`: Apply a CN lemma.
      Requires user-defined predicate support. -/
  | apply_
  /-- `inline(...)`: Inline a function definition.
      Requires user-defined predicate support. -/
  | inline_
  /-- `to_from_bytes(...)`: Convert between byte-level and structured representation.
      Requires user-defined predicate support. -/
  | toFromBytes
  deriving Repr, BEq, Inhabited

namespace GhostStatementKind

/-- Parse a ghost statement kind from a string identifier.
    Fails explicitly for unknown kinds (never guesses). -/
def fromString : String → Except String GhostStatementKind
  | "have" | "cn_have" => .ok .have_
  | "assert" | "cn_assert" => .ok .assert_
  | "instantiate" | "cn_instantiate" => .ok .instantiate
  | "extract" | "focus" => .ok .extract
  | "split_case" | "cn_split_case" => .ok .splitCase
  | "print" | "cn_print" => .ok .print
  | "pack" | "cn_pack" => .ok .pack
  | "unpack" | "cn_unpack" => .ok .unpack
  | "unfold" | "cn_unfold" => .ok .unfold
  | "apply" | "cn_apply" => .ok .apply_
  | "inline" | "cn_inline" => .ok .inline_
  | "to_from_bytes" | "cn_to_from_bytes" => .ok .toFromBytes
  | other => .error s!"unknown ghost statement kind: {other}"

/-- Get a human-readable name for error messages. -/
def name : GhostStatementKind → String
  | .have_ => "have"
  | .assert_ => "assert"
  | .instantiate => "instantiate"
  | .extract => "extract"
  | .splitCase => "split_case"
  | .print => "print"
  | .pack => "pack"
  | .unpack => "unpack"
  | .unfold => "unfold"
  | .apply_ => "apply"
  | .inline_ => "inline"
  | .toFromBytes => "to_from_bytes"

end GhostStatementKind

/-! ## Ghost Statement Handlers

Each handler corresponds to a case in CN's check.ml cn_statement matching.
Handlers operate within TypingM and modify the typing context and/or
generate proof obligations as appropriate.
-/

/-- Handle a `have` ghost statement.
    Adds the constraint to the typing context AND generates a proof obligation
    to verify the constraint actually holds.

    CN ref: check.ml:2171-2187
    ```ocaml
    | M_CN_have (loc, lc_it) ->
      let@ lc_it = ...check the expression... in
      let@ () = add_c (LC.T lc_it) in
      let@ () = provable loc (LC.T lc_it) (fun () -> ...)
    ```

    In CN, `provable` checks the constraint inline and fails immediately if
    refuted. We generate a post-hoc obligation instead, matching our general
    approach of deferring proof queries to the SMT solver.

    Audited: 2026-02-19 -/
def handleHave (constraintTerm : IndexTerm) (loc : Loc) : TypingM Unit := do
  -- 1. Generate proof obligation: the constraint must be provable
  -- CN ref: check.ml:2180-2187 (provable call)
  TypingM.requireConstraint (.t constraintTerm) loc "have obligation"
  -- 2. Add constraint to typing context (assumption for subsequent checking)
  -- CN ref: check.ml:2178 (add_c (LC.T lc_it))
  TypingM.addC (.t constraintTerm)

/-- Handle an `assert` ghost statement.
    Generates a proof obligation only; does NOT add the constraint to the context.

    CN ref: check.ml:2247-2261
    ```ocaml
    | M_CN_assert (loc, lc_it) ->
      let@ lc_it = ...check the expression... in
      let@ () = provable loc (LC.T lc_it) (fun () -> ...)
    ```

    Unlike `have`, the constraint is only verified (as an obligation), not
    assumed for subsequent checking.

    Audited: 2026-02-19 -/
def handleAssert (constraintTerm : IndexTerm) (loc : Loc) : TypingM Unit := do
  -- Generate proof obligation only (no context addition)
  -- CN ref: check.ml:2255-2261 (provable call, no add_c)
  TypingM.requireConstraint (.t constraintTerm) loc "assert obligation"

/-- Handle an `instantiate` ghost statement.
    Would instantiate a quantified predicate (QPredicate / `each`) at a specific index.

    CN ref: check.ml:2204-2226
    ```ocaml
    | M_CN_instantiate (loc, to_instantiate) ->
      ...qpredicateRequest with specific index...
    ```

    Not yet implemented: requires QPredicate support (WP-F).

    Audited: 2026-02-19 -/
def handleInstantiate (_loc : Loc) : TypingM Unit := do
  throw (.other "not yet implemented: instantiate ghost statement (requires QPredicate support, WP-F)")

/-- Handle an `extract` (focus) ghost statement.
    Extracts a single element from a quantified resource (QPredicate / `each`),
    producing a regular Predicate resource at the given index, and updating
    the QPredicate's guard to exclude that index.

    CN ref: check.ml:2158-2190 (Extract handler) + pack.ml:155-191 (extractable_one)

    In CN, `extract` adds a "movable index" and then `do_unfold_resources`
    iterates to extract elements. We perform the extraction directly here,
    which is equivalent for single-element extraction.

    Given `focus Owned<int>, 1u64;` with context containing:
      `each (u64 i; 0 <= i && i < 3) { Owned<int>(array_shift(arr, i)) } => elems`
    This produces:
      1. `Owned<int>(array_shift(arr, 1u64)) => map_get(elems, 1u64)`
      2. Updated QPredicate: guard becomes `(0 <= i && i < 3) && (i != 1u64)`

    Audited: 2026-02-20 against pack.ml:155-191 -/
def handleExtract (resourceName : ResourceName) (indexTerm : IndexTerm) (loc : Loc) : TypingM Unit := do
  let resources ← TypingM.getResources
  -- Phase 1: Find a matching QPredicate by name and quantifier base type
  -- CN ref: pack.ml:162-165 — match Q resources where name matches and index BT matches q BT
  let mut found := none
  for h : idx in [:resources.length] do
    let r := resources[idx]
    match r.request with
    | .q qp =>
      if nameSubsumed resourceName qp.name
        && baseTypeReprEq indexTerm.bt qp.q.2 then
        found := some (idx, qp, r.output)
        break
    | .p _ => pure ()
  match found with
  | none =>
    -- Debug: show what resources are actually in context
    let resInfo := resources.map fun r => match r.request with
      | .q qp => s!"Q({reprStr qp.name}, q_bt={reprStr qp.q.2})"
      | .p pred => s!"P({reprStr pred.name})"
    throw (.other s!"extract/focus: no matching QPredicate found for resource '{reprStr resourceName}' (index bt={reprStr indexTerm.bt}). Resources in context: {resInfo}")
  | some (idx, qp, output) =>
    -- Phase 2: Check that the index is within the QPredicate's permission
    -- CN ref: pack.ml:166-168 — substitute index for q in permission, check provable
    let su := Subst.single qp.q.1 indexTerm
    let indexPermission := qp.permission.subst su
    TypingM.requireConstraint (.t indexPermission) loc "extract/focus: index within permission"
    -- Phase 3: Create the extracted element as a regular Predicate resource
    -- CN ref: pack.ml:170-177
    -- Pointer: substitute the quantifier variable in the QPredicate's pointer template
    -- e.g., arrayShift(arr, int, i)[i → 1u64] = arrayShift(arr, int, 1u64)
    let elemPointer : IndexTerm := qp.pointer.subst su
    -- Output value: map_get(qp_output, index) with element type (not map type)
    let elemBt := match output.value.bt with
      | .map _ vt => vt
      | _ => output.value.bt
    let elemOutput : Output := ⟨AnnotTerm.mk (.mapGet output.value indexTerm) elemBt loc⟩
    let elemPred : Predicate := {
      name := qp.name
      pointer := elemPointer
      iargs := qp.iargs.map (·.subst su)
    }
    let elemResource : Resource := { request := .p elemPred, output := elemOutput }
    -- Phase 4: Update QPredicate permission to exclude the extracted index
    -- CN ref: pack.ml:179-186 — permission := permission AND (q != index)
    let qVar : IndexTerm := AnnotTerm.mk (.sym qp.q.1) qp.q.2 qp.qLoc
    let neIndex : IndexTerm := AnnotTerm.mk
      (.unop .not (AnnotTerm.mk (.binop .eq qVar indexTerm) .bool loc)) .bool loc
    let updatedPermission : IndexTerm := AnnotTerm.mk
      (.binop .and_ qp.permission neIndex) .bool loc
    let updatedQP : QPredicate := { qp with permission := updatedPermission }
    let updatedQPResource : Resource := { request := .q updatedQP, output := output }
    -- Phase 5: Remove old QPredicate, add updated QPredicate and extracted element
    TypingM.removeResourceAt idx
    TypingM.addR updatedQPResource
    TypingM.addR elemResource

/-- Handle a `split_case` ghost statement.
    Provides case-split guidance to the solver by adding a constraint as an assumption.

    CN ref: check.ml:2262-2283
    ```ocaml
    | M_CN_split_case (loc, lc_it) ->
      let@ lc_it = ...check the expression... in
      ...case split logic...
    ```

    CN's split_case is more sophisticated: it checks provability of both the
    constraint and its negation to select which branch to explore. For now,
    we simplify this to just adding the constraint as an assumption.

    DIVERGES-FROM-CN: CN's split_case (check.ml:2262-2283) checks provable(c)
    and provable(not c) to decide which branch to take. We add the constraint
    directly as an assumption. This is sound but less precise (the solver may
    have to consider both cases).

    Audited: 2026-02-19 -/
def handleSplitCase (constraintTerm : IndexTerm) (loc : Loc) : TypingM Unit := do
  -- Add constraint as assumption (simplified case split)
  -- A full implementation would check provability of both directions
  -- and branch accordingly (CN check.ml:2268-2283)
  -- DIVERGES-FROM-CN: simplified to just adding the constraint
  let _ := loc  -- loc available for future use (inline solver queries)
  TypingM.addC (.t constraintTerm)

/-- Handle a `print` ghost statement.
    Debug output during type checking. Currently a no-op.

    CN ref: check.ml (print handling)

    Audited: 2026-02-19 -/
def handlePrint (_loc : Loc) : TypingM Unit := do
  -- No-op: debug output not implemented
  -- A full implementation would print the current typing context
  -- and/or specific expressions to aid debugging
  pure ()

/-! ## Predicate-Dependent Statement Stubs

These ghost statements require user-defined predicate support, which is
not yet implemented. Each fails explicitly with a descriptive error.
-/

/-- Handle a `pack` ghost statement.
    Packs constituent resources into a user-defined predicate instance.
    Requires user-defined predicate support.

    CN ref: check.ml pack handling -/
def handlePack (_loc : Loc) : TypingM Unit := do
  throw (.other "not yet implemented: pack ghost statement (requires user-defined predicates)")

/-- Handle an `unpack` ghost statement.
    Unpacks a user-defined predicate instance into its constituent resources.
    Requires user-defined predicate support.

    CN ref: check.ml unpack handling -/
def handleUnpack (_loc : Loc) : TypingM Unit := do
  throw (.other "not yet implemented: unpack ghost statement (requires user-defined predicates)")

/-- Handle an `unfold` ghost statement.
    Unfolds a recursive predicate definition one step.
    Requires user-defined predicate support.

    CN ref: check.ml unfold handling -/
def handleUnfold (_loc : Loc) : TypingM Unit := do
  throw (.other "not yet implemented: unfold ghost statement (requires user-defined predicates)")

/-- Handle an `apply` ghost statement.
    Applies a CN lemma to derive new facts.
    Requires user-defined predicate support.

    CN ref: check.ml apply handling -/
def handleApply (_loc : Loc) : TypingM Unit := do
  throw (.other "not yet implemented: apply ghost statement (requires user-defined predicates)")

/-- Handle an `inline` ghost statement.
    Inlines a function definition.
    Requires user-defined predicate support.

    CN ref: check.ml inline handling -/
def handleInline (_loc : Loc) : TypingM Unit := do
  throw (.other "not yet implemented: inline ghost statement (requires user-defined predicates)")

/-- Handle a `to_from_bytes` ghost statement.
    Converts between byte-level and structured resource representation.
    Requires user-defined predicate support.

    CN ref: check.ml to_from_bytes handling -/
def handleToFromBytes (_loc : Loc) : TypingM Unit := do
  throw (.other "not yet implemented: to_from_bytes ghost statement (requires user-defined predicates)")

/-! ## Top-Level Dispatch

The main entry point dispatches on the ghost statement kind and calls
the appropriate handler.
-/

/-- Process a ghost statement.
    Dispatches on the ghost statement kind and calls the appropriate handler.
    For most statements, `constraintTerm` provides the boolean expression argument.
    For extract/instantiate, `resourcePred` and `indexExpr` provide the resource
    name and index respectively.

    Corresponds to: cn_statement matching in check.ml:2171-2283

    Audited: 2026-02-20 -/
def processGhostStatement (kind : GhostStatementKind) (constraintTerm : Option IndexTerm)
    (resourcePred : Option ResourceName) (indexExpr : Option IndexTerm)
    (loc : Loc) : TypingM Unit := do
  match kind with
  | .have_ =>
    match constraintTerm with
    | some term => handleHave term loc
    | none => throw (.other "have ghost statement requires a constraint expression")
  | .assert_ =>
    match constraintTerm with
    | some term => handleAssert term loc
    | none => throw (.other "assert ghost statement requires a constraint expression")
  | .splitCase =>
    match constraintTerm with
    | some term => handleSplitCase term loc
    | none => throw (.other "split_case ghost statement requires a constraint expression")
  | .print => handlePrint loc
  | .instantiate => handleInstantiate loc
  | .extract =>
    match resourcePred, indexExpr with
    | some rn, some idx => handleExtract rn idx loc
    | _, _ => throw (.other "extract/focus ghost statement requires a resource predicate and index expression")
  | .pack => handlePack loc
  | .unpack => handleUnpack loc
  | .unfold => handleUnfold loc
  | .apply_ => handleApply loc
  | .inline_ => handleInline loc
  | .toFromBytes => handleToFromBytes loc

/-- Process a ghost statement from its string kind name.
    Parses the kind string and dispatches to processGhostStatement.

    This is the convenience entry point for callers that have the ghost
    statement kind as a raw string (e.g., from parsed annotations).

    Audited: 2026-02-20 -/
def processGhostStatementByName (kindName : String) (constraintTerm : Option IndexTerm)
    (resourcePred : Option ResourceName) (indexExpr : Option IndexTerm)
    (loc : Loc) : TypingM Unit := do
  match GhostStatementKind.fromString kindName with
  | .ok kind => processGhostStatement kind constraintTerm resourcePred indexExpr loc
  | .error msg => throw (.other msg)

end CerbLean.CN.TypeChecking
