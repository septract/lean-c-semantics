import CToLean.Theorems.UBFree
import CToLean.Semantics.Eval
import CToLean.Semantics.Step
import Std.Data.HashMap

/-!
# Weakest Precondition (WP) Calculus for Core IR

This module defines a WP transformer for compositional reasoning about
UB-freeness and functional correctness of Core programs.

## Design Strategy

The WP calculus enables **compositional verification**: proving properties of
compound expressions from properties of their subexpressions. This avoids
reasoning about the entire interpreter for each proof.

### Key Design Decisions

1. **Fuel-indexed WP (`wpPureN`)**: Uses explicit fuel parameter matching
   `evalPexpr`'s recursion structure. This enables compositional rules because
   `evalPexpr (fuel+1)` for compound expressions calls `evalPexpr fuel` for
   subexpressions.

2. **Result state in postcondition**: `wpPureN` passes the result state `s'`
   (not the input state) to the postcondition. This enables clean compositional
   rules since state threads through sequential evaluation.

3. **UB as False, other errors as True**: The WP is `False` only for undefined
   behavior. Type errors, pattern match failures, etc. are treated as `True`
   (vacuously satisfied) since they indicate interpreter limitations, not UB.

### Proof Technique

All compositional proofs follow the same pattern:
1. `simp only [wpPureN]` - unfold WP definition
2. `rw [evalPexpr_X']` - apply equation lemma for the expression form
3. `rw [InterpM_bind_run]` - distribute bind through monad transformers
4. Case split on subexpression results
5. `simp only [hcase] at h ⊢` - substitute case hypothesis

### Key Lemmas

- `evalPexpr_if'`, `evalPexpr_let'`, `evalPexpr_op'`: Equation lemmas that
  characterize `evalPexpr (fuel+1)` for each expression constructor
- `InterpM_bind_run`: Shows how bind distributes through `.run.run`:
  `((m >>= f).run env).run state = match m.run.run with ok => f ... | err => err`

## Module Structure

- **Postcondition Types**: `PurePost`, `ExprPost`
- **WP Definitions**: `wpPureN`, `wpPure`, `wpExpr`
- **Soundness Theorems**: `wpPureN_noUB`, `wpPureN_post`
- **Compositional Rules**: `wpPureN_val`, `wpPureN_if`, `wpPureN_let`, etc.

## Related Modules

- `CToLean.Theorems.UBFree`: Basic UB-freeness predicates
- `CToLean.Semantics.Eval`: Pure expression evaluator with equation lemmas
- `docs/VERIFICATION_PLAN.md`: Overall verification strategy

## References

- Dijkstra's weakest precondition calculus
- Hoare logic for imperative programs
-/

namespace CToLean.Theorems.WP

open CToLean.Core
open CToLean.Semantics
open CToLean.Memory
open Std (HashMap)

/-! ## Postcondition Types

Postconditions describe what should be true after execution.
-/

/-- Postcondition for pure expressions: relates result value to initial state -/
abbrev PurePost := Value → InterpState → Prop

/-- Postcondition for effectful expressions: relates result value to final state -/
abbrev ExprPost := Value → InterpState → Prop

/-! ## WP for Pure Expressions

Pure expressions (Pexpr) don't have side effects, so their WP only needs
to ensure the expression evaluates without UB and satisfies the postcondition.

For a pure expression `pe`, `wpPure pe Q env state` means:
- Evaluating `pe` in environment `env` and state `state` doesn't produce UB
- If evaluation succeeds with value `v`, then `Q v state` holds
-/

/-- Fuel-parameterized weakest precondition for compositional reasoning.

    `wpPureN fuel pe Q env interpEnv state` holds iff:
    - Evaluating `pe` with `fuel` steps doesn't produce undefined behavior
    - If evaluation succeeds with value `v` and final state `s'`, then `Q v s'` holds

    This fuel-indexed version enables compositional rules because
    `evalPexpr (fuel + 1)` for compound expressions uses `evalPexpr fuel`
    for subexpressions.

    Note: We use the result state `s'` in the postcondition rather than the
    parameter state. This enables clean compositional rules since state
    threads through sequential evaluation.
-/
def wpPureN (fuel : Nat) (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) : Prop :=
  match ((evalPexpr fuel env pe).run interpEnv).run state with
  | .ok (v, s') => Q v s'
  | .error (.undefinedBehavior _ _) => False
  | .error _ => True  -- Other errors (type errors, not implemented) are not UB

/-- Weakest precondition for pure expression evaluation (default fuel).

    `wpPure pe Q env state` holds iff:
    - Evaluating `pe` doesn't produce undefined behavior
    - If evaluation succeeds with value `v`, then `Q v state` holds

    Note: Pure expressions don't modify state, so postcondition gets original state.
-/
def wpPure (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) : Prop :=
  wpPureN defaultPexprFuel pe Q env interpEnv state

/-! ## WP Soundness for Pure Expressions

The key theorem: if the WP holds, evaluation doesn't produce UB and
satisfies the postcondition.
-/

/-- Helper: check if an Except result is a UB error -/
def isUBResult {α : Type} : Except InterpError α → Bool
  | .ok _ => false
  | .error (.undefinedBehavior _ _) => true
  | .error _ => false

/-- If wpPureN holds, then evaluation doesn't produce UB -/
theorem wpPureN_noUB (fuel : Nat) (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpPureN fuel pe Q env interpEnv state) :
    isUBResult (((evalPexpr fuel env pe).run interpEnv).run state) = false := by
  unfold wpPureN at h
  unfold isUBResult
  cases hres : ((evalPexpr fuel env pe).run interpEnv).run state with
  | ok p => rfl
  | error e =>
    simp only [hres] at h
    cases e with
    | undefinedBehavior ub loc => exact absurd h (by simp)
    | _ => rfl

/-- If wpPure holds, then evaluation doesn't produce UB -/
theorem wpPure_noUB (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpPure pe Q env interpEnv state) :
    isUBResult (((evalPexpr defaultPexprFuel env pe).run interpEnv).run state) = false :=
  wpPureN_noUB defaultPexprFuel pe Q env interpEnv state h

/-- If wpPureN holds and evaluation succeeds, postcondition holds -/
theorem wpPureN_post (fuel : Nat) (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpPureN fuel pe Q env interpEnv state)
    (result : Value × InterpState)
    (heval : ((evalPexpr fuel env pe).run interpEnv).run state = Except.ok result) :
    Q result.1 result.2 := by
  unfold wpPureN at h
  rw [heval] at h
  exact h

/-- If wpPure holds and evaluation succeeds, postcondition holds -/
theorem wpPure_post (pe : APexpr) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpPure pe Q env interpEnv state)
    (result : Value × InterpState)
    (heval : ((evalPexpr defaultPexprFuel env pe).run interpEnv).run state = Except.ok result) :
    Q result.1 result.2 :=
  wpPureN_post defaultPexprFuel pe Q env interpEnv state h result heval

/-! ## WP Rules for Pure Expression Constructors

These lemmas characterize the WP for each pure expression form.
They allow compositional reasoning.
-/

/-- WP for value literals (fuel-indexed): postcondition must hold for the literal -/
theorem wpPureN_val (fuel : Nat) (v : Value) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN (fuel + 1) ⟨[], none, .val v⟩ Q env interpEnv state ↔ Q v state := by
  unfold wpPureN evalPexpr
  simp only []
  constructor <;> intro h <;> exact h

/-- WP for value literals: postcondition must hold for the literal -/
theorem wpPure_val (v : Value) (Q : PurePost) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpPure ⟨[], none, .val v⟩ Q env interpEnv state ↔ Q v state := by
  unfold wpPure
  -- defaultPexprFuel = 100000 = 99999 + 1
  have h : defaultPexprFuel = 99999 + 1 := rfl
  rw [h]
  exact wpPureN_val 99999 v Q env interpEnv state

/-! ## WP for Effectful Expressions

Effectful expressions (Expr) can modify memory state. Their WP must account
for state changes.

The evaluation of effectful expressions uses small-step semantics (`step` in Step.lean).
The SOUND approach is to define WP in terms of the interpreter result.
-/

/-- SOUND: Weakest precondition for effectful expression evaluation.

    This is defined via `runExprToValue` which runs the small-step interpreter.
    Like `wpPureN`, this is interpreter-grounded and therefore sound.

    To prove compositional rules for this, we need to prove theorems showing
    how `runExprToValue` behaves for each expression constructor.

    Parameters:
    - `e`: The effectful expression to evaluate
    - `Q`: Postcondition relating final value to final state
    - `file`: The Core IR file (needed for function lookups)
    - `env`: The variable environment
    - `interpEnv`: Interpreter environment (type info, etc.)
    - `state`: Initial interpreter state (memory, etc.)
-/
def wpExpr (e : AExpr) (Q : ExprPost) (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) : Prop :=
  match ((runExprToValue e env file).run interpEnv).run state with
  | .ok (v, state') => Q v state'
  | .error (.undefinedBehavior _ _) => False
  | .error _ => True

/-- SOUND: Weakest precondition for effectful expression evaluation WITH continuations.

    This is the proper definition for programs that use save/run for control flow.
    Unlike `wpExpr`, this takes `allLabeledConts` and `currentProc` as parameters,
    allowing `Erun` to find its target continuation.

    **IMPORTANT**: `wpExpr` (without continuations) is NOT suitable for verifying
    programs with save/run! It passes empty `allLabeledConts`, so `Erun` always
    fails with `illformedProgram`. Since that's not UB, wpExpr returns True
    vacuously.

    Use this definition for real C programs that use return statements, loops,
    or other control flow that compiles to save/run.

    Parameters:
    - `e`: The effectful expression to evaluate
    - `Q`: Postcondition relating final value to final state
    - `file`: The Core IR file
    - `allLabeledConts`: Pre-computed labeled continuations (from extractLabeledConts)
    - `currentProc`: The current procedure symbol (continuations are per-procedure)
    - `env`: The variable environment
    - `interpEnv`: Interpreter environment
    - `state`: Initial interpreter state

    The continuation map is indexed by procedure, then by label:
    `allLabeledConts[currentProc][label] = { params, body }`
-/
def wpExprWithConts (e : AExpr) (Q : ExprPost) (file : File)
    (allLabeledConts : HashMap Sym LabeledConts)
    (currentProc : Sym)
    (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) : Prop :=
  let st : ThreadState := {
    arena := e
    stack := .cons (some currentProc) [] .empty
    env := env
    currentProc := some currentProc
  }
  match ((runUntilDone st file allLabeledConts).run interpEnv).run state with
  | .ok (v, state') => Q v state'
  | .error (.undefinedBehavior _ _) => False
  | .error _ => True

/-! ## WP Soundness for Effectful Expressions -/

/-- If wpExpr holds, then evaluation doesn't produce UB -/
theorem wpExpr_noUB (e : AExpr) (Q : ExprPost) (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpExpr e Q file env interpEnv state) :
    isUBResult (((runExprToValue e env file).run interpEnv).run state) = false := by
  unfold wpExpr at h
  unfold isUBResult
  cases hres : ((runExprToValue e env file).run interpEnv).run state with
  | ok p => rfl
  | error e =>
    simp only [hres] at h
    cases e with
    | undefinedBehavior ub loc => exact absurd h (by simp)
    | _ => rfl

/-- If wpExpr holds and evaluation succeeds, postcondition holds -/
theorem wpExpr_post (e : AExpr) (Q : ExprPost) (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpExpr e Q file env interpEnv state)
    (result : Value × InterpState)
    (heval : ((runExprToValue e env file).run interpEnv).run state = Except.ok result) :
    Q result.1 result.2 := by
  unfold wpExpr at h
  rw [heval] at h
  exact h

/-! ## Compositional Rules for Effectful Expressions

These theorems establish compositional reasoning principles for `wpExpr`.
They are SOUND because they are proven theorems about the interpreter-grounded
definition, not structural definitions on the AST.

The proofs use `sorry` where substantial proof work is needed. These establish
the proof obligations that need to be discharged for full soundness.
-/

/-- WP for Expr.bound: bounds wrapper is transparent for WP.

    `Ebound e` evaluates to the same result as `e` - it's just a marker
    for bounds checking that doesn't affect execution.

    Corresponds to: core_run.lem:1643-1649
    ```lem
    | Ebound (_, e) -> Return (TSrunning (st with arena = e))
    ```
-/
theorem wpExpr_bound (e : AExpr) (Q : ExprPost) (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .bound e⟩ Q file env interpEnv state ↔
    wpExpr e Q file env interpEnv state := by
  -- The step function simply unwraps Ebound:
  -- | .bound e, _ => pure (.continue_ { st with arena := e })
  -- So execution of (Ebound e) is identical to execution of e
  sorry

/-- WP for Expr.pure with a value: just check postcondition.

    `Epure (PEval v)` immediately evaluates to `v` without modifying state.

    Corresponds to: core_run.lem:1540-1542 and 1556-1616
-/
theorem wpExpr_pure_val (v : Value) (Q : ExprPost) (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .pure ⟨[], none, .val v⟩⟩ Q file env interpEnv state ↔
    Q v state := by
  -- When arena is Epure(PEval v) and stack is empty, step returns .done v
  -- The state is unchanged
  sorry

/-- WP for Expr.pure with general pexpr: relates to wpPureN.

    `Epure pe` evaluates `pe` as a pure expression and returns the result.
    State may be modified by pure evaluation (though typically not).

    This connects wpExpr (effectful) to wpPureN (pure).
-/
theorem wpExpr_pure (pe : APexpr) (Q : ExprPost) (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .pure pe⟩ Q file env interpEnv state ↔
    wpPureN defaultPexprFuel pe (fun v s => Q v s) env interpEnv state := by
  -- The step function calls evalPexpr for pure expressions:
  -- | .pure pe, .empty =>
  --     let cval ← evalPexpr defaultPexprFuel st.env pe
  --     pure (.continue_ { st with arena := mkValueExpr arenaAnnots cval })
  sorry

/-- WP for Expr.let_: evaluate bound expression, then body with bindings.

    `Elet pat pe1 e2` evaluates `pe1` (pure), binds the result according to `pat`,
    then evaluates `e2` with the extended environment.

    Corresponds to: core_run.lem:837-865
-/
theorem wpExpr_let (pat : APattern) (pe1 : APexpr) (e2 : AExpr) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .let_ pat pe1 e2⟩ Q file env interpEnv state ↔
    wpPureN defaultPexprFuel pe1 (fun v1 s1 =>
      match matchPattern pat v1 with
      | some bindings => wpExpr e2 Q file (bindAllInEnv bindings env) interpEnv s1
      | none => True  -- Pattern match failure is not UB
    ) env interpEnv state := by
  -- The step function for Elet:
  -- | .let_ pat pe1 e2, _ =>
  --     let cval ← evalPexpr defaultPexprFuel st.env pe1
  --     match st.updateEnv pat cval with
  --     | some st' => pure (.continue_ { st' with arena := e2 })
  --     | none => throw .patternMatchFailed
  sorry

/-- WP for Expr.if_: evaluate condition, then appropriate branch.

    `Eif cond then_ else_` evaluates `cond` (pure), then evaluates
    `then_` if true or `else_` if false.

    Corresponds to: core_run.lem:870-924
-/
theorem wpExpr_if (cond : APexpr) (then_ else_ : AExpr) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .if_ cond then_ else_⟩ Q file env interpEnv state ↔
    wpPureN defaultPexprFuel cond (fun v s =>
      match v with
      | .true_ => wpExpr then_ Q file env interpEnv s
      | .false_ => wpExpr else_ Q file env interpEnv s
      | _ => True  -- Type error, not UB
    ) env interpEnv state := by
  -- The step function for Eif:
  -- | .if_ cond then_ else_, .cons _ _ _ =>
  --     let condVal ← evalPexpr defaultPexprFuel st.env cond
  --     match condVal with
  --     | .true_ => pure (.continue_ { st with arena := then_ })
  --     | .false_ => pure (.continue_ { st with arena := else_ })
  --     | _ => throw (.typeError "if condition must be boolean")
  sorry

/-- WP for Expr.sseq: strong sequencing (effectful let).

    `Esseq pat e1 e2` evaluates `e1`, binds result to `pat`, then evaluates `e2`.
    Unlike `Elet`, `e1` can be an arbitrary effectful expression.

    Corresponds to: core_run.lem:1450-1489
-/
theorem wpExpr_sseq (pat : APattern) (e1 e2 : AExpr) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .sseq pat e1 e2⟩ Q file env interpEnv state ↔
    wpExpr e1 (fun v1 s1 =>
      match matchPattern pat v1 with
      | some bindings => wpExpr e2 Q file (bindAllInEnv bindings env) interpEnv s1
      | none => True  -- Pattern match failure is not UB
    ) file env interpEnv state := by
  -- The step function handles sseq by:
  -- 1. If e1 is already a value, bind and continue with e2
  -- 2. Otherwise, push continuation and focus on e1
  -- The overall effect is sequential composition
  sorry

/-- WP for Expr.wseq: weak sequencing.

    `Ewseq pat e1 e2` is similar to `Esseq` but allows interleaving in
    concurrent contexts. In sequential execution (which we use), it's
    equivalent to `Esseq`.

    Corresponds to: core_run.lem:1408-1445
-/
theorem wpExpr_wseq (pat : APattern) (e1 e2 : AExpr) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .wseq pat e1 e2⟩ Q file env interpEnv state ↔
    wpExpr e1 (fun v1 s1 =>
      match matchPattern pat v1 with
      | some bindings => wpExpr e2 Q file (bindAllInEnv bindings env) interpEnv s1
      | none => True
    ) file env interpEnv state := by
  -- Similar to sseq - in sequential execution they're equivalent
  sorry

/-- WP for Expr.nd: nondeterministic choice.

    `End es` nondeterministically chooses one of the expressions.
    For UB-freeness, ALL choices must be UB-free. For our deterministic
    interpreter (which picks the first), we only need the first to be safe.

    Corresponds to: core_run.lem:1618-1623
-/
theorem wpExpr_nd_first (e : AExpr) (es : List AExpr) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .nd (e :: es)⟩ Q file env interpEnv state ↔
    wpExpr e Q file env interpEnv state := by
  -- Our interpreter picks the first element:
  -- | .nd es, _ => match es with | e :: _ => ...
  sorry

/-! ## Memory Operation WP

WP rules for memory actions that can cause UB.
-/

/-- WP for store operation: pointer must be valid and writable -/
def wpStore (ptr : PointerValue) (state : InterpState) : Prop :=
  ValidPointer ptr state.memory
  -- Additional conditions: alignment, type compatibility would go here

/-- WP for load operation: pointer must be valid and initialized -/
def wpLoad (ptr : PointerValue) (state : InterpState) : Prop :=
  ValidInitializedPointer ptr state.memory
  -- The loaded value would need to satisfy Q

/-! ## Continuation WP Rules

Rules for save/run which implement control flow in Core IR.
These are used for return statements, loops, etc.
-/

/-- Helper: WP for evaluating default arguments in a save expression.

    All default argument expressions must evaluate without UB.
-/
def wpSaveDefaults (params : List (Sym × BaseType × APexpr))
    (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) : Prop :=
  ∀ (param : Sym × BaseType × APexpr), param ∈ params →
    wpPureN defaultPexprFuel param.2.2 (fun _ _ => True) env interpEnv state

/-- WP for Expr.save: define a labeled continuation.

    `Esave sym retTy [(p1, ty1, default1), ...] body` defines a continuation
    point that can be jumped to with `Erun sym args`. The default values
    are evaluated and bound to the parameters.

    **IMPORTANT**: This theorem has two parts:
    1. All default argument expressions must evaluate without UB
    2. The body must satisfy the postcondition

    Note: The body may contain `Erun` that jumps to THIS continuation or
    others. In such cases, execution may not follow the body linearly.
    However, for UB-freeness, we still need the body's WP to hold because
    that's what will execute if/when control reaches this save.

    For programs with complex control flow (run jumping elsewhere), use
    `wpExprWithConts` which properly tracks all continuations.

    Corresponds to: core_run.lem:1494-1501
-/
theorem wpExpr_save (sym : Sym) (retTy : BaseType) (params : List (Sym × BaseType × APexpr))
    (body : AExpr) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .save sym retTy params body⟩ Q file env interpEnv state ↔
    -- Default args must evaluate without UB
    wpSaveDefaults params env interpEnv state ∧
    -- Body must satisfy Q (with defaults bound to parameters)
    wpExpr body Q file env interpEnv state := by
  -- The step function:
  -- 1. Evaluates all default expressions
  -- 2. Binds results to parameter symbols
  -- 3. Registers the continuation
  -- 4. Continues with body
  sorry

/-- WP for Expr.run: jump to a labeled continuation.

    `Erun sym args` evaluates the arguments and jumps to the continuation
    labeled `sym`, passing the argument values.

    **CRITICAL LIMITATION**: `wpExpr` passes empty `allLabeledConts` to the
    interpreter, so `Erun` ALWAYS fails with `illformedProgram` (not UB).
    This means `wpExpr` returns `True` vacuously for any Erun expression!

    This theorem is therefore trivially correct for `wpExpr`, but USELESS
    for verification. For programs with save/run, use `wpExprWithConts`.

    Corresponds to: core_run.lem:1509-1530
-/
theorem wpExpr_run (sym : Sym) (args : List APexpr) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .run sym args⟩ Q file env interpEnv state ↔
    -- With wpExpr (no continuations), run always fails with illformedProgram
    -- Since that's not UB, the WP is vacuously True
    -- Arguments still need to evaluate without UB (executed before lookup)
    (∀ argPe ∈ args, wpPureN defaultPexprFuel argPe (fun _ _ => True) env interpEnv state) ∧
    True  -- Vacuously true because run fails with non-UB error
    := by
  -- The step function tries to look up the continuation in allLabeledConts
  -- Since wpExpr passes {}, lookup fails → illformedProgram → True
  sorry

/-- WP for Expr.run WITH continuation context.

    This is the PROPER version for programs that use save/run.
    It requires the continuation to exist in `allLabeledConts` and
    includes the WP of the continuation body.

    Parameters:
    - `sym`: The continuation label to jump to
    - `args`: Arguments to pass to the continuation
    - `allLabeledConts`: The continuation context (from extractLabeledConts or Esave)
    - `currentProc`: The current procedure symbol (continuations are per-procedure)
-/
theorem wpExprWithConts_run (sym : Sym) (args : List APexpr) (Q : ExprPost)
    (file : File) (allLabeledConts : HashMap Sym LabeledConts)
    (currentProc : Sym) (procConts : LabeledConts)
    (cont : LabeledCont)
    (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    -- The continuation must exist in allLabeledConts[currentProc]
    (h_proc : allLabeledConts[currentProc]? = some procConts)
    (h_cont : procConts[sym]? = some cont) :
    wpExprWithConts ⟨[], .run sym args⟩ Q file allLabeledConts currentProc env interpEnv state ↔
    -- Arguments must evaluate without UB
    (∀ argPe ∈ args, wpPureN defaultPexprFuel argPe (fun _ _ => True) env interpEnv state) ∧
    -- Continuation body must satisfy Q (with args bound to params)
    -- (Simplified: full version would bind evaluated args to cont.params)
    wpExprWithConts cont.body Q file allLabeledConts currentProc env interpEnv state := by
  -- The step function:
  -- 1. Evaluates args
  -- 2. Looks up continuation by sym in allLabeledConts[currentProc]
  -- 3. Binds args to continuation params
  -- 4. Continues with continuation body
  sorry

/-- Helper: WP for case branches with FIRST-MATCH semantics.

    Processes branches in order: first matching pattern wins.
    If no pattern matches, we get patternMatchFailed (not UB, so True).

    This is the correct semantics - the existential version was WRONG because
    if branch 1 matches and is unsafe, but branch 2 matches and is safe,
    the existential holds but execution follows the unsafe branch 1.
-/
def wpCaseBranches (v : Value) (branches : List (APattern × AExpr))
    (Q : ExprPost) (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) : Prop :=
  match branches with
  | [] => True  -- No match = patternMatchFailed, not UB
  | (pat, body) :: rest =>
    match matchPattern pat v with
    | some bindings => wpExpr body Q file (bindAllInEnv bindings env) interpEnv state
    | none => wpCaseBranches v rest Q file env interpEnv state

/-- WP for Expr.case: pattern matching with FIRST-MATCH semantics.

    `Ecase scrut branches` evaluates the scrutinee, then matches against
    branches to find the FIRST matching pattern and executes that branch.

    **IMPORTANT**: We use first-match semantics, not existential. The previous
    version using ∃ was WRONG because execution always takes the first
    matching branch, regardless of whether later branches might also match.

    Corresponds to: core_run.lem:785-835
-/
theorem wpExpr_case (scrut : APexpr) (branches : List (APattern × AExpr)) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .case_ scrut branches⟩ Q file env interpEnv state ↔
    wpPureN defaultPexprFuel scrut (fun v s =>
      wpCaseBranches v branches Q file env interpEnv s
    ) env interpEnv state := by
  -- Pattern matching finds first match and executes that branch
  -- Pattern matching failure throws patternMatchFailed, not UB
  sorry

/-! ## Action Expression WP Rules

Rules for memory actions (Eaction) which can cause UB.
These are the critical rules for memory safety verification.

Note: Memory actions are wrapped in Paction (polarity + AAction) and AAction (loc + Action).
The theorems below describe what the WP of an action expression implies.
-/

/-- WP for store action: validates memory store operation.

    Store can cause UB if:
    - Pointer is null
    - Pointer is invalid (use after free, out of bounds)
    - Type mismatch
    - Writing to read-only memory

    This theorem shows: if store doesn't cause UB, then the pointer must be valid.
-/
theorem wpExpr_action_store_implies_valid (pol : Polarity) (loc : Loc)
    (isLocking : Bool) (tyPe ptrPe valPe : APexpr) (order : MemoryOrder) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpExpr ⟨[], .action ⟨pol, ⟨loc, .store isLocking tyPe ptrPe valPe order⟩⟩⟩ Q
        file env interpEnv state) :
    -- If the WP holds, then the store doesn't cause UB
    -- This implies: pointer evaluates to something valid
    wpPureN defaultPexprFuel ptrPe (fun ptrVal _ =>
      match ptrVal with
      | .object (.pointer ptr) => ValidPointer ptr state.memory
      | .loaded (.specified (.pointer ptr)) => ValidPointer ptr state.memory
      | _ => True  -- Non-pointer causes type error, not necessarily UB
    ) env interpEnv state := by
  sorry

/-- WP for load action: validates memory load operation.

    Load can cause UB if:
    - Pointer is null
    - Pointer is invalid (use after free, out of bounds)
    - Reading uninitialized memory (in some models)
-/
theorem wpExpr_action_load_implies_valid (pol : Polarity) (loc : Loc)
    (tyPe ptrPe : APexpr) (order : MemoryOrder) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpExpr ⟨[], .action ⟨pol, ⟨loc, .load tyPe ptrPe order⟩⟩⟩ Q
        file env interpEnv state) :
    wpPureN defaultPexprFuel ptrPe (fun ptrVal _ =>
      match ptrVal with
      | .object (.pointer ptr) => ValidInitializedPointer ptr state.memory
      | .loaded (.specified (.pointer ptr)) => ValidInitializedPointer ptr state.memory
      | _ => True
    ) env interpEnv state := by
  sorry

/-- WP for kill action: validates memory deallocation.

    Kill (free) can cause UB if:
    - Pointer is null (depending on kill kind)
    - Pointer was already freed (double free)
    - Pointer points to wrong allocation
-/
theorem wpExpr_action_kill_implies_valid (pol : Polarity) (loc : Loc)
    (kind : KillKind) (ptrPe : APexpr) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState)
    (h : wpExpr ⟨[], .action ⟨pol, ⟨loc, .kill kind ptrPe⟩⟩⟩ Q file env interpEnv state) :
    wpPureN defaultPexprFuel ptrPe (fun ptrVal _ =>
      match ptrVal with
      | .object (.pointer ptr) => ValidPointer ptr state.memory
      | .loaded (.specified (.pointer ptr)) => ValidPointer ptr state.memory
      | _ => True
    ) env interpEnv state := by
  sorry

/-! ## Procedure Call WP Rules -/

/-- Helper: Look up a function declaration by name in the file.

    Functions are stored in file.funs (user-defined) or file.stdlib.
    Returns the FunDecl if found.
-/
def lookupFunDecl (name : Name) (file : File) : Option FunDecl :=
  match name with
  | .sym sym =>
    -- Look in user functions, then stdlib
    -- Compare by symbol's name field
    let findByName (funs : FunMap) : Option FunDecl :=
      funs.find? (fun entry => entry.1.name == sym.name) |>.map Prod.snd
    findByName file.funs <|> findByName file.stdlib
  | .impl _ => none  -- Implementation-defined functions handled separately

/-- Helper: Bind argument values to parameter symbols in environment -/
def bindProcArgs (params : List (Sym × BaseType)) (argVals : List Value)
    (env : List (HashMap Sym Value)) : List (HashMap Sym Value) :=
  let bindings := params.zip argVals |>.map fun ((sym, _), v) => (sym, v)
  bindAllInEnv bindings env

/-- WP for procedure call (Eproc): calls a defined procedure.

    `Eproc name args` evaluates arguments and calls the named procedure.

    **Structure**:
    1. All argument expressions must evaluate without UB
    2. If procedure is found, its body must satisfy Q (with args bound)
    3. If procedure is not found, it's an error but not necessarily UB
       (depends on whether it's a missing user function vs unimplemented stdlib)

    Note: This is a simplified version. The full version would need to:
    - Handle stdlib functions specially (some may cause UB on invalid inputs)
    - Track recursive calls properly
    - Handle the continuation context for the procedure body
-/
theorem wpExpr_proc (name : Name) (args : List APexpr) (Q : ExprPost)
    (file : File) (env : List (HashMap Sym Value))
    (interpEnv : InterpEnv) (state : InterpState) :
    wpExpr ⟨[], .proc name args⟩ Q file env interpEnv state ↔
    -- All arguments must evaluate without UB
    (∀ argPe ∈ args, wpPureN defaultPexprFuel argPe (fun _ _ => True) env interpEnv state) ∧
    -- If procedure exists and args evaluate to values, body WP must hold
    match lookupFunDecl name file with
    | some (.proc _ _ _ params body) =>
      -- Body must satisfy Q with args bound to params
      -- Simplified: assumes args.length = params.length
      True  -- Full version: wpExpr body Q file (bindProcArgs ...) interpEnv state'
    | some (.fun_ _ params bodyPe) =>
      -- Pure function - body is a Pexpr
      True  -- Full version: wpPureN ... bodyPe (fun v s => Q v s) (bindProcArgs ...)
    | some _ => True  -- Forward declaration, no body to check
    | none => True  -- Missing function is error, not UB
    := by
  -- The step function:
  -- 1. Evaluates all arguments
  -- 2. Looks up procedure by name
  -- 3. Creates new frame with args bound to params
  -- 4. Evaluates procedure body
  sorry

/-! ## Pure Expression Function Calls

WP rules for pure function calls (Pexpr.call). These are calls to stdlib
functions like conv_loaded_int, is_signed, etc.
-/

/-! ## Symbol Lookup WP Rules -/

/-- WP for Pexpr.sym: symbol lookup in environment.

    `PEsym sym` looks up the symbol in the environment and returns its value.
    This never causes UB - if the symbol is not found, it's an error but not UB.
-/
theorem wpPureN_sym (fuel : Nat) (sym : Sym) (Q : PurePost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState)
    (v : Value) (h_bound : lookupEnv sym env = some v) :
    wpPureN fuel ⟨[], none, .sym sym⟩ Q env interpEnv state ↔ Q v state := by
  -- Symbol lookup returns the bound value
  -- If found, check Q on that value
  sorry

/-- Helper: If a symbol is in the bindings from pattern match, it's in the extended env -/
theorem lookupEnv_bindAllInEnv (sym : Sym) (v : Value) (bindings : List (Sym × Value))
    (env : List (HashMap Sym Value))
    (h_in : (sym, v) ∈ bindings) :
    lookupEnv sym (bindAllInEnv bindings env) = some v := by
  sorry

/-- WP for Pexpr.call: call a pure function.

    `PEcall name args` evaluates the arguments, looks up the function,
    and calls it. For stdlib functions, the result depends on the function
    implementation.

    **Structure**:
    1. All argument expressions must evaluate without UB
    2. The function application to the evaluated args must not cause UB
    3. The result must satisfy Q

    Note: Pexpr.call takes `List Pexpr` not `List APexpr`.

    This theorem decomposes function calls: args must be safe, then we
    need to know the function is safe for those arg values. The second
    part depends on the specific function - see `isPureStdlibFunction`
    and `conv_loaded_int_ubfree_*` for specific cases.
-/
theorem wpPureN_call_args (fuel : Nat) (name : Name) (args : List Pexpr) (Q : PurePost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN (fuel + 1) ⟨[], none, .call name args⟩ Q env interpEnv state →
    -- All arguments must evaluate without UB
    (∀ arg ∈ args, wpPureN fuel ⟨[], none, arg⟩ (fun _ _ => True) env interpEnv state) := by
  -- evalPexpr for call first evaluates all args via mapM
  -- If any arg causes UB, the whole call is UB
  intro h
  sorry

/-- Theorem: conv_loaded_int is UB-free for any integer argument (literal values).

    conv_loaded_int('signed int', val) converts a loaded integer value.
    It never causes UB - it's a pure conversion function.

    This is a key lemma for verifying real C programs.

    NOTE: We only prove UB-freeness (postcondition is trivially True), not
    functional correctness. The actual return value depends on the stdlib impl.
-/
theorem conv_loaded_int_ubfree_literal (ctype_val : Ctype) (int_val : IntegerValue)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN defaultPexprFuel
      ⟨[], none, .call (.sym ⟨"", 6, .id "conv_loaded_int", some "conv_loaded_int"⟩)
        [.val (.ctype ctype_val), .val (.loaded (.specified (.integer int_val)))]⟩
      (fun _ _ => True)  -- Only claim UB-freeness
      env interpEnv state := by
  -- conv_loaded_int just extracts/converts the integer value
  -- It never triggers UB
  sorry

/-- Theorem: conv_loaded_int is UB-free when second arg is a symbol bound to an integer.

    This handles the common case where we have:
    conv_loaded_int('signed int', sym) where sym is bound to an integer value.
-/
theorem conv_loaded_int_ubfree_sym (conv_sym : Sym) (ctype_val : Ctype) (arg_sym : Sym)
    (int_val : IntegerValue)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState)
    (h_conv_name : conv_sym.name = some "conv_loaded_int")
    (h_bound : lookupEnv arg_sym env = some (Value.loaded (LoadedValue.specified (ObjectValue.integer int_val)))) :
    wpPureN defaultPexprFuel
      ⟨[], none, .call (.sym conv_sym) [.val (.ctype ctype_val), .sym arg_sym]⟩
      (fun _ _ => True)  -- Only claim UB-freeness
      env interpEnv state := by
  -- 1. Evaluate first arg: .val (.ctype ctype_val) → ctype_val (no UB)
  -- 2. Evaluate second arg: .sym arg_sym → lookup succeeds by h_bound
  -- 3. Call conv_loaded_int(ctype_val, int_val) → pure conversion, no UB
  sorry

/-- Most general: conv_loaded_int call with any arguments that evaluate to valid types.

    If the arguments evaluate successfully to a ctype and a loaded integer,
    the call succeeds without UB.
-/
theorem conv_loaded_int_ubfree (conv_sym : Sym) (arg1 arg2 : Pexpr)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState)
    (h_conv_name : conv_sym.name = some "conv_loaded_int")
    (h_arg1_ok : wpPureN defaultPexprFuel ⟨[], none, arg1⟩ (fun v _ => ∃ ct, v = .ctype ct) env interpEnv state)
    (h_arg2_ok : wpPureN defaultPexprFuel ⟨[], none, arg2⟩
      (fun v _ => ∃ iv, v = .loaded (.specified (.integer iv))) env interpEnv state) :
    wpPureN defaultPexprFuel ⟨[], none, .call (.sym conv_sym) [arg1, arg2]⟩
      (fun _ _ => True)  -- Only claim UB-freeness
      env interpEnv state := by
  -- If both args evaluate to expected types, conv_loaded_int succeeds
  sorry

/-- More general: any stdlib function that doesn't access memory is UB-free.

    This covers: conv_loaded_int, conv_int, wrapI, is_signed, is_unsigned,
    is_representable_integer, etc.
-/
def isPureStdlibFunction (name : String) : Bool :=
  name ∈ [
    "conv_loaded_int",
    "conv_int",
    "wrapI",
    "is_signed",
    "is_unsigned",
    "is_representable_integer",
    "ivmin",
    "ivmax",
    "sizeof",
    "alignof"
  ]

/-- Theorem: Pure stdlib functions don't cause UB.

    These functions only perform pure computations on values - they never
    access memory or trigger undefined behavior.
-/
theorem wpPureN_stdlib_pure (fuel : Nat) (sym : Sym) (args : List Pexpr) (Q : PurePost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState)
    (h_pure : isPureStdlibFunction (sym.name.getD "") = true) :
    wpPureN fuel ⟨[], none, .call (.sym sym) args⟩ Q env interpEnv state ↔
    -- For pure stdlib functions, we just need args to evaluate successfully
    -- and the result to satisfy Q
    (∀ arg ∈ args, wpPureN fuel ⟨[], none, arg⟩ (fun _ _ => True) env interpEnv state) ∧
    (∃ v, Q v state) := by
  -- These functions never trigger UB, only compute values
  sorry

/-! ## Example: Proving Simple Properties

Demonstrate how to use the WP calculus to prove UB-freeness.
-/

/-- Create an integer value for examples -/
def mkIntVal (n : Int) : Value :=
  .object (.integer ⟨n, .none⟩)

/-- Example: literal 5 is UB-free and returns the expected value -/
example : wpPure ⟨[], none, .val (mkIntVal 5)⟩
    (fun v _ => v = mkIntVal 5)
    [] default default := by
  simp only [wpPure_val]

/-- Example: literal true is UB-free -/
example : wpPure ⟨[], none, .val Value.true_⟩ (fun _ _ => True) [] default default := by
  simp only [wpPure_val]

/-- Example: unit is UB-free -/
example : wpPure ⟨[], none, .val Value.unit⟩ (fun v _ => v = Value.unit) [] default default := by
  simp only [wpPure_val]

/-! ### Concrete WP Examples

These examples demonstrate that the WP infrastructure works correctly
by computing specific cases. They serve as sanity checks and show how
the WP calculus will be used in practice.
-/

/-- Example: if true then 1 else 2 is UB-free (evaluates without UB)

    This example verifies that `wpPureN` correctly computes for concrete
    expressions. Uses small fuel (10) for fast reduction.
-/
example : wpPureN 10 ⟨[], none, .if_ (.val .true_) (.val (mkIntVal 1)) (.val (mkIntVal 2))⟩
    (fun _ _ => True) [] default default := by
  -- Unfold and let Lean reduce the computation
  simp only [wpPureN, evalPexpr, mkAPexpr, bind, pure,
    ReaderT.bind, ReaderT.pure, ReaderT.run,
    StateT.bind, StateT.pure, StateT.run,
    Except.bind, Except.pure]

/-- Example: if false then 1 else 2 is UB-free -/
example : wpPureN 10 ⟨[], none, .if_ (.val .false_) (.val (mkIntVal 1)) (.val (mkIntVal 2))⟩
    (fun _ _ => True) [] default default := by
  simp only [wpPureN, evalPexpr, mkAPexpr, bind, pure,
    ReaderT.bind, ReaderT.pure, ReaderT.run,
    StateT.bind, StateT.pure, StateT.run,
    Except.bind, Except.pure]

/-! ## Compositional Rules (Fuel-Indexed)

These rules enable modular reasoning about WP. They are fuel-indexed
because `evalPexpr (fuel + 1)` for compound expressions uses `evalPexpr fuel`
for subexpressions.

The key insight is that `evalPexpr` is structured as:
```
evalPexpr (fuel + 1) env pe = match pe.expr with
  | .val v => pure v
  | .if_ cond then_ else_ =>
      evalPexpr fuel env cond >>= fun cv =>
        if cv = true_ then evalPexpr fuel env then_
        else if cv = false_ then evalPexpr fuel env else_
        else error
  ...
```

This structure means the WP for a compound expression relates to the WP
of its subexpressions with one less fuel.

Note: The proofs below use `sorry` because the current proof approach
(unfolding `evalPexpr` and case splitting) doesn't work well with Lean's
definitional equality checking for large mutual recursive functions.

A better approach would be to define `evalPexpr` using well-founded recursion
in a way that enables definitional unfolding, or to prove these lemmas
using a relational characterization of evaluation.
-/

/-- Helper: mkAPexpr equals the struct literal -/
theorem mkAPexpr_eq (e : Pexpr) : mkAPexpr e = ⟨[], none, e⟩ := rfl

/-- Helper: Except.bind on error -/
@[simp] theorem Except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

/-- Helper: Except.bind on ok -/
@[simp] theorem Except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- Monad bind distribution for InterpM through .run.run

    This lemma shows how bind distributes through running the monad transformers.
    Key insight: (m >>= f).run env).run state decomposes based on m's result.
-/
theorem InterpM_bind_run {α β : Type} (m : InterpM α) (f : α → InterpM β)
    (env : InterpEnv) (state : InterpState) :
    ((m >>= f).run env).run state =
    match (m.run env).run state with
    | .ok (v, s') => ((f v).run env).run s'
    | .error e => .error e := by
  simp only [bind, ReaderT.bind, StateT.bind, ReaderT.run, StateT.run]
  -- After simp, LHS is: (m env state).bind (fun (v, s') => f v env s')
  -- RHS is: match m env state with | ok (v,s') => f v env s' | error e => error e
  -- Split on m env state and substitute
  split
  · -- ok case: have heq : m env state = ok (v, s')
    rename_i v s' heq
    simp only [heq, Except.bind]
  · -- error case: have heq : m env state = error e
    rename_i e heq
    simp only [heq, Except.bind]

/-- WP for conditionals (fuel-indexed): requires WP for condition, then appropriate branch. -/
theorem wpPureN_if (fuel : Nat) (cond then_ else_ : Pexpr) (Q : PurePost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN (fuel + 1) ⟨[], none, .if_ cond then_ else_⟩ Q env interpEnv state ↔
    wpPureN fuel ⟨[], none, cond⟩ (fun v s =>
      match v with
      | .true_ => wpPureN fuel ⟨[], none, then_⟩ Q env interpEnv s
      | .false_ => wpPureN fuel ⟨[], none, else_⟩ Q env interpEnv s
      | _ => True  -- Type error, not UB
    ) env interpEnv state := by
  -- Unfold wpPureN on both sides
  simp only [wpPureN]
  -- Rewrite LHS using the evalPexpr equation lemma
  rw [evalPexpr_if']
  simp only [mkAPexpr_eq]
  -- Use bind distribution lemma to decompose the LHS
  rw [InterpM_bind_run]
  -- Now both sides have: match (evalPexpr cond).run.run with | ok => ... | error => ...
  -- Prove equivalence by case splitting
  constructor
  · -- Forward direction
    intro h
    cases hcond : ((evalPexpr fuel env ⟨[], none, cond⟩).run interpEnv).run state with
    | error e =>
      simp only [hcond] at h ⊢
      cases e with
      | undefinedBehavior _ _ => exact h
      | _ => trivial
    | ok p =>
      obtain ⟨condVal, state'⟩ := p
      simp only [hcond] at h ⊢
      cases condVal with
      | true_ => exact h
      | false_ => exact h
      | _ => trivial
  · -- Backward direction
    intro h
    cases hcond : ((evalPexpr fuel env ⟨[], none, cond⟩).run interpEnv).run state with
    | error e =>
      simp only [hcond] at h ⊢
      cases e with
      | undefinedBehavior _ _ => exact h
      | _ => trivial
    | ok p =>
      obtain ⟨condVal, state'⟩ := p
      simp only [hcond] at h ⊢
      cases condVal with
      | true_ => exact h
      | false_ => exact h
      | _ => trivial

/-- WP for let binding (fuel-indexed): WP of e1, then WP of e2 with bindings. -/
theorem wpPureN_let (fuel : Nat) (pat : APattern) (e1 e2 : Pexpr) (Q : PurePost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN (fuel + 1) ⟨[], none, .let_ pat e1 e2⟩ Q env interpEnv state ↔
    wpPureN fuel ⟨[], none, e1⟩ (fun v1 s =>
      match matchPattern pat v1 with
      | some bindings => wpPureN fuel ⟨[], none, e2⟩ Q (bindAllInEnv bindings env) interpEnv s
      | none => True  -- Pattern match failure, not UB
    ) env interpEnv state := by
  simp only [wpPureN]
  rw [evalPexpr_let']
  simp only [mkAPexpr_eq]
  -- Use bind distribution lemma
  rw [InterpM_bind_run]
  -- Now both sides have the same structure
  constructor
  · -- Forward direction
    intro h
    cases he1 : ((evalPexpr fuel env ⟨[], none, e1⟩).run interpEnv).run state with
    | error e =>
      simp only [he1] at h ⊢
      cases e with
      | undefinedBehavior _ _ => exact h
      | _ => trivial
    | ok p =>
      obtain ⟨v1, state'⟩ := p
      simp only [he1] at h ⊢
      cases hpat : matchPattern pat v1 with
      | none =>
        simp only [hpat] at h ⊢
        -- h : True, goal reduces to True after throw unfolds
      | some bindings =>
        simp only [hpat] at h ⊢
        exact h
  · -- Backward direction
    intro h
    cases he1 : ((evalPexpr fuel env ⟨[], none, e1⟩).run interpEnv).run state with
    | error e =>
      simp only [he1] at h ⊢
      cases e with
      | undefinedBehavior _ _ => exact h
      | _ => trivial
    | ok p =>
      obtain ⟨v1, state'⟩ := p
      simp only [he1] at h ⊢
      cases hpat : matchPattern pat v1 with
      | none =>
        -- Goal: match (throw patternMatchFailed).run ... with ... = True
        -- throw e unfolds to Except.error e, which matches the non-UB error case
        simp only [throw, throwThe, MonadExcept.throw, ReaderT.run, StateT.run]
        trivial
      | some bindings =>
        simp only [hpat] at h ⊢
        exact h

/-- WP for binary operations (fuel-indexed): first operand must be UB-free. -/
theorem wpPureN_binop_implies_e1 (fuel : Nat) (op : Binop) (e1 e2 : Pexpr) (Q : PurePost)
    (env : List (HashMap Sym Value)) (interpEnv : InterpEnv) (state : InterpState) :
    wpPureN (fuel + 1) ⟨[], none, .op op e1 e2⟩ Q env interpEnv state →
    wpPureN fuel ⟨[], none, e1⟩ (fun _ _ => True) env interpEnv state := by
  intro h
  simp only [wpPureN] at h ⊢
  rw [evalPexpr_op'] at h
  simp only [mkAPexpr_eq] at h
  -- Use bind distribution lemma to decompose LHS
  rw [InterpM_bind_run] at h
  cases he1 : ((evalPexpr fuel env ⟨[], none, e1⟩).run interpEnv).run state with
  | error e =>
    -- e1 failed - h has this error result
    simp only [he1] at h ⊢
    cases e with
    | undefinedBehavior _ _ => exact h
    | _ => trivial
  | ok p =>
    -- e1 succeeded - goal is True
    trivial

end CToLean.Theorems.WP
