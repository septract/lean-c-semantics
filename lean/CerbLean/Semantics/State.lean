/-
  Thread state data structures for small-step interpreter
  Corresponds to: cerberus/frontend/model/core_run_aux.lem

  CRITICAL: This file must match Cerberus data structures EXACTLY.
  Each type is documented with its Cerberus correspondence.
-/

import CerbLean.Semantics.Monad
import CerbLean.Core.Expr
import Std.Data.HashMap

namespace CerbLean.Semantics

open CerbLean.Core
open Std (HashMap)

/-! ## Continuation Elements

Corresponds to: core_run_aux.lem lines 56-60
```lem
type continuation_element 'a =
  | Kunseq of list annot * list (Core.expr 'a) * list (Core.expr 'a)
  | Kwseq  of list annot * Core.pattern * Core.expr 'a
  | Ksseq  of list annot * Core.pattern * Core.expr 'a
```
-/

/-- A single continuation element on the stack.
    Corresponds to: continuation_element in core_run_aux.lem:56-60
    Audited: 2025-01-01
    Deviations: None -/
inductive ContElem where
  /-- Unsequenced evaluation context: (done expressions, remaining expressions)
      Corresponds to: Kunseq annots es1 es2 -/
  | unseq (annots : Annots) (done : List AExpr) (remaining : List AExpr)
  /-- Weak sequence: waiting for e1, then bind to pattern and continue with e2
      Corresponds to: Kwseq annots pat e2 -/
  | wseq (annots : Annots) (pat : APattern) (e2 : AExpr)
  /-- Strong sequence: waiting for e1, then bind to pattern and continue with e2
      Corresponds to: Ksseq annots pat e2 -/
  | sseq (annots : Annots) (pat : APattern) (e2 : AExpr)
  /-- Dynamic annotation context: wrap result in annotation when complete.
      Corresponds to: Cannot in core_run_aux.lem context type.
      This is used when stepping into {A}e where e needs reduction.
      Note: Cerberus uses evaluation contexts rather than continuations for this,
      but the behavior is equivalent. -/
  | annot (annots : Annots) (dynAnnots : DynAnnotations)
  /-- Bound context: marks a boundary for neg action transformation.
      Corresponds to: Cbound in core_run_aux.lem context type.
      When a neg action is encountered, the context up to the first bound
      is used to create the neg action transformation (unseq structure). -/
  | bound (annots : Annots)
  deriving Inhabited

/-! ## Continuation

Corresponds to: core_run_aux.lem line 62
```lem
type continuation 'a = list (continuation_element 'a)
```
-/

/-- A continuation is a list of continuation elements.
    Corresponds to: continuation in core_run_aux.lem:62
    Audited: 2025-01-01
    Deviations: None -/
abbrev Continuation := List ContElem

/-! ## Labeled Continuations

Corresponds to: core_run_aux.lem line 64
```lem
type labeled_continuations 'a = map Symbol.sym (list (Symbol.sym * core_base_type) * expr 'a)
```
-/

/-- A labeled continuation stores parameter symbols and the continuation body.
    Corresponds to: labeled_continuations values in core_run_aux.lem:64
    Audited: 2025-01-01
    Deviations: None -/
structure LabeledCont where
  /-- Parameter symbols (without types in our representation) -/
  params : List Sym
  /-- The continuation body expression -/
  body : AExpr
  deriving Inhabited

/-- Map from label symbols to their continuations.
    Corresponds to: labeled_continuations in core_run_aux.lem:64
    Audited: 2025-01-01
    Deviations: We don't store parameter types (core_base_type) as they're not
                needed for our sequential interpreter -/
abbrev LabeledConts := HashMap Sym LabeledCont

/-- Map from procedure symbols to their labeled continuations.
    Corresponds to: labeled field in core_run_state (core_run_aux.lem:242)
    ```lem
    labeled: map Symbol.sym (labeled_continuations core_run_annotation);
    ```
    Audited: 2026-01-02
    Deviations: None -/
abbrev AllLabeledConts := HashMap Sym LabeledConts

/-! ## Stack

Corresponds to: core_run_aux.lem lines 67-76
```lem
type stack 'a =
  | Stack_empty
  | Stack_cons of maybe Symbol.sym * continuation 'a * stack 'a
  | Stack_cons2 of maybe Symbol.sym * context * stack 'a  -- for Core_reduction
```

Note: We only implement Stack_empty and Stack_cons. Stack_cons2 is for Core_reduction
which we don't use.
-/

/-- Call stack for the interpreter.
    Corresponds to: stack in core_run_aux.lem:67-76
    Audited: 2025-01-01
    Deviations: We don't implement Stack_cons2 (only for Core_reduction) -/
inductive Stack where
  /-- Empty stack (initial state or after all procedures return)
      Corresponds to: Stack_empty -/
  | empty
  /-- Stack frame: procedure symbol, current continuation, parent stack
      Corresponds to: Stack_cons of maybe Symbol.sym * continuation 'a * stack 'a -/
  | cons (procSym : Option Sym) (cont : Continuation) (parent : Stack)
  deriving Inhabited

namespace Stack

/-- Check if stack is empty.
    Corresponds to: is_empty_stack in core_run_aux.lem:129-135 -/
def isEmpty : Stack → Bool
  | .empty => true
  | .cons .. => false

/-- Push an empty continuation for a new procedure call.
    Corresponds to: push_empty_continuation in core_run_aux.lem:139-142
    ```lem
    let push_empty_continuation sym_opt sk =
      Stack_cons2 sym_opt CTX sk
    ```
    Note: Cerberus uses Stack_cons2 with CTX, but we use Stack_cons with []
    because we use the Stack_cons variant (not Stack_cons2 for Core_reduction) -/
def pushEmptyCont (procSym : Option Sym) (sk : Stack) : Stack :=
  .cons procSym [] sk

/-- Pop the entire frame from the stack, returning continuation and parent.
    Corresponds to: pop_stack in core_run_aux.lem:155-163
    ```lem
    let pop_stack = function
      | Stack_empty -> Exception.fail (Found_empty_stack "pop_stack")
      | Stack_cons _ cont sk -> Exception.return (cont, sk)
    ```
    -/
def popFrame : Stack → Option (Continuation × Stack)
  | .empty => none
  | .cons _ cont parent => some (cont, parent)

/-- Pop a single continuation element from the current frame.
    Corresponds to: pop_continuation_element in core_run_aux.lem:165-175
    ```lem
    let pop_continuation_element = function
      | Stack_empty -> Exception.fail (Found_empty_stack "pop_continuation_element")
      | Stack_cons _ [] _ -> Exception.fail Reached_end_of_proc
      | Stack_cons sym_opt (cont_elem :: cont) sk ->
          Exception.return (cont_elem, Stack_cons sym_opt cont sk)
    ``` -/
def popContElem : Stack → Option (ContElem × Stack)
  | .empty => none
  | .cons _ [] _ => none  -- End of procedure
  | .cons procSym (elem :: rest) parent => some (elem, .cons procSym rest parent)

/-- Push a continuation element onto the current frame.
    Corresponds to: push_continuation_element in core_run_aux.lem:178-186
    ```lem
    let push_continuation_element cont_elem = function
      | Stack_empty -> Exception.fail (Found_empty_stack "push_continuation_element")
      | Stack_cons sym_opt cont sk ->
          Exception.return (Stack_cons sym_opt (cont_elem :: cont) sk)
    ``` -/
def pushContElem (elem : ContElem) : Stack → Option Stack
  | .empty => none
  | .cons procSym cont parent => some (.cons procSym (elem :: cont) parent)

/-- Get the current procedure symbol (if any).
    Helper function not directly in Cerberus. -/
def currentProc : Stack → Option Sym
  | .empty => none
  | .cons procSym _ _ => procSym

/-- Extract exclusion IDs from dynamic annotations.
    These are the IDs from DA_neg annotations that should be inherited
    by inner annotations. -/
def extractExclusionIds (annots : DynAnnotations) : List Nat :=
  annots.filterMap fun da =>
    match da with
    | .neg id _ _ => some id
    | .pos _ _ => none

/-- Get the current exclusion context from the continuation stack.
    This collects exclusion IDs from all enclosing annotation contexts.
    When creating a new DA_neg annotation, these IDs should be added
    to its exclusion set to prevent false race detection.
    Corresponds to: add_exclusion in core_reduction.lem which adds
    exclusion IDs to the context. -/
def getExclusionContext (cont : Continuation) : List Nat :=
  cont.foldl (init := []) fun acc elem =>
    match elem with
    | .annot _ dynAnnots => acc ++ extractExclusionIds dynAnnots
    | _ => acc

/-- Get ALL dynamic annotations from the continuation stack.
    This collects all annotations from enclosing annotation contexts.
    Used for race checking when executing neg actions - the neg action's
    footprint must be checked against accumulated annotations.
    Corresponds to: Cerberus's neg action transformation which creates
    an unseq between the action and context annotations for race detection
    (core_reduction.lem:1285-1302). -/
def getContextAnnotations (cont : Continuation) : DynAnnotations :=
  cont.foldl (init := []) fun acc elem =>
    match elem with
    | .annot _ dynAnnots => acc ++ dynAnnots
    | _ => acc

/-- Result of break_at_bound: either no bound found, or bound with context.
    Corresponds to: break_at_bound_and_sseq result type in core_reduction.lem:849-852 -/
inductive BreakAtBoundResult where
  | noBound
  | boundNoSseq (ctxBound : ContElem) (ctxA : Continuation)
  deriving Inhabited

/-- Find the first bound in the continuation and split into context before and after.
    Returns the continuation elements UP TO (but not including) the bound,
    plus the bound element itself.
    Corresponds to: break_at_bound_and_sseq in core_reduction.lem:854-901
    Note: We don't implement the SSEQ case yet - for now, we only handle BOUND_NO_SSEQ. -/
def breakAtBound (cont : Continuation) : BreakAtBoundResult :=
  go cont []
where
  go : Continuation → Continuation → BreakAtBoundResult
  | [], _ => .noBound
  | elem :: rest, acc =>
    match elem with
    | .bound annots => .boundNoSseq elem acc.reverse
    | _ => go rest (elem :: acc)

/-- Add an exclusion ID to a single annotation's exclusion set.
    Corresponds to: add_exclusion_to_dyn_annot in core_reduction.lem:192-194 -/
def addExclusionToAnnot (n : Nat) : DynAnnotation → DynAnnotation
  | .neg id es fp => .neg id (n :: es) fp
  | .pos es fp => .pos (n :: es) fp

/-- Add an exclusion ID to all annotations' exclusion sets.
    Corresponds to: add_exclusion in core_reduction.lem:196-197 -/
def addExclusionToAnnots (n : Nat) (annots : DynAnnotations) : DynAnnotations :=
  annots.map (addExclusionToAnnot n)

/-- Add exclusion ID n to all annotations in the continuation.
    This modifies the dynAnnots in any .annot continuation elements.
    Corresponds to: add_exclusion in core_reduction.lem:925-944
    which adds the exclusion ID to all context annotations. -/
def addExclusionToCont (n : Nat) (cont : Continuation) : Continuation :=
  cont.map fun elem =>
    match elem with
    | .annot annots dynAnnots =>
        .annot annots (dynAnnots.map (addExclusionToAnnot n))
    | other => other

/-- Drop continuation elements until (but not including) the bound.
    Returns the continuation from the bound onwards (including the bound).
    This is used after the neg action transformation to "pop" the context
    that was captured and converted to an expression.
    Corresponds to: keeping ctx_bound in break_at_bound_and_sseq (core_reduction.lem:854-901) -/
def dropUntilBound (cont : Continuation) : Continuation :=
  go cont
where
  go : Continuation → Continuation
  | [] => []
  | elem :: rest =>
    match elem with
    | .bound _ => elem :: rest  -- Keep bound and everything after
    | _ => go rest

end Stack

/-! ## Thread State

Corresponds to: core_run_aux.lem lines 208-218
```lem
type thread_state = <|
  arena:  expr core_run_annotation;
  stack:  stack core_run_annotation;
  errno:  Mem.pointer_value;
  env: list (map Symbol.sym value);  -- Scoped environment
  current_proc_opt: maybe Symbol.sym;
  exec_loc: exec_location;
  current_loc: Loc.t;
|>
```
-/

/-- Thread state for the small-step interpreter.
    Corresponds to: thread_state in core_run_aux.lem:208-218
    Audited: 2025-01-01
    Deviations:
    - We don't track errno (errno handling is out of scope)
    - We don't track exec_loc (debugging info only)
    - We don't track current_loc (debugging info only) -/
structure ThreadState where
  /-- Current expression being evaluated (the "arena")
      Corresponds to: arena field -/
  arena : AExpr
  /-- Call stack with continuations
      Corresponds to: stack field -/
  stack : Stack := .empty
  /-- Scoped symbol environment (list of maps, head is innermost scope)
      Corresponds to: env field (list (map Symbol.sym value)) -/
  env : List (HashMap Sym Value) := [{}]
  /-- Current procedure being executed (for labeled continuation lookup)
      Corresponds to: current_proc_opt field
      Note: This duplicates info in stack but matches Cerberus structure -/
  currentProc : Option Sym := none
  deriving Inhabited

namespace ThreadState

/-- Look up a symbol in the environment (searches from innermost scope).
    This mirrors Cerberus's scoped environment lookup. -/
def lookupSym (st : ThreadState) (sym : Sym) : Option Value :=
  st.env.findSome? fun scope => scope[sym]?

/-- Bind a symbol in the innermost scope. -/
def bindSym (st : ThreadState) (sym : Sym) (val : Value) : ThreadState :=
  match st.env with
  | [] =>
    let emptyMap : HashMap Sym Value := {}
    { st with env := [emptyMap.insert sym val] }
  | scope :: rest => { st with env := (scope.insert sym val) :: rest }

/-- Bind multiple symbols in the innermost scope. -/
def bindSyms (st : ThreadState) (bindings : List (Sym × Value)) : ThreadState :=
  bindings.foldl (fun s (sym, val) => s.bindSym sym val) st

/-- Push a new empty scope (for entering a function). -/
def pushScope (st : ThreadState) : ThreadState :=
  { st with env := {} :: st.env }

/-- Pop the innermost scope (for leaving a function). -/
def popScope (st : ThreadState) : ThreadState :=
  match st.env with
  | [] => st
  | _ :: rest => { st with env := if rest.isEmpty then [{}] else rest }

/-- Push a new scope with initial bindings (for function parameters). -/
def pushScopeWith (st : ThreadState) (bindings : List (Sym × Value)) : ThreadState :=
  let newScope := bindings.foldl (fun m (s, v) => m.insert s v) {}
  { st with env := newScope :: st.env }

end ThreadState

/-! ## Pattern Matching

Helper for extracting bindings from pattern matches.
Corresponds to the pattern matching in core_aux.lem (match_pattern).
-/

mutual
/-- Extract symbol bindings from a pattern match.
    Returns None if pattern doesn't match.
    Terminates because we recurse on structurally smaller patterns. -/
def matchPatternBindings (pat : Pattern) (val : Value) : Option (List (Sym × Value)) :=
  match pat, val with
  | .base (some sym) _, v =>
    -- Named pattern: bind the symbol
    some [(sym, v)]
  | .base none _, _ =>
    -- Wildcard pattern: no bindings
    some []
  | .ctor .specified [inner], .loaded (.specified ov) =>
    -- Corresponds to: core_aux.lem:1119-1120 (subst_pattern_val)
    --   (CaseCtor Cspecified [pat'], Vloaded (LVspecified oval)) ->
    --       subst_pattern_val pat' (Vobject oval) expr
    matchPatternBindings inner (.object ov)
  | .ctor .unspecified [inner], .loaded (.unspecified ty) =>
    -- Unspecified(cty) pattern - match inner against the ctype
    -- Corresponds to: core_aux.lem:1121-1122 (subst_pattern_val)
    --   (CaseCtor Cunspecified [pat'], Vloaded (LVunspecified ty)) ->
    --       subst_pattern_val pat' (Vctype ty) expr
    matchPatternBindings inner (.ctype ty)
  | .ctor .tuple args, .tuple vs =>
    if args.length != vs.length then none else
    matchPatternBindingsAll args vs
  | .ctor .array args, .list _ vs =>
    if args.length != vs.length then none else
    matchPatternBindingsAll args vs
  | .ctor (.nil _) [], .list _ [] =>
    some []
  | .ctor .cons [hd, tl], .list ty (v :: vs) =>
    match matchPatternBindings hd v, matchPatternBindings tl (.list ty vs) with
    | some b1, some b2 => some (b1 ++ b2)
    | _, _ => none
  | _, .true_ =>
    -- Match true against any pattern that accepts boolean true
    some []
  | _, .false_ =>
    -- Match false against any pattern that accepts boolean false
    some []
  | _, .unit =>
    -- Match unit value
    if let .base none .unit := pat then some [] else none
  | _, _ =>
    none

/-- Helper: match a list of patterns against a list of values -/
def matchPatternBindingsAll (pats : List Pattern) (vals : List Value) : Option (List (Sym × Value)) :=
  match pats, vals with
  | [], [] => some []
  | p :: ps, v :: vs =>
    match matchPatternBindings p v, matchPatternBindingsAll ps vs with
    | some b1, some b2 => some (b1 ++ b2)
    | _, _ => none
  | _, _ => none
end

namespace ThreadState

/-- Update env by applying a pattern match.
    Corresponds to: update_env in core_run.lem (used in Esseq case)
    ```lem
    env= update_env pat cval1 th_st.env
    ``` -/
def updateEnv (st : ThreadState) (pat : APattern) (val : Value) : Option ThreadState := do
  let bindings ← matchPatternBindings pat.pat val
  pure (st.bindSyms bindings)

end ThreadState

/-! ## Step Result

Result of a single step of execution.
-/

/-- Result of a single step.
    Corresponds to the various Step_* constructors in core_reduction.lem.
    Step_* corresponds to deterministic steps, Step_nd2 to non-deterministic. -/
inductive StepResult where
  /-- Execution completed with a value -/
  | done (val : Value)
  /-- Continue with new thread state (deterministic) -/
  | continue_ (st : ThreadState)
  /-- Non-deterministic branch: multiple possible next states.
      Corresponds to: Step_nd2 in core_reduction.lem:145
      Each branch is a complete ThreadState with its own arena and continuation stack.
      The driver decides how to explore these branches (exhaustive, random, or pick first). -/
  | branches (states : List ThreadState)
  /-- Error occurred -/
  | error (err : InterpError)
  deriving Inhabited

/-! ## Apply Continuation

Corresponds to: apply_continuation in core_run_aux.lem:106-121
```lem
val apply_continuation: forall 'a. continuation 'a -> expr 'a -> expr 'a
let apply_continuation cont expr =
  let f _cont (Expr annot _ as expr) =
    match _cont with
      | Kwseq annots pat e2 -> Expr annots (Ewseq pat expr e2)
      | Ksseq annots pat e2 -> Expr annots (Esseq pat expr e2)
      | Kunseq annots es1 es2 -> Expr annots (Eunseq $ es1 ++ (expr :: es2))
    end in
  foldl (fun acc x -> f x acc) expr cont
```
-/

/-- Apply a continuation to an expression, wrapping it in the appropriate
    sequencing constructs.
    Corresponds to: apply_continuation in core_run_aux.lem:106-121
    Audited: 2025-01-01
    Deviations: None -/
def applyContinuation (cont : Continuation) (expr : AExpr) : AExpr :=
  cont.foldl applyContElem expr
where
  applyContElem (e : AExpr) (elem : ContElem) : AExpr :=
    match elem with
    | .wseq annots pat e2 =>
      -- Expr annots (Ewseq pat expr e2)
      -- e : AExpr (the accumulated expression)
      -- e2 : AExpr (the continuation)
      -- Result: wrap e with wseq to e2
      { annots, expr := .wseq pat e e2 }
    | .sseq annots pat e2 =>
      -- Expr annots (Esseq pat expr e2)
      { annots, expr := .sseq pat e e2 }
    | .unseq annots done remaining =>
      -- Expr annots (Eunseq $ es1 ++ (expr :: es2))
      { annots, expr := .unseq (done ++ [e] ++ remaining) }
    | .annot annots dynAnnots =>
      -- Expr annots (Eannot dynAnnots expr)
      -- Corresponds to: Cannot annot xs ctx' -> Expr annot (Eannot xs (apply_ctx ctx' expr))
      { annots, expr := .annot dynAnnots e }
    | .bound annots =>
      -- Expr annots (Ebound expr)
      -- RESTORED: Needed for neg action transformation which rebuilds expressions.
      -- Value propagation now happens one-by-one in Step.lean, so this no longer
      -- causes infinite loops (bound(v) -> v is handled in the step function).
      { annots, expr := .bound e }

end CerbLean.Semantics
