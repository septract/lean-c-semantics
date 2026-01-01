/-
  Thread state data structures for small-step interpreter
  Corresponds to: cerberus/frontend/model/core_run_aux.lem

  CRITICAL: This file must match Cerberus data structures EXACTLY.
  Each type is documented with its Cerberus correspondence.
-/

import CToLean.Semantics.Monad
import CToLean.Core.Expr
import Std.Data.HashMap

namespace CToLean.Semantics

open CToLean.Core
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

/-- Extract symbol bindings from a pattern match.
    Returns None if pattern doesn't match. -/
partial def matchPatternBindings (pat : Pattern) (val : Value) : Option (List (Sym × Value)) :=
  match pat, val with
  | .base (some sym) _, v =>
    -- Named pattern: bind the symbol
    some [(sym, v)]
  | .base none _, _ =>
    -- Wildcard pattern: no bindings
    some []
  | .ctor .specified [inner], .loaded (.specified ov) =>
    matchPatternBindings inner (.object ov)
  | .ctor .unspecified [], .loaded (.unspecified _) =>
    some []
  | .ctor .tuple args, .tuple vs =>
    if args.length != vs.length then none else
    let results := args.zip vs |>.map fun (p, v) => matchPatternBindings p v
    if results.any Option.isNone then none else
    some (results.filterMap id |>.flatten)
  | .ctor .array args, .list _ vs =>
    if args.length != vs.length then none else
    let results := args.zip vs |>.map fun (p, v) => matchPatternBindings p v
    if results.any Option.isNone then none else
    some (results.filterMap id |>.flatten)
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
    Corresponds to the various Step_* constructors in core_run.lem. -/
inductive StepResult where
  /-- Execution completed with a value -/
  | done (val : Value)
  /-- Continue with new thread state -/
  | continue_ (st : ThreadState)
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

end CToLean.Semantics
