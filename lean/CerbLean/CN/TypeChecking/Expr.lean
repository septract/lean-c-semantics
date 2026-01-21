/-
  CN Expression Checking
  Corresponds to: cn/lib/check.ml (check_expr)

  Walks effectful Core expressions, threading resources through the computation.
  This is the main entry point for Level 2 (separation logic verification).

  Audited: 2026-01-20 against cn/lib/check.ml
-/

import CerbLean.CN.TypeChecking.Pexpr
import CerbLean.CN.TypeChecking.Action

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Expr AExpr APexpr APattern Name)
open CerbLean.CN.Types

/-! ## Path Conditions

For conditional branches, we track path conditions to enable
reasoning about branch-specific constraints.
-/

/-- Add a path condition for the current branch -/
def withPathCondition (cond : IndexTerm) (m : TypingM α) : TypingM α := do
  -- Add the condition as a constraint (assumption)
  TypingM.addC (.t cond)
  m

/-- Create the negation of a term -/
def negTerm (t : IndexTerm) : IndexTerm :=
  AnnotTerm.mk (.unop .not t) .bool t.loc

/-! ## Branch Handling

For conditionals and case expressions, we need to:
1. Save the current resource state
2. Check each branch
3. Verify resource states agree (in CN, branches must produce same resources)

Corresponds to: cn/lib/check.ml branch merging logic
-/

/-- Check if two resource names match (same predicate type and C type) -/
def resourceNameMatch (n1 n2 : ResourceName) : Bool :=
  match n1, n2 with
  | .owned ct1 init1, .owned ct2 init2 => ct1 == ct2 && init1 == init2
  | .pname s1, .pname s2 => s1.id == s2.id
  | _, _ => false

/-- Syntactic comparison of constants (for the common cases) -/
def constEq : Const → Const → Bool
  | .z v1, .z v2 => v1 == v2
  | .bits s1 w1 v1, .bits s2 w2 v2 => s1 == s2 && w1 == w2 && v1 == v2
  | .bool b1, .bool b2 => b1 == b2
  | .unit, .unit => true
  | .null, .null => true
  | .allocId id1, .allocId id2 => id1 == id2
  | .pointer p1, .pointer p2 => p1.allocId == p2.allocId && p1.addr == p2.addr
  | _, _ => false  -- Conservative: different constant types don't match

/-- Syntactic comparison of terms (conservative - only matches identical structure).
    A full implementation would use the SMT solver for semantic equality. -/
partial def termEq : Term → Term → Bool
  | .const c1, .const c2 => constEq c1 c2
  | .sym s1, .sym s2 => s1.id == s2.id
  | .unop op1 a1, .unop op2 a2 => op1 == op2 && annotTermEq a1 a2
  | .binop op1 l1 r1, .binop op2 l2 r2 => op1 == op2 && annotTermEq l1 l2 && annotTermEq r1 r2
  | _, _ => false  -- Conservative: different structures don't match
where
  annotTermEq (t1 t2 : AnnotTerm) : Bool := termEq t1.term t2.term

/-- Check if two predicates match (same name and pointer).
    We compare pointers syntactically for now - a full implementation
    would use the SMT solver to check semantic equality. -/
def predicateMatch (p1 p2 : Predicate) : Bool :=
  resourceNameMatch p1.name p2.name &&
  -- Compare pointers syntactically (term equality)
  -- This is conservative - pointers must be syntactically identical
  termEq p1.pointer.term p2.pointer.term

/-- Check if two requests match structurally -/
def requestMatch (r1 r2 : Request) : Bool :=
  match r1, r2 with
  | .p p1, .p p2 => predicateMatch p1 p2
  | .q q1, .q q2 =>
    resourceNameMatch q1.name q2.name &&
    termEq q1.pointer.term q2.pointer.term &&
    q1.q.1.id == q2.q.1.id
  | _, _ => false

/-- Find a matching resource in a list, return remaining resources if found -/
def findMatchingResource (r : Resource) (rs : List Resource)
    : Option (Resource × List Resource) :=
  go rs []
where
  go : List Resource → List Resource → Option (Resource × List Resource)
  | [], _ => none
  | r' :: rest, acc =>
    if requestMatch r.request r'.request then
      some (r', acc.reverse ++ rest)
    else
      go rest (r' :: acc)

/-- Format a resource name for error messages -/
def formatResourceName (name : ResourceName) : String :=
  match name with
  | .owned _ initState => s!"Owned({if initState == Init.init then "Init" else "Uninit"})"
  | .pname s => s!"{s.name.getD "?"}"

/-- Check that resources after branches match.
    In CN, both branches must end with the same resources.

    Corresponds to: branch merging in cn/lib/check.ml

    The check ensures:
    1. Both branches have the same number of resources
    2. Each resource in one branch has a matching resource in the other
       (same predicate type and pointer)

    Note: Output values may differ between branches - that's expected
    when branches write different values. What matters is that the
    *structure* of resources is the same. -/
def checkResourcesMatch (ctx1 ctx2 : Context) : TypingM Unit := do
  let rs1 := ctx1.resources
  let rs2 := ctx2.resources

  -- First check: same number of resources
  if rs1.length != rs2.length then
    TypingM.fail (.other s!"Branch resource mismatch: then-branch has {rs1.length} resources, else-branch has {rs2.length}")

  -- Second check: each resource in rs1 has a match in rs2
  let mut remaining := rs2
  for r1 in rs1 do
    match findMatchingResource r1 remaining with
    | some (_, rest) => remaining := rest
    | none =>
      let name := match r1.request with
        | .p p => formatResourceName p.name
        | .q q => s!"each {formatResourceName q.name}"
      TypingM.fail (.other s!"Branch resource mismatch: then-branch has {name} resource not matched in else-branch")

/-! ## Expression Checking

Main function to walk effectful Core expressions.
-/

/-- Check an effectful expression, threading resources.
    Returns the result value of the expression.

    Corresponds to: check_expr in check.ml lines 1506-2315 -/
partial def checkExpr (e : AExpr) : TypingM IndexTerm := do
  let loc := getAnnotsLoc e.annots
  match e.expr with
  -- Pure expression (no side effects)
  | .pure pe =>
    checkPexpr pe

  -- Memory operation (memop)
  | .memop _op args =>
    -- Evaluate all arguments (simplified - just return unit)
    for arg in args do
      let _ ← checkPexpr arg
    return mkUnitTerm loc

  -- Memory action (create, kill, store, load)
  | .action pact =>
    checkAction pact

  -- Weak sequencing: e1 ; e2 (resources flow from e1 to e2)
  | .wseq pat e1 e2 =>
    let v1 ← checkExpr e1
    -- Bind the result to the pattern
    let bindings ← bindPattern pat v1
    let result ← checkExpr e2
    unbindPattern bindings
    return result

  -- Strong sequencing: e1 ; e2 (same as weak for sequential code)
  | .sseq pat e1 e2 =>
    let v1 ← checkExpr e1
    let bindings ← bindPattern pat v1
    let result ← checkExpr e2
    unbindPattern bindings
    return result

  -- Let binding: let pat = pe in e2
  | .let_ pat pe e2 =>
    let v1 ← checkPexpr pe
    let bindings ← bindPattern pat v1
    let result ← checkExpr e2
    unbindPattern bindings
    return result

  -- Conditional: if cond then thenE else elseE
  | .if_ cond thenE elseE =>
    let condVal ← checkPexpr cond

    -- Save FULL state for branching (including fresh counter, param map, etc.)
    -- This is critical: without this, fresh symbols in different branches
    -- would have different IDs, causing spurious resource mismatches.
    let savedState ← TypingM.getState

    -- Check "then" branch with condition as assumption
    let _thenResult ← withPathCondition condVal (checkExpr thenE)
    let thenCtx ← TypingM.getContext

    -- Restore FULL state and check "else" branch with negated condition
    TypingM.setState savedState
    let elseResult ← withPathCondition (negTerm condVal) (checkExpr elseE)
    let elseCtx ← TypingM.getContext

    -- Check that branches produce compatible resources
    checkResourcesMatch thenCtx elseCtx

    -- For now, return the else result (both branches should return same type)
    return elseResult

  -- Case expression
  | .case_ scrut branches =>
    let scrutVal ← checkPexpr scrut

    if branches.isEmpty then
      TypingM.fail (.other "Empty case expression")

    -- Check each branch (save FULL state to ensure consistent symbol IDs)
    let savedState ← TypingM.getState
    let mut lastResult := mkUnitTerm loc

    for (pat, body) in branches do
      TypingM.setState savedState
      let bindings ← bindPattern pat scrutVal
      lastResult ← checkExpr body
      unbindPattern bindings

    return lastResult

  -- C function call
  | .ccall funPtr _funTy args =>
    -- Evaluate function pointer and arguments
    let _fnVal ← checkPexpr funPtr
    let argVals ← args.mapM checkPexpr

    -- In a full implementation, we would:
    -- 1. Look up the function's specification
    -- 2. Check that we have the required precondition resources
    -- 3. Consume those resources
    -- 4. Produce the postcondition resources
    -- 5. Return the result

    -- For now, just return a placeholder
    let resultBt := if argVals.isEmpty then .unit else argVals.head!.bt
    return AnnotTerm.mk (.const .unit) resultBt loc

  -- Named procedure call
  | .proc name args =>
    let argVals ← args.mapM checkPexpr

    -- Similar to ccall - would need to look up the procedure's spec
    let fnSym := match name with
      | .sym s => s
      | .impl _ => { id := 0, name := some "impl" : Sym }

    let resultBt := if argVals.isEmpty then .unit else argVals.head!.bt
    return AnnotTerm.mk (.apply fnSym argVals) resultBt loc

  -- Unsequenced (for sequential, pick first ordering)
  | .unseq es =>
    if es.isEmpty then
      return mkUnitTerm loc

    -- For sequential execution, just execute in order
    let mut result := mkUnitTerm loc
    for e' in es do
      result ← checkExpr e'
    return result

  -- Bound (resource boundary)
  | .bound e' =>
    checkExpr e'

  -- Nondeterministic choice (pick first for now)
  | .nd es =>
    if es.isEmpty then
      return mkUnitTerm loc
    checkExpr es.head!

  -- Save/run (for labels/goto)
  -- save label: ret_ty (param := default, ...) in body
  -- The parameters are bound in the scope of the body
  | .save _retSym _retTy args body =>
    -- Bind save parameters as variables in scope
    -- Each arg is (sym, basetype, default_expr)
    let mut bindings : List (Sym × BaseType) := []
    for (sym, bt, _defaultPe) in args do
      -- Convert Core.BaseType to CN BaseType
      let cnBt := coreBaseTypeToCN bt
      TypingM.addL sym cnBt loc s!"save parameter {sym.name.getD ""}"
      bindings := (sym, cnBt) :: bindings
    -- Check body with parameters in scope
    let result ← checkExpr body
    -- Unbind parameters (in reverse order)
    for (sym, _) in bindings do
      TypingM.modifyContext fun ctx =>
        { ctx with logical := ctx.logical.filter (·.1.id != sym.id) }
    return result

  | .run _label args =>
    for arg in args do
      let _ ← checkPexpr arg
    return mkUnitTerm loc

  -- Concurrency constructs (not fully supported)
  | .par es =>
    -- For parallel, check all expressions but don't merge properly
    if es.isEmpty then
      return mkUnitTerm loc

    let mut result := mkUnitTerm loc
    for e' in es do
      result ← checkExpr e'
    return result

  | .wait _tid =>
    return mkUnitTerm loc

where
  /-- Helper to create a unit term -/
  mkUnitTerm (loc : Core.Loc) : IndexTerm :=
    AnnotTerm.mk (.const .unit) .unit loc

/-! ## Function Body Checking

Check a complete function body against its specification.
-/

/-- Check a function body, returning the result value.
    This is the entry point for checking a function's implementation.

    The process:
    1. Precondition resources should already be in context
    2. Check the body expression, tracking resources
    3. Return value should satisfy postcondition constraints

    Corresponds to: the body checking part of check_procedure in check.ml -/
def checkFunctionBody (body : AExpr) : TypingM IndexTerm := do
  checkExpr body

end CerbLean.CN.TypeChecking
