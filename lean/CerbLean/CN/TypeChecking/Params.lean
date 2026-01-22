/-
  Parameter handling for CN type checking.

  This module implements the "lazy muCore transformation" for function parameters.

  ## Background

  In Core IR (from Cerberus), function parameters are stored in stack slots:
  - Parameter `p` of type `T*` is represented as a stack slot address
  - The actual pointer value is obtained by `load(T*, p_slot)`

  In CN's muCore representation, parameters are direct values:
  - Parameter `p` IS the pointer value directly

  CN's `core_to_mucore.ml` transforms Core to muCore by:
  1. Mapping stack slot symbols to value symbols via `C_vars.Value`
  2. Replacing `load(T, stack_slot)` with the value symbol

  ## Our Approach: Lazy Transformation

  Instead of transforming the AST upfront, we:
  1. Build a `ParamValueMap` mapping stack slot IDs → value terms
  2. Track aliases (e.g., `let a = pure(p)` means `a` aliases `p`)
  3. In `handleLoad`, check if the pointer is a mapped symbol and return the value directly

  This is semantically equivalent to CN's approach but done lazily during type checking.

  ## Correspondence to CN

  | CN (core_to_mucore.ml)              | Our Implementation                    |
  |-------------------------------------|---------------------------------------|
  | `C_vars.Value(pure_arg, sbt)`       | `ParamValueMap` entry                 |
  | `C_vars.add [(mut_arg, state)]`     | `addParamValue` in TypingM            |
  | Transform at translation time       | Transform at load time (lazy)         |

  Audited: 2026-01-20 against cn/lib/core_to_mucore.ml lines 745-786
-/

import CerbLean.Core
import CerbLean.CN.Types
import CerbLean.CN.TypeChecking.Check
import CerbLean.CN.TypeChecking.Expr
import CerbLean.CN.Verification.Obligation
import Std.Data.HashMap

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types
open CerbLean.CN.Verification (TypeCheckResult)

/-! ## Type Aliases -/

/-- Mapping from symbol ID to what it aliases (for tracking `let x = pure(p)` patterns) -/
abbrev AliasMap := Std.HashMap Nat Nat

/-! ## Helper Functions -/

/-- Check if a pattern binds a single symbol -/
def patternBindsSym (pat : Core.APattern) : Option Core.Sym :=
  match pat.pat with
  | .base sym _ => sym
  | _ => none

/-- Check if a pexpr is pure(sym) for some symbol -/
def isPureSym (pe : Core.APexpr) : Option Core.Sym :=
  match pe.expr with
  | .sym s => some s
  | _ => none

/-- Check if an expr is Epure(sym) for some symbol -/
def isExprPureSym (e : Core.AExpr) : Option Core.Sym :=
  match e.expr with
  | .pure pe => isPureSym pe
  | _ => none

/-- Resolve a symbol through the alias chain to find the original parameter (if any).
    Only follows a few levels of aliasing to avoid termination issues. -/
def resolveToParam (aliases : AliasMap) (paramIds : List Nat) (symId : Nat) : Option Nat :=
  -- First check if symId is directly a parameter
  if paramIds.contains symId then
    some symId
  else
    -- Otherwise check if it's an alias to a parameter (one level)
    match aliases.get? symId with
    | some targetId =>
      if paramIds.contains targetId then some targetId
      else
        -- Try one more level of aliasing
        match aliases.get? targetId with
        | some targetId2 => if paramIds.contains targetId2 then some targetId2 else none
        | none => none
    | none => none

/-! ## Alias Scanning

We scan the function body to find all aliases of parameter symbols.
This lets us handle patterns like:
  let a_530 = pure(p)
  ...
  load(T, a_530)  -- a_530 is an alias of p
-/

/-- Scan an expression for alias bindings (let x = pure(p) patterns).
    Returns a map from alias symbol ID to target symbol ID. -/
partial def scanForAliases
    (paramIds : List Nat)
    (aliases : AliasMap)
    (e : Core.AExpr) : AliasMap :=
  match e.expr with
  | .pure _ => aliases
  | .memop _ _ => aliases
  | .action _ => aliases
  | .case_ _ branches =>
    branches.foldl (fun acc (_, body) => scanForAliases paramIds acc body) aliases
  | .let_ pat e1 e2 =>
    -- Track aliases: if `let x = pure(y)` where y is a param or alias
    let aliases' := tryTrackAlias paramIds aliases (patternBindsSym pat) (isPureSym e1)
    scanForAliases paramIds aliases' e2
  | .if_ _ then_ else_ =>
    let aliases' := scanForAliases paramIds aliases then_
    scanForAliases paramIds aliases' else_
  | .ccall _ _ _ => aliases
  | .proc _ _ => aliases
  | .unseq es => es.foldl (scanForAliases paramIds) aliases
  | .wseq pat e1 e2 | .sseq pat e1 e2 =>
    let aliases' := scanForAliases paramIds aliases e1
    -- Track aliases from wseq/sseq bindings
    let aliases'' := tryTrackAlias paramIds aliases' (patternBindsSym pat) (isExprPureSym e1)
    scanForAliases paramIds aliases'' e2
  | .bound inner => scanForAliases paramIds aliases inner
  | .nd es => es.foldl (scanForAliases paramIds) aliases
  | .save _ _ _ body => scanForAliases paramIds aliases body
  | .run _ _ => aliases
  | .par es => es.foldl (scanForAliases paramIds) aliases
  | .wait _ => aliases
where
  /-- Try to track an alias from a binding pattern -/
  tryTrackAlias (paramIds : List Nat) (acc : AliasMap)
      (boundSymOpt : Option Core.Sym) (srcSymOpt : Option Core.Sym) : AliasMap :=
    match boundSymOpt, srcSymOpt with
    | some boundSym, some srcSym =>
      -- Check if srcSym is a param or resolves to one
      let targetId := (resolveToParam acc paramIds srcSym.id).getD srcSym.id
      if paramIds.contains targetId || acc.contains srcSym.id then
        acc.insert boundSym.id targetId
      else
        acc
    | _, _ => acc

/-! ## Type Conversion -/

/-- Convert Core.BaseType to CN.Types.BaseType.
    Returns none for unsupported types. -/
def tryCoreBaseTypeToCN (bt : Core.BaseType) : Option BaseType :=
  match bt with
  | .unit => some .unit
  | .boolean => some .bool
  | .ctype => some .ctype
  | .object .integer => some .integer
  | .object .pointer => some .loc
  | .object .floating => some .real
  | .object (.struct_ tag) => some (.struct_ tag)
  | .loaded _ => some .loc
  -- Unsupported types
  | .list _ => none
  | .tuple _ => none
  | .object (.array _) => none
  | .object (.union_ _) => none
  | .storable => none

/-! ## Main Function: Check Function With Parameters

This is the main entry point for checking a function with its parameters.
It sets up the lazy muCore transformation by:
1. Scanning for aliases
2. Building the ParamValueMap
3. Running type checking with the mapping in place
-/

/-- Check a function with parameters using lazy muCore transformation.

    For each pointer parameter:
    1. Create a fresh value symbol representing the parameter value
    2. Map the stack slot symbol (and its aliases) to this value
    3. When loads from these symbols are encountered, return the value directly

    This corresponds to CN's make_function_args in core_to_mucore.ml lines 745-786.

    The spec's parameter names (e.g., `p` in `Owned<int>(p)`) refer to the
    parameter VALUES, which is what this transformation achieves. -/
def checkFunctionWithParams
    (spec : FunctionSpec)
    (body : Core.AExpr)
    (params : List (Core.Sym × Core.BaseType))
    (loc : Core.Loc)
    : TypeCheckResult :=
  -- For trusted specs, skip verification
  if spec.trusted then
    TypeCheckResult.ok
  else
    -- Step 1: Get parameter IDs and scan for aliases
    let paramIds := params.map (·.1.id)
    let aliases := scanForAliases paramIds {} body

    -- Step 2: Build ParamValueMap and Context
    -- For each pointer parameter, create a value term and add mapping
    let setupResult : Except String (Context × ParamValueMap × Nat) :=
      params.foldlM (init := (Context.empty, ({} : ParamValueMap), 0)) fun (ctx, pvm, nextId) (sym, bt) =>
        match bt with
        | .object .pointer =>
          -- Pointer parameter: create value term and add to mapping
          -- The value term represents the loaded value (the pointer the caller passed)
          match tryCoreBaseTypeToCN bt with
          | some cnBt =>
            -- Create a fresh symbol for the parameter value
            let valueSym : Core.Sym := { id := nextId, name := sym.name.map (· ++ "_val") }
            let valueTerm : IndexTerm := AnnotTerm.mk (.sym valueSym) cnBt loc

            -- Map the stack slot to the value term
            let pvm' := pvm.insert sym.id valueTerm

            -- Also map all aliases of this parameter
            let pvm'' := aliases.fold (init := pvm') fun acc aliasId targetId =>
              if targetId == sym.id then acc.insert aliasId valueTerm else acc

            -- Add the parameter to the computational context
            -- The parameter name in the context refers to the VALUE (the pointer)
            let ctx' := ctx.addA sym cnBt ⟨loc, s!"parameter {sym.name.getD ""}"⟩

            Except.ok (ctx', pvm'', nextId + 1)
          | none =>
            Except.error s!"Unsupported parameter type for {sym.name.getD "<unknown>"}: {repr bt}"
        | _ =>
          -- Non-pointer parameter: simple binding, no mapping needed
          match tryCoreBaseTypeToCN bt with
          | some cnBt =>
            let ctx' := ctx.addA sym cnBt ⟨loc, s!"parameter {sym.name.getD ""}"⟩
            Except.ok (ctx', pvm, nextId)
          | none =>
            Except.error s!"Unsupported parameter type for {sym.name.getD "<unknown>"}: {repr bt}"

    match setupResult with
    | .error msg =>
      TypeCheckResult.fail msg
    | .ok (paramCtx, paramValueMap, nextFreshId) =>
      -- Step 3: Initial context (resources will be added by processPrecondition)
      let initialCtx := paramCtx

      -- Step 4: Create initial state with ParamValueMap and obligation accumulation
      let initialState : TypingState := {
        context := initialCtx
        oracle := .trivial  -- Not used when accumulating obligations
        freshCounter := nextFreshId
        paramValues := paramValueMap
        accumulateObligations := true
      }

      -- Step 5: Run type checking (CPS style)
      let computation : TypingM Unit := do
        -- Process precondition: add resources to context, bind outputs
        processPrecondition spec.requires loc

        -- Check the body with a continuation that handles postcondition
        -- The continuation is called at each exit point of the function
        let postconditionK (returnVal : IndexTerm) : TypingM Unit := do
          -- Bind 'return' to the actual return value
          -- This allows postconditions to refer to the function's return value
          let returnSym : Sym := { id := 999999, name := some "return" }
          TypingM.addAValue returnSym returnVal loc "function return value"

          -- Add the constraint `return = returnVal` to the context
          -- This is crucial for SMT to know what 'return' equals
          let returnTerm := AnnotTerm.mk (.sym returnSym) returnVal.bt loc
          let eqConstraint := AnnotTerm.mk (.binop .eq returnTerm returnVal) .bool loc
          TypingM.addC (.t eqConstraint)

          -- Process postcondition: consume final resources, generate obligations
          processPostcondition spec.ensures loc
          -- Check no resources leaked (must all be consumed or returned)
          checkNoLeakedResources

        checkExprK body postconditionK

      match TypingM.run computation initialState with
      | .ok (_, finalState) =>
        TypeCheckResult.okWithObligations finalState.obligations
      | .error err =>
        TypeCheckResult.fail (toString err)

end CerbLean.CN.TypeChecking
