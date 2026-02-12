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
import CerbLean.Core.Ctype
import CerbLean.Core.MuCore
import CerbLean.CN.Types
import CerbLean.CN.TypeChecking.Check
import CerbLean.CN.TypeChecking.Expr
import CerbLean.CN.TypeChecking.Resolve
import CerbLean.CN.Verification.Obligation
import Std.Data.HashMap

namespace CerbLean.CN.TypeChecking

open CerbLean.Core.MuCore (transformProc)

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
  | .annot _ inner => scanForAliases paramIds aliases inner
  | .excluded _ _ => aliases
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

/-- Convert C type (Ctype) to CN base type.
    This gives the actual VALUE type, not the stack slot pointer type.
    Uses Bits types for integers to match CN's bt_of_sct.
    Corresponds to: Memory.bt_of_sct in CN's memory.ml -/
def tryCtypeToCN (ct : Core.Ctype) : Option BaseType :=
  -- Use the same logic as Resolve.ctypeToOutputBaseType
  some (Resolve.ctypeToOutputBaseType ct)

/-! ## Main Function: Check Function With Parameters

This is the main entry point for checking a function with its parameters.
It sets up the lazy muCore transformation by:
1. Scanning for aliases
2. Building the ParamValueMap
3. Running type checking with the mapping in place
-/

/-- Check a function with parameters using lazy muCore transformation.

    For each parameter:
    1. Create a value term representing the parameter value
    2. Map the stack slot symbol (and its aliases) to this value
    3. When loads from these symbols are encountered, return the value directly

    This corresponds to CN's make_function_args in core_to_mucore.ml lines 745-786.

    The spec's parameter names (e.g., `p` in `Owned<int>(p)`) refer to the
    parameter VALUES, which is what this transformation achieves.

    Parameters:
    - `spec`: The CN specification for the function
    - `body`: The Core IR body of the function
    - `params`: Core parameters (sym × BaseType), where BaseType is always pointer (stack slot)
    - `cParams`: C-level parameter types from funinfo (sym × Ctype), giving actual value types
    - `retTy`: Core return type of the function
    - `loc`: Source location for error reporting

    Corresponds to: WProc.check_procedure in wellTyped.ml lines 2467-2520 -/
def checkFunctionWithParams
    (spec : FunctionSpec)
    (body : Core.AExpr)
    (params : List (Core.Sym × Core.BaseType))
    (cParams : List (Option Core.Sym × Core.Ctype))
    (retTy : Core.BaseType)
    (cRetTy : Option Core.Ctype := none)
    (loc : Core.Loc)
    (functionSpecs : FunctionSpecMap := {})
    (funInfoMap : Core.FunInfoMap := {})
    (tagDefs : Core.TagDefs := [])
    : IO TypeCheckResult := do
  -- For trusted specs, skip verification
  if spec.trusted then
    return TypeCheckResult.ok
  else
    -- Step 1: Get parameter IDs and scan for aliases
    let paramIds := params.map (·.1.id)
    let aliases := scanForAliases paramIds {} body

    -- Step 2: Build ParamValueMap and Context
    -- We use Core params for symbol IDs and C params for value types.
    -- In Core, all parameters are stack slot pointers. In CN, parameters are direct values.
    -- The C type tells us what type the VALUE has (e.g., int, not pointer-to-stack-slot).
    --
    -- Fresh ID strategy (matching CN's approach):
    -- CN uses a global counter for fresh IDs that never collides with Cerberus IDs.
    -- We compute the max param ID and start our fresh counter from there.
    -- This ensures fresh symbols (like `return`) get unique IDs.
    let maxParamId := params.foldl (init := 0) fun acc (sym, _) => max acc sym.id
    let initialFreshId := maxParamId + 1

    let setupResult : Except String (Context × ParamValueMap × Nat × List (Sym × BaseType) × List (String × Core.Ctype)) :=
      params.zip cParams |>.foldlM
        (init := (Context.empty, ({} : ParamValueMap), initialFreshId, [], []))
        fun (ctx, pvm, nextId, cnParamAcc, cTypeAcc) ((coreSym, _coreBt), (_, ctype)) =>
          -- Use C type to get the actual value type
          match tryCtypeToCN ctype with
          | some cnBt =>
            -- Create value term using the SAME symbol as the Core parameter.
            -- This ensures that when the spec refers to `x`, it matches the
            -- value we return when loading from x's stack slot.
            -- The key insight: CN's name resolution gives spec identifiers
            -- the Core parameter's symbol ID, and we use that same ID here.
            let valueTerm : IndexTerm := AnnotTerm.mk (.sym coreSym) cnBt loc

            -- Map the stack slot to the value term
            let pvm' := pvm.insert coreSym.id valueTerm

            -- Also map all aliases of this parameter
            let pvm'' := aliases.fold (init := pvm') fun acc aliasId targetId =>
              if targetId == coreSym.id then acc.insert aliasId valueTerm else acc

            -- Add the parameter to the computational context
            -- The parameter name in the context refers to the VALUE
            let ctx' := ctx.addA coreSym cnBt ⟨loc, s!"parameter {coreSym.name.getD ""}"⟩

            -- Accumulate CN-level params for resolution (using coreSym for ID, cnBt for type)
            let cnParamAcc' := (coreSym, cnBt) :: cnParamAcc

            -- Accumulate C types for pointer arithmetic elaboration
            let cTypeAcc' := match coreSym.name with
              | some name => (name, ctype) :: cTypeAcc
              | none => cTypeAcc

            Except.ok (ctx', pvm'', nextId, cnParamAcc', cTypeAcc')
          | none =>
            Except.error s!"Unsupported parameter type for {coreSym.name.getD "<unknown>"}: {repr ctype}"

    match setupResult with
    | .error msg =>
      return TypeCheckResult.fail msg
    | .ok (paramCtx, paramValueMap, nextFreshId, cnParams, paramCTypes) =>
      -- Step 3: Convert return type to CN BaseType
      -- Corresponds to: WProc extracting return_bt from function type
      -- Prefer C return type (gives Bits types) over Core return type (gives unbounded Integer)
      let returnBtResult : Except String BaseType := match cRetTy with
        | some ct => .ok (Resolve.ctypeToOutputBaseType ct)
        | none =>
          -- Fall back to Core return type if C type not available
          match tryCoreBaseTypeToCN retTy with
          | some bt => .ok bt
          | none => .error s!"Unsupported return type: {repr retTy}"
      match returnBtResult with
      | .error msg => return TypeCheckResult.fail msg
      | .ok returnBt =>

      -- Step 4: Transform body to muCore form
      -- This extracts label definitions and replaces Esave with Erun.
      -- Corresponds to: core_to_micore__funmap_decl in milicore.ml
      let muProc := transformProc body

      -- Step 5: Resolve the spec - convert parsed identifiers to proper symbols
      -- This is the CN-matching approach: resolve names to symbols before type checking.
      -- Corresponds to: CN's Cabs_to_ail.desugar_cn_* functions
      -- Pass return type so 'return' symbol gets the correct type
      let resolveResult := (Resolve.resolveFunctionSpec spec cnParams.reverse returnBt nextFreshId paramCTypes tagDefs).mapError fun e =>
        match e with
        | .symbolNotFound name => s!"Symbol not found: {name}"
        | .integerTooLarge n => s!"Integer too large for any CN type: {n}"
        | .unknownPointeeType msg => s!"Pointer arithmetic error: {msg}"
        | .other msg => s!"Resolution error: {msg}"
      match resolveResult with
      | .error msg => return TypeCheckResult.fail msg
      | .ok resolvedSpec =>
      -- Step 6: Create label context from label definitions
      -- Corresponds to: WProc.label_context in wellTyped.ml line 2474
      -- Maps each label symbol to its type (LT) and kind (return, loop, other)
      let labels := LabelContext.ofLabelDefs resolvedSpec returnBt muProc.labels

      -- Step 7: Initial context (resources will be added by processPrecondition)
      let initialCtx := paramCtx

      -- Step 8: Initialize inline solver (managed at IO level)
      -- The preamble includes pointer datatype and struct declarations.
      -- Corresponds to: init_solver in typing.ml + Solver.make → declare_solver_basics
      let structPreamble := CerbLean.CN.Verification.SmtLib.generateStructPreamble
        { tagDefs := tagDefs : CerbLean.Memory.TypeEnv }
      let preamble := CerbLean.CN.Verification.SmtLib.pointerPreamble ++ structPreamble
      let solverChild ← try
        let proc ← IO.Process.spawn {
          cmd := "z3"
          args := #["-in", "-smt2"]
          stdin := .piped
          stdout := .piped
          stderr := .piped
        }
        proc.stdin.putStr preamble
        proc.stdin.flush
        pure (some proc)
      catch _ => pure none

      -- Step 9: Create initial state with ParamValueMap, LabelDefs, solver, and obligations
      let initialState : TypingState := {
        context := initialCtx
        freshCounter := nextFreshId + 1000  -- Leave room for resolution IDs
        paramValues := paramValueMap
        labelDefs := muProc.labels  -- Label definitions from transformation
        functionSpecs := functionSpecs  -- Pre-built function types for ccall
        funInfoMap := funInfoMap  -- C-level function signatures for cfunction/params_length
        tagDefs := tagDefs  -- Struct/union definitions for resource unpacking
        solverStdin := solverChild.map (·.stdin)    -- Inline solver for provable queries (H5)
        solverStdout := solverChild.map (·.stdout)
      }

      -- Step 10: Run type checking on transformed body
      -- Corresponds to: check_expr_top in check.ml lines 2317-2330
      let computation : TypingM Unit := do
        -- Process precondition: add resources to context, bind outputs
        processPrecondition resolvedSpec.requires loc

        -- Check the body using check_expr_top
        -- This handles return labels via Spine.calltype_lt and
        -- fallthrough via Spine.subtype (for void functions)
        checkExprTop loc labels resolvedSpec returnBt muProc.body

      let result ← TypingM.run computation initialState

      -- Cleanup solver at IO level (regardless of success/failure)
      if let some proc := solverChild then
        try
          proc.stdin.putStr "(exit)\n"
          proc.stdin.flush
          let _ ← proc.wait
        catch _ => pure ()

      match result with
      | .ok (_, finalState) =>
        -- Convert conditional failures to (Obligation, errorString) pairs
        let cfs := finalState.conditionalFailures.map fun cf =>
          (cf.obligation, toString cf.originalError)
        return TypeCheckResult.okWithAll finalState.obligations cfs
      | .error err =>
        return TypeCheckResult.fail (toString err)

end CerbLean.CN.TypeChecking
