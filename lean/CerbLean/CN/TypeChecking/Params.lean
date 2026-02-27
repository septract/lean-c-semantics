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
import CerbLean.CN.Parser
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

/-! ## Loop Label Type Building

Build proper label types for loop labels. Each loop label needs:
1. Computational args with Loc type (pointers to stack slots)
2. Owned<T> resource for each arg (matches what Create+Store produced)
3. Constraint clauses from the loop invariant

Corresponds to: make_label_args in core_to_mucore.ml lines 697-742
-/

/-- Extract cerb::magic text from a LoopAttribute's attributes.
    Corresponds to: get_cerb_magic_attr in annot.lem -/
private def getLoopMagicText (la : Core.LoopAttribute) : List String :=
  la.attributes.attrs.foldl (init := []) fun acc attr =>
    match attr.ns, attr.id with
    | some "cerb", "magic" => acc ++ attr.args.map (·.arg)
    | _, _ => acc

/-- Parse invariant constraints from a magic text string.
    The format is: " inv expr1; expr2; expr3; "
    Returns parsed constraint AnnotTerms. -/
private def parseInvariantConstraints (text : String) : Except String (List AnnotTerm) := do
  -- Strip leading whitespace and "inv" keyword
  let text := text.trim
  let text := if text.startsWith "inv " then text.drop 4
              else if text.startsWith "inv\n" then text.drop 4
              else text
  -- Split on semicolons and parse each constraint
  let parts := text.splitOn ";"
  parts.foldlM (init := []) fun acc part =>
    let part := part.trim
    if part.isEmpty then pure acc
    else match CN.Parser.runParser CN.Parser.expr part with
      | .ok term => pure (acc ++ [term])
      | .error e => .error s!"failed to parse invariant expression '{part}': {e}"

/-- Build an Owned<ct>(Init) resource request for a pointer.
    Corresponds to: Translate.ownership in core_to_mucore.ml line 713 -/
private def mkOwnedRequest (ct : Core.Ctype) (ptrTerm : AnnotTerm) : Request :=
  .p { name := .owned (some ct) .init, pointer := ptrTerm, iargs := [] }

/-- Build a pre-built loop label type for a single loop label.
    Corresponds to: make_label_args in core_to_mucore.ml lines 697-742

    The label type has:
    - Computational args (one per loop variable, type = Loc)
    - LAT with Owned resources (one per loop variable)
    - LAT with invariant constraints (from the loop annotation)
    - Terminal LAT.I False_.false_

    Parameters:
    - info: The label definition info (params, annotations)
    - loopAttributes: Loop attributes from the Core File
    - saveArgCTypes: C types for save args from the parser
    - symId: The label's symbol ID
    - resolveCtx: Context for resolving invariant expression symbols -/
private def buildLoopLabelType
    (info : Core.MuCore.LabelInfo)
    (loopAttributes : Core.LoopAttributes)
    (saveArgCTypes : List (Nat × List (Option Core.Sym × Core.Ctype)))
    (symId : Nat)
    (resolveCtx : Resolve.ResolveContext)
    : Except String LT := do
  -- Step 1: Get the loop ID from annotations
  let loopIdOpt := info.annots.findSome? fun
    | .label (.loop id) => some id
    | _ => none

  -- Step 2: Get the C types for the args from saveArgCTypes
  let argCTypes ← match saveArgCTypes.lookup symId with
    | some cts => pure cts
    | none => .error s!"no C types found for loop label {symId}"

  -- Step 3: Get invariant text from loop_attributes
  let invariantTexts := match loopIdOpt with
    | some loopId =>
      match loopAttributes.lookup loopId with
      | some la => getLoopMagicText la
      | none => []
    | none => []

  -- Step 4: Parse and resolve invariant constraints
  -- Pre-compute output symbols for each loop variable. These correspond to the
  -- loaded values that resource consumption will bind (not the pointer symbols).
  -- Constraints reference these output symbols, matching CN's make_label_args:
  -- AT { Computational(ptr) { L { Resource(val, Owned(ptr)) { Constraint(val >= 0) } } } }
  let loopVarOutputs := info.params.zip argCTypes |>.map fun ((sym, _bt), (_argSymOpt, ct)) =>
    let outputBt := Resolve.ctypeToOutputBaseType ct
    -- QUALITY: ideally use a proper fresh counter instead of ID offset.
    -- Using large offset to avoid collisions with other symbols.
    let outputSym : Sym := { id := sym.id + 1000000, name := sym.name.map (· ++ "_out") }
    (sym, ct, outputSym, outputBt)

  -- Resolve context maps variable NAMES to their loaded VALUE symbols (output symbols),
  -- not the pointer symbols. This ensures `i <= n` in an invariant refers to the
  -- loaded value of `i`, not the stack slot pointer.
  let loopVarEntries := loopVarOutputs.filterMap fun (sym, _, outputSym, outputBt) =>
    sym.name.map fun name => (name, outputSym, outputBt)
  let extendedCtx := { resolveCtx with
    nameToSymType := resolveCtx.nameToSymType ++ loopVarEntries
  }

  let rawConstraints ← invariantTexts.foldlM (init := []) fun acc text => do
    let parsed ← parseInvariantConstraints text
    pure (acc ++ parsed)

  -- Resolve constraint symbols against the extended resolve context
  let resolvedConstraints ← rawConstraints.mapM fun constraint =>
    match Resolve.resolveAnnotTerm extendedCtx constraint none with
    | .ok resolved => pure resolved
    | .error e => .error s!"failed to resolve invariant constraint: {repr e}"

  -- Step 5: Build the LAT (logical argument type) part
  -- Start with the terminal value
  let baseLat : LAT False_ := LAT.terminalValue

  -- Add invariant constraints
  let latWithConstraints := resolvedConstraints.foldr (init := baseLat) fun constraint acc =>
    .constraint (.t constraint) { loc := info.loc, desc := "loop invariant" } acc

  -- Add Owned resources for each loop variable
  -- Corresponds to: make_label_args ownership in core_to_mucore.ml:712-717
  -- Each loop variable is a pointer to a stack slot with an Owned<ct>(Init) resource
  -- Uses the SAME output symbols as the constraints above.
  let latWithResources := loopVarOutputs.foldr (init := latWithConstraints)
    fun (sym, ct, outputSym, outputBt) acc =>
      let ptrTerm := AnnotTerm.mk (.sym sym) .loc info.loc
      .resource outputSym (mkOwnedRequest ct ptrTerm) outputBt
        { loc := info.loc, desc := s!"loop var {sym.name.getD ""} ownership" } acc

  -- Step 6: Build the AT (argument type) with computational args
  -- Each arg gets type Loc (pointer) matching what Erun passes
  -- Corresponds to: make_label_args Computational ((s, Loc()), ...) in core_to_mucore.ml:736
  pure (info.params.foldr (init := (.L latWithResources : LT)) fun (sym, _bt) acc =>
    .computational sym .loc { loc := info.loc, desc := s!"loop var {sym.name.getD ""}" } acc)

/-- Build loop label types for all loop labels in a function.
    Returns a list of (label_sym_id, label_type) pairs.

    Corresponds to: Loop case in WProc.label_context (wellTyped.ml:2483-2486) -/
private def buildLoopLabelTypes
    (labelDefs : Core.MuCore.LabelDefs)
    (loopAttributes : Core.LoopAttributes)
    (saveArgCTypes : List (Nat × List (Option Core.Sym × Core.Ctype)))
    (resolveCtx : Resolve.ResolveContext)
    : Except String (List (Nat × LT)) :=
  labelDefs.foldlM (init := []) fun acc (symId, labelDef) =>
    match labelDef with
    | .label info =>
      -- Check if this is a loop label
      let isLoop := info.annots.any fun
        | .label (.loop _) => true
        | _ => false
      if isLoop then do
        let lt ← buildLoopLabelType info loopAttributes saveArgCTypes symId resolveCtx
        pure (acc ++ [(symId, lt)])
      else pure acc
    | _ => pure acc

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
    - `maxFileSymId`: Maximum symbol ID across all parsed symbols in the Core file.
      Fresh symbols are generated starting from maxFileSymId + 1 to avoid collisions.
      Corresponds to: CN initializes its fresh counter to max(all_parsed_symbol_ids) + 1.

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
    (loopAttributes : Core.LoopAttributes := [])
    (saveArgCTypes : List (Nat × List (Option Core.Sym × Core.Ctype)) := [])
    (globals : List (Core.Sym × Core.GlobDecl) := [])
    (maxFileSymId : Nat := 0)
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
    -- We use maxFileSymId (max of all parsed symbol IDs in the Core file) to start
    -- our fresh counter, ensuring no collisions with any parsed symbol.
    -- Corresponds to: CN's Sym.fresh_make_uniq initializing counter from max parsed ID.
    let initialFreshId := maxFileSymId + 1

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
      let resolveResult := (Resolve.resolveFunctionSpec spec cnParams.reverse returnBt nextFreshId paramCTypes tagDefs globals).mapError fun e =>
        match e with
        | .symbolNotFound name => s!"Symbol not found: {name}"
        | .integerTooLarge n => s!"Integer too large for any CN type: {n}"
        | .unknownPointeeType msg => s!"Pointer arithmetic error: {msg}"
        | .other msg => s!"Resolution error: {msg}"
      match resolveResult with
      | .error msg => return TypeCheckResult.fail msg
      | .ok resolvedSpec0 =>
      -- Step 5b: Inject `accesses` global resources into the spec.
      -- `accesses g` generates implicit `take g = Owned<T>(&g)` in both requires
      -- and ensures (the function borrows the global's resource).
      -- Corresponds to: CN's handling of `accesses` in core_to_mucore.ml:718-723
      let resolvedSpecResult : Except String _ := resolvedSpec0.resolvedAccesses.foldlM (init := resolvedSpec0) fun spec (globalName, valueSym, globalBt) =>
        match globals.find? (fun (sym, _) => sym.name == some globalName) with
        | some (globalSym, globDecl) =>
          let globalCt := match globDecl with
            | .def_ _ cTy _ => cTy
            | .decl _ cTy => cTy
          let ptrTerm : IndexTerm := AnnotTerm.mk (.sym globalSym) .loc Core.Loc.t.unknown
          let clause : Clause := .resource valueSym {
            request := .p {
              name := .owned (some globalCt) .init
              pointer := ptrTerm
              iargs := []
            }
            output := { value := AnnotTerm.mk (.sym valueSym) globalBt Core.Loc.t.unknown }
          }
          .ok { spec with
            requires := { clauses := clause :: spec.requires.clauses }
            ensures := { clauses := clause :: spec.ensures.clauses }
          }
        | none => .error s!"unknown global '{globalName}' in accesses clause"
      let resolvedSpec ← match resolvedSpecResult with
        | .ok v => pure v
        | .error msg => return TypeCheckResult.fail msg

      -- Step 6: Create label context from label definitions
      -- Corresponds to: WProc.label_context in wellTyped.ml line 2474
      -- Maps each label symbol to its type (LT) and kind (return, loop, other)
      -- Build loop label types using invariant text from loop_attributes and
      -- arg C types from saveArgCTypes.
      -- The resolve context for invariant expressions includes function params
      -- (so invariants can reference `n`, `p`, etc.)
      let loopResolveCtx : Resolve.ResolveContext := {
        nameToSymType := cnParams.reverse.filterMap fun (sym, bt) =>
          sym.name.map fun name => (name, sym, bt)
        nextFreshId := nextFreshId + 500
        tagDefs := tagDefs
      }
      let loopLabelTypes ← match buildLoopLabelTypes muProc.labels loopAttributes saveArgCTypes loopResolveCtx with
        | .ok v => pure v
        | .error msg => return TypeCheckResult.fail msg
      let labels := LabelContext.ofLabelDefs resolvedSpec returnBt muProc.labels loopLabelTypes

      -- Step 7: Initial context (resources will be added by processPrecondition)
      let initialCtx := paramCtx

      -- Step 8: Initialize inline solver (managed at IO level)
      -- The preamble includes pointer datatype and struct declarations.
      -- Corresponds to: init_solver in typing.ml + Solver.make → declare_solver_basics
      let structPreamble ← match CerbLean.CN.Verification.SmtLib.generateStructPreamble
        { tagDefs := tagDefs : CerbLean.Memory.TypeEnv } with
        | .ok s => pure s
        | .error msg => return TypeCheckResult.fail msg
      let preamble := CerbLean.CN.Verification.SmtLib.pointerPreamble ++ structPreamble
      let solverChild ← try
        let proc ← IO.Process.spawn {
          cmd := "cvc5"
          args := #["--quiet", "--incremental", "--lang", "smt"]
          stdin := .piped
          stdout := .piped
          stderr := .piped
        }
        proc.stdin.putStr preamble
        proc.stdin.flush
        pure (some proc)
      catch e =>
        return TypeCheckResult.fail s!"failed to start cvc5 solver: {e}"

      -- Step 9: Create initial state with ParamValueMap, LabelDefs, solver, and obligations
      -- freshCounter starts past all resolve-phase IDs (resolve uses nextFreshId+500 range)
      let initialState : TypingState := {
        context := initialCtx
        freshCounter := nextFreshId + 1000
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
        -- Declare all parameter variables to the inline solver.
        -- Parameters were added to paramCtx directly (not via TypingM.addA which
        -- calls solverDeclare), so we need to declare them explicitly here.
        -- Corresponds to: init_solver declaring function params in typing.ml
        for (sym, btOrVal, _) in initialCtx.computational do
          TypingM.solverDeclare sym btOrVal.bt

        -- Declare ghost parameters as logical variables in the context and solver.
        -- Ghost params are logical-only (cn_ghost) and need to be available for
        -- constraint evaluation in the precondition and postcondition.
        -- Corresponds to: CN's add_logical for ghost params in compile.ml
        for (ghostSym, ghostBt) in resolvedSpec.ghostParams do
          TypingM.addL ghostSym ghostBt loc s!"ghost param {ghostSym.name.getD ""}"

        -- Add global address symbols to computational context so that
        -- `pure(g)` in the function body can resolve the global's address.
        -- The Owned resources are already in the spec clauses (injected in step 5b).
        for (globalName, _, _) in resolvedSpec.resolvedAccesses do
          match globals.find? (fun (sym, _) => sym.name == some globalName) with
          | some (globalSym, _) =>
            TypingM.addA globalSym .loc loc s!"global address {globalName}"
          | none => pure ()

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
