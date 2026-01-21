/-
  Parameter handling for CN type checking.

  In Core IR, function parameters are passed by reference to stack slots.
  This module handles the transformation from Core IR's parameter representation
  to CN's muCore-style where parameters are directly available as values.

  The key transformation:
  - Core IR: parameter `p` is a stack slot address, value obtained via `load(T, p)`
  - CN/muCore: parameter `p` is directly the value

  We scan function bodies to:
  1. Track aliases through `let x = pure(p)` and `wseq`/`sseq` patterns
  2. Extract C types from the first `load(T, p)` operations
  3. Set up implicit resources for parameter stack slots

  This corresponds to CN's core_to_mucore transformation.

  Audited: 2026-01-20 (new file for Issue 20)
-/

import CerbLean.Core
import CerbLean.CN.Types
import CerbLean.CN.TypeChecking.Check
import CerbLean.CN.TypeChecking.Expr
import Std.Data.HashMap

namespace CerbLean.CN.TypeChecking

open CerbLean.Core (Sym Loc)
open CerbLean.CN.Types

/-! ## Type Aliases -/

/-- Mapping from parameter symbol ID to its C type (from first load) -/
abbrev ParamCtypeMap := Std.HashMap Nat Core.Ctype

/-- Mapping from symbol ID to what it aliases (for tracking `let x = pure(p)` patterns) -/
abbrev AliasMap := Std.HashMap Nat Nat

/-- State for scanning: tracks both C types found and aliases -/
structure ScanState where
  ctypes : ParamCtypeMap
  aliases : AliasMap
  deriving Inhabited

/-! ## Helper Functions -/

/-- Extract Ctype from an APexpr that should contain a Ctype value.
    The expression should be `PEval (Vctype ct)`. -/
def extractCtypeFromExpr (e : Core.APexpr) : Option Core.Ctype :=
  match e.expr with
  | .val (.ctype ct) => some ct
  | _ => none

/-- Resolve a symbol through the alias chain to find the original parameter (if any).
    Only follows two levels of aliasing to avoid termination issues. -/
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

/-- Try to track an alias from a let binding.
    If we have `let x = pure(y)` where y is a parameter (or alias thereof),
    record x as an alias for y. -/
def tryTrackAlias (paramIds : List Nat) (acc : ScanState)
    (boundSymOpt : Option Core.Sym) (srcSymOpt : Option Core.Sym) : ScanState :=
  match boundSymOpt, srcSymOpt with
  | some boundSym, some srcSym =>
    -- Check if srcSym is a param or resolves to one
    let targetId := (resolveToParam acc.aliases paramIds srcSym.id).getD srcSym.id
    if paramIds.contains targetId || acc.aliases.contains srcSym.id then
      { acc with aliases := acc.aliases.insert boundSym.id targetId }
    else
      acc
  | _, _ => acc

/-! ## Scanning Functions -/

/-- Scan a Pexpr for loads from parameter symbols, accumulating C types.
    We only record the FIRST load from each parameter.
    Also tracks aliasing through `pure(p)` patterns. -/
partial def scanPexprForParamLoads
    (paramIds : List Nat)
    (acc : ScanState)
    (e : Core.Pexpr) : ScanState :=
  match e with
  | .sym _ => acc
  | .impl _ => acc
  | .val _ => acc
  | .undef _ _ => acc
  | .error _ inner => scanPexprForParamLoads paramIds acc inner
  | .ctor _ args => args.foldl (scanPexprForParamLoads paramIds) acc
  | .case_ scrut branches =>
    let acc := scanPexprForParamLoads paramIds acc scrut
    branches.foldl (fun a (_, body) => scanPexprForParamLoads paramIds a body) acc
  | .arrayShift ptr _ idx =>
    let acc := scanPexprForParamLoads paramIds acc ptr
    scanPexprForParamLoads paramIds acc idx
  | .memberShift ptr _ _ => scanPexprForParamLoads paramIds acc ptr
  | .not_ inner => scanPexprForParamLoads paramIds acc inner
  | .op _ e1 e2 =>
    let acc := scanPexprForParamLoads paramIds acc e1
    scanPexprForParamLoads paramIds acc e2
  | .struct_ _ members => members.foldl (fun a (_, v) => scanPexprForParamLoads paramIds a v) acc
  | .union_ _ _ v => scanPexprForParamLoads paramIds acc v
  | .cfunction inner => scanPexprForParamLoads paramIds acc inner
  | .memberof _ _ inner => scanPexprForParamLoads paramIds acc inner
  | .call _ args => args.foldl (scanPexprForParamLoads paramIds) acc
  | .let_ _ e1 e2 =>
    let acc := scanPexprForParamLoads paramIds acc e1
    scanPexprForParamLoads paramIds acc e2
  | .if_ c t e =>
    let acc := scanPexprForParamLoads paramIds acc c
    let acc := scanPexprForParamLoads paramIds acc t
    scanPexprForParamLoads paramIds acc e
  | .isScalar inner => scanPexprForParamLoads paramIds acc inner
  | .isInteger inner => scanPexprForParamLoads paramIds acc inner
  | .isSigned inner => scanPexprForParamLoads paramIds acc inner
  | .isUnsigned inner => scanPexprForParamLoads paramIds acc inner
  | .areCompatible e1 e2 =>
    let acc := scanPexprForParamLoads paramIds acc e1
    scanPexprForParamLoads paramIds acc e2
  | .convInt _ inner => scanPexprForParamLoads paramIds acc inner
  | .wrapI _ _ e1 e2 =>
    let acc := scanPexprForParamLoads paramIds acc e1
    scanPexprForParamLoads paramIds acc e2
  | .catchExceptionalCondition _ _ e1 e2 =>
    let acc := scanPexprForParamLoads paramIds acc e1
    scanPexprForParamLoads paramIds acc e2
  | .bmcAssume inner => scanPexprForParamLoads paramIds acc inner
  | .pureMemop _ args => args.foldl (scanPexprForParamLoads paramIds) acc
  | .constrained constraints => constraints.foldl (fun a (_, e) => scanPexprForParamLoads paramIds a e) acc

def scanAPexprForParamLoads (paramIds : List Nat) (acc : ScanState) (e : Core.APexpr) : ScanState :=
  scanPexprForParamLoads paramIds acc e.expr

/-- Scan an action for loads from parameter symbols.
    Uses alias tracking to handle `let x = pure(p)` patterns. -/
def scanActionForParamLoads
    (paramIds : List Nat)
    (acc : ScanState)
    (act : Core.Action) : ScanState :=
  match act with
  | .load tyExpr ptrExpr _ =>
    -- Check if ptr resolves to a parameter through aliases
    match ptrExpr.expr with
    | .sym s =>
      match resolveToParam acc.aliases paramIds s.id with
      | some paramId =>
        if !acc.ctypes.contains paramId then
          -- Extract the C type from the type expression
          match extractCtypeFromExpr tyExpr with
          | some ct => { acc with ctypes := acc.ctypes.insert paramId ct }
          | none => acc
        else acc
      | none => acc
    | _ => acc
  | .create _ size _ => scanAPexprForParamLoads paramIds acc size
  | .createReadonly _ size init _ =>
    let acc := scanAPexprForParamLoads paramIds acc size
    scanAPexprForParamLoads paramIds acc init
  | .alloc _ size _ => scanAPexprForParamLoads paramIds acc size
  | .kill _ ptr => scanAPexprForParamLoads paramIds acc ptr
  | .store _ ty ptr val _ =>
    let acc := scanAPexprForParamLoads paramIds acc ty
    let acc := scanAPexprForParamLoads paramIds acc ptr
    scanAPexprForParamLoads paramIds acc val
  | .rmw ty ptr expected desired _ _ =>
    let acc := scanAPexprForParamLoads paramIds acc ty
    let acc := scanAPexprForParamLoads paramIds acc ptr
    let acc := scanAPexprForParamLoads paramIds acc expected
    scanAPexprForParamLoads paramIds acc desired
  | .fence _ => acc
  | .compareExchangeStrong ty ptr expected desired _ _
  | .compareExchangeWeak ty ptr expected desired _ _ =>
    let acc := scanAPexprForParamLoads paramIds acc ty
    let acc := scanAPexprForParamLoads paramIds acc ptr
    let acc := scanAPexprForParamLoads paramIds acc expected
    scanAPexprForParamLoads paramIds acc desired
  | .seqRmw _ ty ptr _ val =>
    let acc := scanAPexprForParamLoads paramIds acc ty
    let acc := scanAPexprForParamLoads paramIds acc ptr
    scanAPexprForParamLoads paramIds acc val

/-- Scan an expression for loads from parameter symbols.
    Tracks aliases through let bindings of pure(param) expressions. -/
partial def scanExprForParamLoads
    (paramIds : List Nat)
    (acc : ScanState)
    (e : Core.AExpr) : ScanState :=
  match e.expr with
  | .pure pe => scanAPexprForParamLoads paramIds acc pe
  | .memop _ args => args.foldl (scanAPexprForParamLoads paramIds) acc
  | .action pact => scanActionForParamLoads paramIds acc pact.action.action
  | .case_ scrut branches =>
    let acc := scanAPexprForParamLoads paramIds acc scrut
    branches.foldl (fun a (_, body) => scanExprForParamLoads paramIds a body) acc
  | .let_ pat e1 e2 =>
    -- Track aliases: if `let x = pure(param)`, then x is an alias for param
    let acc := scanAPexprForParamLoads paramIds acc e1
    let boundSymOpt := patternBindsSym pat
    let srcSymOpt := isPureSym e1
    -- Try to track aliasing if this is `let x = pure(y)` pattern
    let acc := tryTrackAlias paramIds acc boundSymOpt srcSymOpt
    scanExprForParamLoads paramIds acc e2
  | .if_ cond then_ else_ =>
    let acc := scanAPexprForParamLoads paramIds acc cond
    let acc := scanExprForParamLoads paramIds acc then_
    scanExprForParamLoads paramIds acc else_
  | .ccall funPtr funTy args =>
    let acc := scanAPexprForParamLoads paramIds acc funPtr
    let acc := scanAPexprForParamLoads paramIds acc funTy
    args.foldl (scanAPexprForParamLoads paramIds) acc
  | .proc _ args => args.foldl (scanAPexprForParamLoads paramIds) acc
  | .unseq es => es.foldl (scanExprForParamLoads paramIds) acc
  | .wseq pat e1 e2 | .sseq pat e1 e2 =>
    let acc := scanExprForParamLoads paramIds acc e1
    -- Track aliases: if `pat = pure(sym)`, then pattern binds an alias to sym
    let boundSymOpt := patternBindsSym pat
    let srcSymOpt := isExprPureSym e1
    let acc := tryTrackAlias paramIds acc boundSymOpt srcSymOpt
    scanExprForParamLoads paramIds acc e2
  | .bound inner => scanExprForParamLoads paramIds acc inner
  | .nd es => es.foldl (scanExprForParamLoads paramIds) acc
  | .save _ _ args body =>
    let acc := args.foldl (fun a (_, _, e) => scanAPexprForParamLoads paramIds a e) acc
    scanExprForParamLoads paramIds acc body
  | .run _ args => args.foldl (scanAPexprForParamLoads paramIds) acc
  | .par es => es.foldl (scanExprForParamLoads paramIds) acc
  | .wait _ => acc

/-- Extract C types for function parameters by scanning for their first loads.
    Returns a map from parameter symbol ID to C type.

    In Core IR, function parameters are stored in stack slots. The actual
    parameter value is obtained by loading from the slot. We extract the
    C type from these load operations.

    Handles aliasing: tracks `let x = pure(p)` patterns so loads from `x`
    are attributed to parameter `p`. -/
def extractParamCtypes
    (params : List (Core.Sym × Core.BaseType))
    (body : Core.AExpr) : ParamCtypeMap :=
  let paramIds := params.map (·.1.id)
  let initState : ScanState := { ctypes := {}, aliases := {} }
  let result := scanExprForParamLoads paramIds initState body
  -- Debug output
  dbg_trace s!"extractParamCtypes: paramIds={paramIds}, aliases={result.aliases.toList}, ctypes={result.ctypes.toList.map (fun (id, ct) => (id, repr ct.ty))}"
  result.ctypes

/-! ## Type Conversion Functions -/

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
  -- Unsupported types - return none to signal error
  | .list _ => none
  | .tuple _ => none
  | .object (.array _) => none
  | .object (.union_ _) => none
  | .storable => none

/-- Convert Ctype to CN BaseType (for parameter value types).
    Returns the base type of the VALUE, not the storage type. -/
def ctypeToCNBaseType (ct : Core.Ctype) : Option BaseType :=
  match ct.ty with
  | .void => some .unit
  | .basic (.integer _) => some .integer
  | .basic (.floating _) => some .real
  | .pointer _ _ => some .loc
  | .struct_ tag => some (.struct_ tag)
  | .array _ _ => none  -- Arrays not yet supported
  | .union_ _ => none   -- Unions not yet supported
  | .function _ _ _ _ => none
  | .functionNoParams _ _ => none
  | .atomic _ => none
  | .byte => none

/-! ## Term Construction Helpers -/

/-- Create an IndexTerm for a parameter stack slot address -/
def mkParamStackSlotTerm (sym : Core.Sym) (loc : Core.Loc) : IndexTerm :=
  AnnotTerm.mk (.sym sym) .loc loc

/-- Create a fresh symbolic IndexTerm for a parameter value -/
def mkParamValueTerm (sym : Core.Sym) (bt : BaseType) (loc : Core.Loc) (id : Nat) : IndexTerm :=
  -- Use a fresh symbol with a name indicating it's the parameter value
  let valueSym : Core.Sym := { id := id, name := sym.name.map (· ++ "_value") }
  AnnotTerm.mk (.sym valueSym) bt loc

/-! ## Main Function Checking -/

/-- Check a function with parameters bound to the context.

    In Core IR, function parameters are stored in stack slots:
    - Parameter `p` of C type `T` is a stack slot address
    - The actual value is obtained by `load(T, p)`

    For CN verification, we:
    1. Create implicit Owned<T>(p_slot) resources for each parameter's stack slot
    2. Bind spec parameter names to symbolic values representing the loaded values
    3. The spec's constraints then correctly apply to the parameter values

    This corresponds to CN's core_to_mucore transformation. -/
def checkFunctionWithParams
    (spec : FunctionSpec)
    (body : Core.AExpr)
    (params : List (Core.Sym × Core.BaseType))
    (loc : Core.Loc)
    (oracle : ProofOracle := .trivial)
    : TypeCheckResult :=
  -- For trusted specs, skip verification
  if spec.trusted then
    { success := true
    , finalContext := Context.empty
    , error := none }
  else
    -- Extract C types for parameters from their first loads in the body
    let paramCtypes := extractParamCtypes params body

    -- Build initial context and resources for parameters
    -- For each pointer parameter, we need to:
    -- 1. Create implicit Owned<Ctype>(stack_slot) resource
    -- 2. Bind the parameter name to a symbolic value representing the loaded value
    let setupResult : Except String (Context × List Resource × Nat) :=
      params.foldlM (init := (Context.empty, [], 0)) fun (ctx, resources, nextId) (sym, bt) =>
        match bt with
        | .object .pointer =>
          -- Pointer parameter: check if we found its C type from a load
          match paramCtypes.get? sym.id with
          | some ct =>
            -- Found the C type from the body's load operation
            match ctypeToCNBaseType ct with
            | some valueBt =>
              -- Create symbolic value for the parameter (what gets loaded from stack slot)
              let valueId := nextId
              let valueTerm := mkParamValueTerm sym valueBt loc valueId
              let stackSlotTerm := mkParamStackSlotTerm sym loc

              -- Create implicit Owned<Ctype>(stack_slot) resource with the value term
              let pred : Predicate := {
                name := .owned ct .init
                pointer := stackSlotTerm
                iargs := []
              }
              let resource : Resource := {
                request := .p pred
                output := { value := valueTerm }
              }

              -- Bind the parameter name to the VALUE term in the context
              -- This is the key transformation: spec's `p` refers to the loaded value
              let ctx' := ctx.addA sym valueBt ⟨loc, s!"parameter {sym.name.getD ""} (value)"⟩

              Except.ok (ctx', resource :: resources, nextId + 1)
            | none =>
              Except.error s!"Unsupported C type for parameter {sym.name.getD "<unknown>"}: {repr ct}"
          | none =>
            -- No load found for this parameter - might be unused or non-pointer access pattern
            -- Fall back to treating it as a simple pointer
            match tryCoreBaseTypeToCN bt with
            | some cnBt =>
              let ctx' := ctx.addA sym cnBt ⟨loc, s!"parameter {sym.name.getD ""}"⟩
              Except.ok (ctx', resources, nextId)
            | none =>
              Except.error s!"Unsupported parameter type for {sym.name.getD "<unknown>"}: {repr bt}"
        | _ =>
          -- Non-pointer parameter: simple binding
          match tryCoreBaseTypeToCN bt with
          | some cnBt =>
            let ctx' := ctx.addA sym cnBt ⟨loc, s!"parameter {sym.name.getD ""}"⟩
            Except.ok (ctx', resources, nextId)
          | none =>
            Except.error s!"Unsupported parameter type for {sym.name.getD "<unknown>"}: {repr bt}"

    match setupResult with
    | .error msg =>
      { success := false
      , finalContext := Context.empty
      , error := some (.other msg) }
    | .ok (paramCtx, implicitResources, nextFreshId) =>
      -- Combine implicit parameter resources with precondition resources
      let precondResources := extractPreconditionResources spec
      let allInitialResources := implicitResources ++ precondResources

      -- Create initial context with parameters bound and resources
      let initialCtx := { paramCtx with resources := allInitialResources }

      -- Run type checking
      let initialState : TypingState := {
        context := initialCtx
        oracle := oracle
        freshCounter := nextFreshId
      }

      let computation : TypingM Unit := do
        -- 1. Process precondition: consume initial resources, bind outputs
        processPrecondition spec.requires loc

        -- 2. Check the body expression
        let _returnVal ← checkExpr body

        -- 3. Process postcondition: produce final resources
        processPostcondition spec.ensures loc

        -- 4. Verify all accumulated constraints
        verifyConstraints

      match TypingM.run computation initialState with
      | .ok (_, finalState) =>
        { success := true
        , finalContext := finalState.context
        , error := none }
      | .error err =>
        { success := false
        , finalContext := Context.empty
        , error := some err }

end CerbLean.CN.TypeChecking
