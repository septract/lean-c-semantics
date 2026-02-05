/-
  Small-step execution semantics
  Corresponds to: cerberus/frontend/model/core_run.lem (core_thread_step2)

  CRITICAL: This file must match Cerberus semantics EXACTLY.
  Each case is documented with its Cerberus correspondence.
-/

import CerbLean.Semantics.Monad
import CerbLean.Semantics.State
import CerbLean.Semantics.Env
import CerbLean.Semantics.Eval
import CerbLean.Semantics.Context
import CerbLean.Semantics.Race
import CerbLean.Memory.Interface
import Std.Data.HashMap

namespace CerbLean.Semantics

open CerbLean.Core
open CerbLean.Memory
open Std (HashMap)

/-! ## Call Procedure

Corresponds to: call_proc in core_run.lem:30-70
```lem
val call_proc:
  map Symbol.sym Symbol.sym ->
  Core.file core_run_annotation -> Symbol.sym -> list Core.value ->
  Exception.exceptM (map Symbol.sym Core.value * Core.expr core_run_annotation) core_run_cause
let call_proc core_extern file psym cvals =
  ...
  let env = Utils.foldl2 (fun acc (sym, _) cval ->
    Map.insert sym cval acc
  ) Map.empty params cvals in
  Exception.return (env, body)
```
-/

/-- Build symbol remapping from extern field.
    Corresponds to: create_extern_symmap in core_linking.lem:317-325
    For each (decls, lk) entry in file.extern:
    - LK_none: skip
    - LK_tentative def / LK_normal def: map each decl -> def -/
def createExternSymmap (file : File) : HashMap Sym Sym :=
  file.extern.fold (init := {}) fun acc _ (decls, lk) =>
    match lk with
    | .none_ => acc
    | .tentative defSym => decls.foldl (fun acc decl => acc.insert decl defSym) acc
    | .normal defSym => decls.foldl (fun acc decl => acc.insert decl defSym) acc

/-- Look up a procedure and return (resolvedSym, env, body).
    Corresponds to: call_proc in core_run.lem:30-70
    Audited: 2025-01-01, updated 2026-01-16 for extern symbol remapping
    Returns the resolved symbol (for label lookup) along with env and body -/
def callProc (file : File) (psym : Sym) (cvals : List Value)
    : Except InterpError (Sym × HashMap Sym Value × AExpr) := do
  -- Build extern symbol map (matches core_run.lem:42-45)
  let coreExtern := createExternSymmap file
  -- Look up in stdlib first, then funs (matches Cerberus order)
  -- Note: stdlib lookup uses psym directly (core_run.lem:38)
  -- funs lookup uses remapped symbol (core_run.lem:42-46)
  let procOpt : Option (Sym × FunDecl) :=
    match file.stdlib.find? fun (s, _) => s == psym with
    | some x => some x
    | none =>
      let coreSym := coreExtern.get? psym |>.getD psym
      file.funs.find? fun (s, _) => s == coreSym
  match procOpt with
  | some (resolvedSym, .proc _loc _markerEnv _retTy params body) =>
    if params.length != cvals.length then
      throw (.illformedProgram s!"calling procedure '{psym.name}' with wrong number of args")
    -- Build environment: env = foldl2 (fun acc (sym, _) cval -> Map.insert sym cval acc) Map.empty params cvals
    let emptyMap : HashMap Sym Value := {}
    let env := params.zip cvals |>.foldl (fun acc ((sym, _), cval) => acc.insert sym cval) emptyMap
    pure (resolvedSym, env, body)
  | some (_, .fun_ _ _ _) =>
    throw (.illformedProgram s!"call_proc: '{psym.name}' is a fun, not a proc")
  | some (_, .procDecl _ _ _) =>
    -- Function is declared but not defined - typically a libc function that
    -- wasn't linked into the Core IR. Cerberus --exec links libc at runtime,
    -- but --json_core_out doesn't include linked library implementations.
    throw (.illformedProgram s!"cannot call '{psym.name}': declared but not defined (missing libc?)")
  | some (_, .builtinDecl _ _ _) =>
    throw (.illformedProgram s!"call_proc: '{psym.name}' is a builtinDecl (use builtin handler)")
  | none =>
    throw (.illformedProgram s!"calling unknown procedure: '{psym.name}'")

/-! ## Value Extraction

Helpers to check if a pure expression is already a value.
Corresponds to: valueFromPexpr in core_aux.lem
-/

/-- Extract value from a pure expression if it's already evaluated -/
def valueFromPexpr (pe : APexpr) : Option Value :=
  match pe.expr with
  | .val v => some v
  | _ => none

/-- Check if an AExpr is Epure(PEval v) -/
def valueFromExpr (e : AExpr) : Option Value :=
  match e.expr with
  | .pure pe => valueFromPexpr pe
  | _ => none

/-- Extract pure expression from AExpr if it's Epure -/
def toPure (e : AExpr) : Option APexpr :=
  match e.expr with
  | .pure pe => some pe
  | _ => none

/-- Extract all pure expressions from a list if ALL are Epure.
    Corresponds to: to_pures in core_run.lem
    Returns None if any element is not Epure. -/
def toPures (es : List AExpr) : Option (List APexpr) :=
  es.mapM toPure

/-- Make a tuple pure expression from a list of pure expressions.
    Corresponds to: mk_tuple_pe in core_aux.lem -/
def mkTuplePexpr (pes : List APexpr) : APexpr :=
  { annots := [], ty := none, expr := .ctor .tuple (pes.map (·.expr)) }

/-- Make a pure value expression -/
def mkValueExpr (annots : Annots) (v : Value) : AExpr :=
  { annots, expr := .pure { annots := [], ty := none, expr := .val v } }

/-- Extract value and annotations from an irreducible expression.
    Irreducible expressions are either:
    - Epure(PEval v) - plain value
    - Eannot xs (Epure(PEval v)) - annotated value
    Corresponds to: core_reduction.lem:246-261 pattern matching in one_step_unseq_aux -/
def extractValueAndAnnots : AExpr → Option (Value × DynAnnotations)
  | ⟨_, .pure ⟨_, _, .val v⟩⟩ => some (v, [])
  | ⟨_, .annot xs ⟨_, .pure ⟨_, _, .val v⟩⟩⟩ => some (v, xs)
  | _ => none

/-- Collect values from all irreducible expressions, checking for races.
    Returns (values, combined_annotations) or throws UB035 on race.
    Corresponds to: one_step_unseq_aux in core_reduction.lem:244-261
    ```lem
    let rec one_step_unseq_aux annot (cvals_acc, acc_xs) = function
      | [] -> Step_eval annot (Expr [] (Epure (Pexpr [] None (PEctor Ctuple (...)))))
      | Expr _ (Eannot xs (Expr _ (Epure (Pexpr _ _ (PEval cval))))) :: es ->
          if do_race xs acc_xs then Step_ub_race UB_unsequenced_race
          else one_step_unseq_aux annot (cvals_acc ++ [cval], combine_dynamic_annotations xs acc_xs) es
      | Expr _ (Epure (Pexpr _ _ (PEval cval))) :: es ->
          one_step_unseq_aux annot (cvals_acc ++ [cval], acc_xs) es
    ``` -/
def collectValuesCheckRace (es : List AExpr) : Except InterpError (List Value × DynAnnotations) :=
  go [] [] es
where
  go (valsAcc : List Value) (annotsAcc : DynAnnotations) : List AExpr → Except InterpError (List Value × DynAnnotations)
  | [] => .ok (valsAcc, annotsAcc)
  | e :: rest =>
    match extractValueAndAnnots e with
    | some (v, xs) =>
      if doRace xs annotsAcc then
        .error (.undefinedBehavior .ub035_unsequencedRace none)
      else
        go (valsAcc ++ [v]) (combineDynAnnotations xs annotsAcc) rest
    | none => .error (.illformedProgram "unseq: expected irreducible expression")

/-- Make an annotated value expression with dynamic annotations.
    Used for memory operations that need to track footprints.
    Corresponds to: core_reduction.lem:689-698 (store), 724-734 (load)
    Creates: Expr [] (Eannot [DA_pos [] fp] (mk_value_e cval)) -/
def mkAnnotatedValueExpr (annots : Annots) (dynAnnots : DynAnnotations) (v : Value) : AExpr :=
  let innerExpr := mkValueExpr [] v
  { annots, expr := .annot dynAnnots innerExpr }

/-! ## Expression Builders for Neg Action Transformation

These helpers are used to construct the transformed expression when a neg action
is encountered. The transformation creates:
  wseq sym = unseq [Eexcluded n act; apply_ctx ctxA' (pure ())] in sym

Corresponds to: core_reduction.lem:1285-1302 neg action transformation
-/

/-- Create an Eexcluded wrapper around an action.
    Corresponds to: Eexcluded in core.lem:337 -/
def mkExcludedExpr (exclId : Nat) (paction : Paction) : AExpr :=
  { annots := [], expr := .excluded exclId paction }

/-- Create a pure unit expression.
    Used as the base expression when applying context. -/
def mkPureUnit : AExpr :=
  { annots := [], expr := .pure { annots := [], ty := some .unit, expr := .val .unit } }

/-- Create an unseq expression from a list of expressions. -/
def mkUnseqExpr (es : List AExpr) : AExpr :=
  { annots := [], expr := .unseq es }

/-- Create a wseq expression for neg transform: let weak (_, sym) = e1 in e2
    The pattern is a tuple to match the unseq result: [ignored_result, sym_result]
    Corresponds to: Caux.mk_tuple_pat [mk_empty_pat BTy_unit, mk_sym_pat sym BTy_unit]
    in core_reduction.lem:1296-1297 -/
def mkWseqExpr (sym : Sym) (e1 : AExpr) (e2 : AExpr) : AExpr :=
  -- Pattern: (_, sym) - ignore first element, bind second to sym
  let emptyPat : Pattern := .base none .unit
  let symPat : Pattern := .base (some sym) .unit
  let tuplePat : APattern := { annots := [], pat := .ctor .tuple [emptyPat, symPat] }
  { annots := [], expr := .wseq tuplePat e1 e2 }

/-- Create a pure symbol reference expression. -/
def mkPureSym (sym : Sym) : AExpr :=
  { annots := [], expr := .pure { annots := [], ty := none, expr := .sym sym } }

/-- Create an sseq expression: let strong pat = e1 in e2
    Corresponds to: Caux.mk_sseq_e in core_aux.lem -/
def mkSseqExpr (pat : APattern) (e1 : AExpr) (e2 : AExpr) : AExpr :=
  { annots := [], expr := .sseq pat e1 e2 }

/-- Create a tuple pattern: (pat1, pat2)
    Corresponds to: Caux.mk_tuple_pat [pat1, pat2] in core_aux.lem -/
def mkTuplePat (pats : List Pattern) : APattern :=
  { annots := [], pat := .ctor .tuple pats }

/-- Create an sseq expression for BOUND_WITH_SSEQ with non-empty ctxB:
    let strong (_, sseq_pat) = e1 in e2
    The pattern is a tuple to match the unseq result: [ignored_result, original_result]
    Corresponds to: core_reduction.lem:1317-1318 -/
def mkSseqTupleExpr (sseqPat : APattern) (e1 : AExpr) (e2 : AExpr) : AExpr :=
  -- Pattern: (_, sseq_pat) - ignore first element (unit from excluded action),
  -- bind second to sseq_pat
  let emptyPat : Pattern := .base none .unit
  let tuplePat : APattern := mkTuplePat [emptyPat, sseqPat.pat]
  mkSseqExpr tuplePat e1 e2

/-- Convert a Paction from Neg to Pos polarity.
    Corresponds to: Eaction (Paction Pos act) in core_reduction.lem:1307-1308 -/
def mkPosActionExpr (paction : Paction) : AExpr :=
  { annots := [], expr := .action { paction with polarity := .pos } }

/-- Convert a continuation to a Context type for use with applyCtx.
    This inverts the continuation (which is inside-out) to create
    a context (which is outside-in).
    Corresponds to: the relationship between Continuation and Context in Cerberus -/
def contToContext (cont : Continuation) : Context :=
  cont.foldl (init := Context.ctx) fun acc elem =>
    match elem with
    | .wseq annots pat e2 => Context.wseq annots pat acc e2
    | .sseq annots pat e2 => Context.sseq annots pat acc e2
    | .unseq annots done remaining => Context.unseq annots done acc remaining
    | .annot annots dynAnnots => Context.annot_ annots dynAnnots acc
    | .bound annots => Context.bound annots acc

/-- Convert a Context to a list of ContElems (continuation).
    Flattens the nested context structure into a flat continuation.
    The innermost context becomes the first element (closest to the hole).
    Corresponds to: converting Cerberus evaluation contexts to continuation elements -/
def contextToContElems : Context → List ContElem
  | .ctx => []
  | .unseq annots before inner after =>
      -- Innermost first, so recurse then append this element
      contextToContElems inner ++ [.unseq annots before after]
  | .wseq annots pat inner e2 =>
      contextToContElems inner ++ [.wseq annots pat e2]
  | .sseq annots pat inner e2 =>
      contextToContElems inner ++ [.sseq annots pat e2]
  | .annot_ annots dynAnnots inner =>
      contextToContElems inner ++ [.annot annots dynAnnots]
  | .bound annots inner =>
      contextToContElems inner ++ [.bound annots]

/-! ## Value Conversion Helpers

See Eval.lean for memValueFromValue and valueFromMemValue.
These are defined there because they're needed for struct/union construction
during pure expression evaluation (matching core_aux.lem:114-200).
-/

/-! ## Single Step Execution

Corresponds to: core_thread_step2 in core_run.lem:~750-1655

The step function takes a ThreadState and returns a StepResult.
Each case matches the corresponding case in Cerberus.
-/

/-- Single step of execution.
    Corresponds to: core_thread_step2 in core_run.lem
    Audited: 2025-01-01 (partial - main cases only)
    Deviations:
    - No PEconstrained handling (for bounded model checking)
    - No core_extern handling (external symbol remapping)
    - Simplified memory action handling -/
def step (st : ThreadState) (file : File) (allLabeledConts : HashMap Sym LabeledConts)
    : InterpM StepResult := do
  let arena := st.arena
  let arenaAnnots := arena.annots

  match arena.expr, st.stack with
  -- Epure(PEval cval) with empty stack -> done
  -- Corresponds to: core_run.lem:1540-1542
  | .pure pe, .empty =>
    match valueFromPexpr pe with
    | some cval => pure (.done cval)
    | none =>
      -- Need to evaluate the pure expression
      let cval ← evalPexpr defaultPexprFuel st.env pe
      pure (.continue_ { st with arena := mkValueExpr arenaAnnots cval })

  -- Epure(PEval cval) with non-empty stack
  -- Corresponds to: core_run.lem:1556-1616
  | .pure pe, .cons currentProcOpt cont parent =>
    match valueFromPexpr pe with
    | some cval =>
      match cont, parent with
      -- Empty continuation, empty parent -> done (end of execution)
      -- Corresponds to: core_run.lem:1564-1572
      | [], .empty =>
        pure (.done cval)

      -- Empty continuation, non-empty parent -> end of procedure, pop env
      -- Corresponds to: core_run.lem:1573-1598
      | [], .cons parentProcOpt parentCont parentStack =>
        -- Pop the environment scope
        let env' := match st.env with
          | [] => [{}]  -- Should not happen
          | _ :: rest => if rest.isEmpty then [{}] else rest
        -- Continue with parent's continuation (value passes to parent frame)
        pure (.continue_ { st with
          arena := mkValueExpr arenaAnnots cval
          stack := .cons parentProcOpt parentCont parentStack
          env := env'
        })

      -- Non-empty continuation -> handle ONE element at a time
      -- This avoids rebuilding the entire expression (which caused infinite loops with bounds)
      -- Corresponds to: core_reduction.lem reduction rules for values in contexts
      | elem :: rest, _ =>
        match elem with
        | .wseq _annots pat e2 =>
            -- Bind value to pattern, continue with e2
            match st.updateEnv pat cval with
            | some st' => pure (.continue_ { st' with arena := e2, stack := .cons currentProcOpt rest parent })
            | none => throw .patternMatchFailed
        | .sseq _annots pat e2 =>
            -- Same as wseq (strong vs weak doesn't matter for values)
            match st.updateEnv pat cval with
            | some st' => pure (.continue_ { st' with arena := e2, stack := .cons currentProcOpt rest parent })
            | none => throw .patternMatchFailed
        | .unseq annots done remaining =>
            -- Add value to done list, continue with remaining or complete
            let newDone := done ++ [mkValueExpr arenaAnnots cval]
            match remaining with
            | [] =>
                -- All branches done: rebuild unseq with all values and continue
                -- The unseq case in the stepper will then check for races
                let unseqExpr : AExpr := { annots, expr := .unseq newDone }
                pure (.continue_ { st with arena := unseqExpr, stack := .cons currentProcOpt rest parent })
            | next :: moreRemaining =>
                -- More branches to evaluate
                let newElem := ContElem.unseq annots newDone moreRemaining
                pure (.continue_ { st with arena := next, stack := .cons currentProcOpt (newElem :: rest) parent })
        | .bound _ =>
            -- CRITICAL: bound(v) → v (pass value through, matching Cerberus core_reduction.lem)
            -- The bound is consumed - we don't rebuild Ebound around the value
            pure (.continue_ { st with arena := mkValueExpr arenaAnnots cval, stack := .cons currentProcOpt rest parent })
        | .annot annots dynAnnots =>
            -- Wrap value in annotation
            let annotatedExpr := mkAnnotatedValueExpr annots dynAnnots cval
            pure (.continue_ { st with arena := annotatedExpr, stack := .cons currentProcOpt rest parent })

    | none =>
      -- Need to evaluate the pure expression
      let cval ← evalPexpr defaultPexprFuel st.env pe
      pure (.continue_ { st with arena := mkValueExpr arenaAnnots cval })

  -- Elet pat pe1 e2: evaluate pe1, bind pattern, continue with e2
  -- Corresponds to: core_run.lem:837-865
  | .let_ pat pe1 e2, _ =>
    let cval ← evalPexpr defaultPexprFuel st.env pe1
    match st.updateEnv pat cval with
    | some st' => pure (.continue_ { st' with arena := e2 })
    | none => throw .patternMatchFailed

  -- Eif: evaluate condition and branch
  -- Corresponds to: core_run.lem:870-924
  | .if_ cond then_ else_, .cons _ _ _ =>
    let condVal ← evalPexpr defaultPexprFuel st.env cond
    match condVal with
    | .true_ => pure (.continue_ { st with arena := then_ })
    | .false_ => pure (.continue_ { st with arena := else_ })
    | _ => throw (.typeError "if condition must be boolean")

  | .if_ _ _ _, .empty =>
    throw (.illformedProgram "reached empty stack with Eif")

  -- Ecase: evaluate scrutinee and match branches
  -- Corresponds to: core_run.lem:785-835
  | .case_ scrut branches, _ =>
    let scrutVal ← evalPexpr defaultPexprFuel st.env scrut
    let rec tryBranches : List (APattern × AExpr) → InterpM StepResult
      | [] => throw .patternMatchFailed
      | (pat, body) :: rest =>
        match matchPattern pat scrutVal with
        | some bindings =>
          let env' := bindAllInEnv bindings st.env
          pure (.continue_ { st with arena := body, env := env' })
        | none => tryBranches rest
    tryBranches branches

  -- Ewseq pat e1 e2: weak sequencing
  -- Corresponds to: core_reduction.lem Ewseq cases
  | .wseq pat e1 e2, .cons currentProcOpt cont parent =>
    match e1.expr with
    -- Case: letw pat = {A}v in e2 --> {A}(letw pat = v in e2)
    -- Corresponds to: core_reduction.lem LETW-ANNOT rule
    -- The annotation propagates to wrap e2
    | .annot xs innerE =>
      match valueFromExpr innerE with
      | some cval =>
        -- {A}v case: propagate annotation to e2
        -- Corresponds to: core_reduction.lem:383-391 LETW-ANNOT rule
        -- letw pat = {A}v in E2 --> {A} { v / pat } E2
        -- NOTE: Cerberus passes xs through unchanged (no neg-to-pos conversion)
        match st.updateEnv pat cval with
        | some st' =>
          let wrappedE2 : AExpr := { annots := [], expr := .annot xs e2 }
          pure (.continue_ { st' with arena := wrappedE2 })
        | none => throw .patternMatchFailed
      | none =>
        match innerE.expr with
        | .pure pe1 =>
          -- {A}(pure e) - evaluate and propagate annotation
          let cval ← evalPexpr defaultPexprFuel st.env pe1
          match st.updateEnv pat cval with
          | some st' =>
            let wrappedE2 : AExpr := { annots := [], expr := .annot xs e2 }
            pure (.continue_ { st' with arena := wrappedE2 })
          | none => throw .patternMatchFailed
        | _ =>
          -- {A}e where e is not a value - focus on e1
          let contElem := ContElem.wseq arenaAnnots pat e2
          pure (.continue_ { st with
            arena := e1
            stack := .cons currentProcOpt (contElem :: cont) parent
          })
    -- Case: letw pat = v in e2 --> e2[v/pat]
    -- Corresponds to: core_reduction.lem LETW-PURE rule
    | .pure pe1 =>
      let cval ← evalPexpr defaultPexprFuel st.env pe1
      match st.updateEnv pat cval with
      | some st' => pure (.continue_ { st' with arena := e2 })
      | none => throw .patternMatchFailed
    | _ =>
      -- e1 not yet a value - focus on e1, push continuation
      let contElem := ContElem.wseq arenaAnnots pat e2
      pure (.continue_ { st with
        arena := e1
        stack := .cons currentProcOpt (contElem :: cont) parent
      })

  | .wseq _ _ _, .empty =>
    throw (.illformedProgram "reached empty stack with Ewseq")

  -- Esseq pat e1 e2: strong sequencing
  -- Corresponds to: core_reduction.lem Esseq cases
  | .sseq pat e1 e2, .cons currentProcOpt cont parent =>
    match e1.expr with
    -- Case: lets pat = {A}v in e2 --> {A}(lets pat = v in e2)
    -- Corresponds to: core_reduction.lem LETS-ANNOT rule
    -- The annotation propagates to wrap e2
    | .annot xs innerE =>
      match valueFromExpr innerE with
      | some cval =>
        -- {A}v case: propagate annotation to e2
        match st.updateEnv pat cval with
        | some st' =>
          let wrappedE2 : AExpr := { annots := [], expr := .annot xs e2 }
          pure (.continue_ { st' with arena := wrappedE2 })
        | none => throw .patternMatchFailed
      | none =>
        match innerE.expr with
        | .pure pe1 =>
          -- {A}(pure e) - evaluate and propagate annotation
          let cval ← evalPexpr defaultPexprFuel st.env pe1
          match st.updateEnv pat cval with
          | some st' =>
            let wrappedE2 : AExpr := { annots := [], expr := .annot xs e2 }
            pure (.continue_ { st' with arena := wrappedE2 })
          | none => throw .patternMatchFailed
        | _ =>
          -- {A}e where e is not a value - focus on e1
          let contElem := ContElem.sseq arenaAnnots pat e2
          pure (.continue_ { st with
            arena := e1
            stack := .cons currentProcOpt (contElem :: cont) parent
          })
    -- Case: lets pat = v in e2 --> e2[v/pat]
    -- Corresponds to: core_reduction.lem LETS-PURE rule
    | .pure pe1 =>
      let cval ← evalPexpr defaultPexprFuel st.env pe1
      match st.updateEnv pat cval with
      | some st' => pure (.continue_ { st' with arena := e2 })
      | none => throw .patternMatchFailed
    | _ =>
      -- e1 not yet a value - focus on e1, push continuation
      let contElem := ContElem.sseq arenaAnnots pat e2
      pure (.continue_ { st with
        arena := e1
        stack := .cons currentProcOpt (contElem :: cont) parent
      })

  | .sseq _ _ _, .empty =>
    throw (.illformedProgram "reached empty stack with Esseq")

  -- Esave: evaluate default args and substitute into body
  -- Corresponds to: core_run.lem:1494-1501
  | .save _sym _retTy symBTyPes body, _ =>
    -- Evaluate default argument values and bind them
    let st' ← symBTyPes.foldlM (init := st) fun acc (sym, _bTy, pe) => do
      let cval ← evalPexpr defaultPexprFuel acc.env pe
      pure (acc.bindSym sym cval)
    pure (.continue_ { st' with arena := body })

  -- Erun: jump to labeled continuation
  -- Corresponds to: core_run.lem:1509-1530
  | .run sym pes, .cons (some currentProc) _cont parent =>
    -- Two-level lookup: first by procedure, then by label
    -- Corresponds to: Maybe.bind (Map.lookup proc_sym st.labeled) (Map.lookup sym)
    let procConts : Option LabeledConts := Std.HashMap.get? allLabeledConts currentProc
    match procConts.bind (fun conts => Std.HashMap.get? conts sym) with
    | none =>
      throw (.illformedProgram s!"Erun couldn't resolve label: '{sym.name}' for procedure '{currentProc.name}'")
    | some labeledCont =>
      -- Evaluate arguments
      let cvals ← pes.mapM (evalPexpr defaultPexprFuel st.env)
      -- Substitute arguments into continuation body
      if labeledCont.params.length != cvals.length then
        throw (.typeError s!"Erun '{sym.name}': wrong number of arguments")
      let bindings := labeledCont.params.zip cvals
      let env' := bindAllInEnv bindings st.env
      -- Push empty continuation for new "procedure" context
      let newStack := Stack.pushEmptyCont (some currentProc) parent
      pure (.continue_ { st with
        arena := labeledCont.body
        stack := newStack
        env := env'
      })

  | .run _ _, .cons none _ _ =>
    throw (.illformedProgram "found Erun outside of a procedure")

  | .run _ _, .empty =>
    throw (.illformedProgram "reached empty stack with Erun")

  -- Eproc: procedure call
  -- Corresponds to: core_run.lem:1002-1042
  | .proc name pes, sk =>
    match name with
    | .sym psym =>
      -- Evaluate arguments
      let cvals ← pes.mapM (evalPexpr defaultPexprFuel st.env)
      -- Look up and call procedure (returns resolved symbol for label lookup)
      match callProc file psym cvals with
      | .ok (resolvedSym, (procEnv, body)) =>
        -- Push new stack frame with procedure environment
        -- Use resolvedSym (not psym) so Erun can find labels in allLabeledConts
        let newStack := Stack.pushEmptyCont (some resolvedSym) sk
        pure (.continue_ { st with
          arena := body
          stack := newStack
          env := procEnv :: st.env  -- Push new scope
          currentProc := some resolvedSym
        })
      | .error err => throw err
    | .impl ic =>
      let msg := match ic with
        | .other name => s!"builtin function '{name}' not implemented (requires driver layer)"
        | _ => s!"impl proc: {repr ic}"
      throw (.notImplemented msg)

  -- Eaction: execute memory action
  -- Corresponds to: core_action_step in core_run.lem:275-650
  -- For polarity handling, see core_reduction.lem:1280-1327:
  --   Pos actions → DA_pos [] fp (execute directly)
  --   Neg actions → NEG ACTION TRANSFORMATION (create unseq structure)
  --
  -- NEG ACTION TRANSFORMATION (core_reduction.lem:1285-1302):
  -- When a neg action is encountered:
  -- 1. break_at_bound_and_sseq ctx → (ctx_bound, ctxA)
  -- 2. n ← fresh_excluded_id
  -- 3. ctxA' = add_exclusion n ctxA  -- Add n to all exclusion sets
  -- 4. expr' = wseq sym = unseq [Eexcluded n act; apply_ctx ctxA' (pure ())] in sym
  -- 5. return apply_ctx ctx_bound expr'
  | .action paction, stack =>
    match paction.polarity with
    | .neg =>
      -- NEG ACTION TRANSFORMATION
      match stack with
      | .cons currentProcOpt cont parent =>
        match Stack.breakAtBound cont with
        | .noBound =>
          -- No bound found - this is unexpected for neg actions
          throw (.illformedProgram "neg action without bound in continuation")
        | .boundNoSseq _boundElem ctxA =>
          -- BOUND_NO_SSEQ: No sseq between action and bound
          -- Corresponds to: core_reduction.lem:1289-1302
          -- wseq sym = unseq [Eexcluded n act; apply_ctx ctxA' (pure ())] in sym
          let n ← InterpM.freshExclusionId
          let ctxA' := Stack.addExclusionToCont n ctxA
          let sym : Sym := { name := some s!"_unseq_{n}", id := n }
          let excludedExpr := mkExcludedExpr n paction
          let ctx' := contToContext ctxA'
          let ctxExpr := applyCtx ctx' mkPureUnit
          let unseqExpr := mkUnseqExpr [excludedExpr, ctxExpr]
          let wseqExpr := mkWseqExpr sym unseqExpr (mkPureSym sym)
          let newCont := Stack.dropUntilBound cont
          pure (.continue_ { st with
            arena := wseqExpr
            stack := .cons currentProcOpt newCont parent
          })

        | .boundWithSseq _boundElem ctxA sseqPat ctxB sseqE2 =>
          -- BOUND_WITH_SSEQ: sseq between action and bound
          if ctxB.isEmpty then
            -- BOUND_WITH_SSEQ with CTX (empty inner context)
            -- Corresponds to: core_reduction.lem:1303-1309
            -- Just execute: sseq sseq_pat = (action Pos act) in sseq_e2
            -- wrapped in ctxA and ctx_bound
            let posActionExpr := mkPosActionExpr paction
            let sseqExpr := mkSseqExpr sseqPat posActionExpr sseqE2
            -- Apply ctxA around the sseq
            let ctxA' := contToContext ctxA
            let wrappedExpr := applyCtx ctxA' sseqExpr
            -- Drop everything up to and including bound
            let newCont := Stack.dropUntilBound cont
            pure (.continue_ { st with
              arena := wrappedExpr
              stack := .cons currentProcOpt newCont parent
            })
          else
            -- BOUND_WITH_SSEQ with non-CTX (non-empty inner context)
            -- Corresponds to: core_reduction.lem:1311-1323
            -- sseq (_, sseq_pat) = unseq [Eexcluded n act; apply_ctx ctxB' (pure ())] in sseq_e2
            -- wrapped in ctxA and ctx_bound
            let n ← InterpM.freshExclusionId
            let ctxB' := Stack.addExclusionToCont n ctxB
            let excludedExpr := mkExcludedExpr n paction
            let ctxB'' := contToContext ctxB'
            let ctxExpr := applyCtx ctxB'' mkPureUnit
            let unseqExpr := mkUnseqExpr [excludedExpr, ctxExpr]
            let sseqExpr := mkSseqTupleExpr sseqPat unseqExpr sseqE2
            -- Apply ctxA around the sseq
            let ctxA' := contToContext ctxA
            let wrappedExpr := applyCtx ctxA' sseqExpr
            -- Drop everything up to and including bound
            let newCont := Stack.dropUntilBound cont
            pure (.continue_ { st with
              arena := wrappedExpr
              stack := .cons currentProcOpt newCont parent
            })

      | .empty =>
        throw (.illformedProgram "neg action with empty stack")
    | .pos =>
      -- POSITIVE POLARITY: Execute the action directly
      let act := paction.action.action
      match act with
      -- Create: allocate memory for a typed object
      -- Corresponds to: core_run.lem:297-338 (Create case)
      | .create alignPe sizePe prefix_ =>
        let alignVal ← evalPexpr defaultPexprFuel st.env alignPe
        let sizeVal ← evalPexpr defaultPexprFuel st.env sizePe
        match alignVal, sizeVal with
        | .object (.integer alignIv), .ctype ty =>
          let typeEnv ← InterpM.getTypeEnv
          let size := sizeof typeEnv ty
          let prefixName := prefix_.val
          let ptr ← InterpM.liftMem (allocateImpl prefixName size (some ty) alignIv.val.toNat .writable none)
          let resultVal := Value.object (.pointer ptr)
          pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
        | _, _ =>
          throw (.typeError "create: expected integer alignment and ctype size")

      -- CreateReadonly: allocate read-only memory with initial value
      -- Corresponds to: core_run.lem:340-408 (CreateReadOnly case)
      | .createReadonly alignPe sizePe initPe prefix_ =>
        let alignVal ← evalPexpr defaultPexprFuel st.env alignPe
        let sizeVal ← evalPexpr defaultPexprFuel st.env sizePe
        let initVal ← evalPexpr defaultPexprFuel st.env initPe
        match alignVal, sizeVal with
        | .object (.integer alignIv), .ctype ty =>
          let typeEnv ← InterpM.getTypeEnv
          let size := sizeof typeEnv ty
          let prefixName := prefix_.val
          -- Convert Core value to MemValue
          match memValueFromValue ty initVal with
          | some mval =>
            let ptr ← InterpM.liftMem (allocateImpl prefixName size (some ty) alignIv.val.toNat (.readonly .constQualified) (some mval))
            let resultVal := Value.object (.pointer ptr)
            pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
          | none =>
            throw (.typeError s!"createReadonly: value doesn't match type")
        | _, _ =>
          throw (.typeError "createReadonly: expected integer alignment and ctype size")

      -- Alloc: allocate raw memory region (malloc-style)
      -- Corresponds to: core_run.lem:409-449 (Alloc case)
      | .alloc alignPe sizePe prefix_ =>
        let alignVal ← evalPexpr defaultPexprFuel st.env alignPe
        let sizeVal ← evalPexpr defaultPexprFuel st.env sizePe
        match alignVal, sizeVal with
        | .object (.integer alignIv), .object (.integer sizeIv) =>
          let prefixName := prefix_.val
          let ptr ← InterpM.liftMem (allocateImpl prefixName sizeIv.val.toNat none alignIv.val.toNat .writable none)
          let resultVal := Value.object (.pointer ptr)
          pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
        | _, _ =>
          throw (.typeError "alloc: expected integer alignment and size")

      -- Kill: deallocate memory
      -- Corresponds to: core_run.lem:451-477 (Kill case)
      | .kill kind ptrPe =>
        let ptrVal ← evalPexpr defaultPexprFuel st.env ptrPe
        match ptrVal with
        | .object (.pointer ptr) =>
          let isDynamic := match kind with
            | .dynamic => true
            | .static _ => false
          InterpM.liftMem (killImpl isDynamic ptr)
          let resultVal := Value.unit
          pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
        | .loaded (.specified (.pointer ptr)) =>
          let isDynamic := match kind with
            | .dynamic => true
            | .static _ => false
          InterpM.liftMem (killImpl isDynamic ptr)
          let resultVal := Value.unit
          pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
        | _ =>
          throw (.typeError "kill: expected pointer value")

      -- Store: store value to memory (POSITIVE POLARITY ONLY)
      -- Corresponds to: core_reduction.lem:689-698 (Store case)
      -- Creates: Expr [] (Eannot [DA_pos exclusionSet fp] (mk_value_e Vunit))
      --
      -- Note: Neg polarity is handled by the neg action transformation above,
      -- which wraps the action in Eexcluded and creates an unseq structure.
      -- This branch only executes for pos polarity actions.
      | .store isLocking tyPe ptrPe valPe _order =>
        let tyVal ← evalPexpr defaultPexprFuel st.env tyPe
        let ptrVal ← evalPexpr defaultPexprFuel st.env ptrPe
        let cval ← evalPexpr defaultPexprFuel st.env valPe
        -- Get exclusion context from continuation stack
        let exclusionSet := match st.stack with
          | .cons _ cont _ => Stack.getExclusionContext cont
          | .empty => []
        match tyVal, ptrVal with
        | .ctype ty, .object (.pointer ptr) =>
          match memValueFromValue ty cval with
          | some mval =>
            let fp ← InterpM.liftMem (storeImpl ty isLocking ptr mval)
            let resultVal := Value.unit
            -- Create DA_pos annotation (this is a pos polarity action)
            let dynAnnots : DynAnnotations := [.pos exclusionSet fp]
            pure (.continue_ { st with arena := mkAnnotatedValueExpr arenaAnnots dynAnnots resultVal })
          | none =>
            throw (.typeError s!"store: value doesn't match type")
        | .ctype ty, .loaded (.specified (.pointer ptr)) =>
          match memValueFromValue ty cval with
          | some mval =>
            let fp ← InterpM.liftMem (storeImpl ty isLocking ptr mval)
            let resultVal := Value.unit
            -- Create DA_pos annotation (this is a pos polarity action)
            let dynAnnots : DynAnnotations := [.pos exclusionSet fp]
            pure (.continue_ { st with arena := mkAnnotatedValueExpr arenaAnnots dynAnnots resultVal })
          | none =>
            throw (.typeError s!"store: value doesn't match type")
        | _, _ =>
          throw (.typeError "store: expected ctype and pointer")

      -- Load: load value from memory (POSITIVE POLARITY ONLY)
      -- Corresponds to: core_reduction.lem:724-734 (Load case)
      -- Creates: Expr [] (Eannot [DA_pos exclusionSet fp] (mk_value_e cval))
      --
      -- Note: Neg polarity is handled by the neg action transformation above,
      -- which wraps the action in Eexcluded and creates an unseq structure.
      -- This branch only executes for pos polarity actions.
      | .load tyPe ptrPe _order =>
        let tyVal ← evalPexpr defaultPexprFuel st.env tyPe
        let ptrVal ← evalPexpr defaultPexprFuel st.env ptrPe
        -- Get exclusion context from continuation stack
        let exclusionSet := match st.stack with
          | .cons _ cont _ => Stack.getExclusionContext cont
          | .empty => []
        match tyVal, ptrVal with
        | .ctype ty, .object (.pointer ptr) =>
          let (fp, mval) ← InterpM.liftMem (loadImpl ty ptr)
          let resultVal := valueFromMemValue mval
          -- Create DA_pos annotation (this is a pos polarity action)
          let dynAnnots : DynAnnotations := [.pos exclusionSet fp]
          pure (.continue_ { st with arena := mkAnnotatedValueExpr arenaAnnots dynAnnots resultVal })
        | .ctype ty, .loaded (.specified (.pointer ptr)) =>
          let (fp, mval) ← InterpM.liftMem (loadImpl ty ptr)
          let resultVal := valueFromMemValue mval
          -- Create DA_pos annotation (this is a pos polarity action)
          let dynAnnots : DynAnnotations := [.pos exclusionSet fp]
          pure (.continue_ { st with arena := mkAnnotatedValueExpr arenaAnnots dynAnnots resultVal })
        | _, _ =>
          throw (.typeError "load: expected ctype and pointer")

      -- SeqRMW: sequential read-modify-write (increment/decrement)
      -- Corresponds to: core_reduction.lem:1214-1276 and driver.lem:704-714
      -- NOTE: Negative SeqRMW is forbidden by typecheck (core_reduction.lem:1215-1216)
      --
      -- SeqRMW performs its OWN neg action transformation for the store footprint.
      -- This is critical for race detection: the store creates a DA_neg annotation
      -- with a fresh exclusion ID, so it can't be falsely excluded by outer neg
      -- transformations (DA_neg n1 vs DA_neg n2 where n1≠n2 → not excluded).
      --
      -- Algorithm (matching core_reduction.lem:1218-1277 and driver.lem:704-714):
      -- 1. Evaluate pe1 (type) and pe2 (pointer)
      -- 2. Fresh exclusion ID n (core_reduction.lem:1223)
      -- 3. Load current value from memory (driver.lem:705 DISCARDS load footprint)
      -- 4. Bind sym to loaded value, evaluate update expression
      -- 5. Store new value → get fpStore
      -- 6. Build {DA_neg n [] fpStore}(unit) and result value expression
      -- 7. Expression reconstruction: break_at_bound_and_sseq + unseq structure
      --    (core_reduction.lem:1246-1271)
      | .seqRmw withForward tyPe ptrPe sym valPe =>
        -- Note: Negative SeqRMW is forbidden (core_reduction.lem:1215-1216)
        -- If we're here, we're in the .pos branch, so polarity is already positive.
        match stack with
        | .cons currentProcOpt cont parent =>
          let tyVal ← evalPexpr defaultPexprFuel st.env tyPe
          let ptrVal ← evalPexpr defaultPexprFuel st.env ptrPe
          -- Helper: given a resolved pointer, execute the RMW and do neg transformation
          let doSeqRmw (ty : Ctype) (ptr : PointerValue) : InterpM StepResult := do
            -- Step 2: Fresh exclusion ID (core_reduction.lem:1223)
            let n ← InterpM.freshExclusionId
            -- Step 3: Load current value (driver.lem:705 discards load footprint)
            let (_, mval) ← InterpM.liftMem (loadImpl ty ptr)
            -- Step 4: Bind sym to loaded value, evaluate update expression
            let loadedVal := valueFromMemValue mval
            let newEnv := bindInEnv sym loadedVal st.env
            let cval3 ← evalPexpr defaultPexprFuel newEnv valPe
            -- Step 5: Convert to MemValue and store
            let ty' : Ctype := { annots := [], ty := unatomic_ ty.ty }
            match memValueFromValue ty' cval3 with
            | some mval' =>
              let fpStore ← InterpM.liftMem (storeImpl ty false ptr mval')
              -- Step 6: Build annotated unit and result value expression
              let resultVal := if withForward then valueFromMemValue mval' else loadedVal
              let cvalExpr := mkValueExpr [] resultVal
              let annotatedUnit := mkAnnotatedValueExpr [] [.neg n [] fpStore] .unit
              -- Step 7: Expression reconstruction (core_reduction.lem:1246-1271)
              match Stack.breakAtBound cont with
              | .noBound =>
                throw (.illformedProgram "SeqRMW: no bound in continuation")
              | .boundNoSseq _boundElem ctxA =>
                -- BOUND_NO_SSEQ (core_reduction.lem:1249-1258)
                let ctxA' := Stack.addExclusionToCont n ctxA
                let sym' : Sym := { name := some s!"_unseq_{n}", id := n }
                let ctx' := contToContext ctxA'
                let ctxExpr := applyCtx ctx' cvalExpr
                let unseqExpr := mkUnseqExpr [annotatedUnit, ctxExpr]
                let wseqExpr := mkWseqExpr sym' unseqExpr (mkPureSym sym')
                let newCont := Stack.dropUntilBound cont
                pure (.continue_ { st with
                  arena := wseqExpr
                  stack := .cons currentProcOpt newCont parent
                })
              | .boundWithSseq _boundElem ctxA sseqPat ctxB sseqE2 =>
                if ctxB.isEmpty then
                  -- BOUND_WITH_SSEQ with empty ctxB (core_reduction.lem:1259-1262)
                  let annotatedCval := mkAnnotatedValueExpr [] [.neg n [] fpStore] resultVal
                  let sseqExpr := mkSseqExpr sseqPat annotatedCval sseqE2
                  let ctxA' := contToContext ctxA
                  let wrappedExpr := applyCtx ctxA' sseqExpr
                  let newCont := Stack.dropUntilBound cont
                  pure (.continue_ { st with
                    arena := wrappedExpr
                    stack := .cons currentProcOpt newCont parent
                  })
                else
                  -- BOUND_WITH_SSEQ with non-empty ctxB (core_reduction.lem:1263-1271)
                  let ctxB' := Stack.addExclusionToCont n ctxB
                  let ctxB'' := contToContext ctxB'
                  let ctxExpr := applyCtx ctxB'' cvalExpr
                  let unseqExpr := mkUnseqExpr [annotatedUnit, ctxExpr]
                  let sseqExpr := mkSseqTupleExpr sseqPat unseqExpr sseqE2
                  let ctxA' := contToContext ctxA
                  let wrappedExpr := applyCtx ctxA' sseqExpr
                  let newCont := Stack.dropUntilBound cont
                  pure (.continue_ { st with
                    arena := wrappedExpr
                    stack := .cons currentProcOpt newCont parent
                  })
            | none =>
              throw (.typeError "seq_rmw: update expression doesn't match lvalue type")
          match tyVal, ptrVal with
          | .ctype ty, .object (.pointer ptr) =>
            doSeqRmw ty ptr
          | .ctype ty, .loaded (.specified (.pointer ptr)) =>
            doSeqRmw ty ptr
          | _, _ =>
            throw (.typeError "seq_rmw: expected ctype and pointer")
        | .empty =>
          throw (.illformedProgram "seq_rmw with empty stack")

      -- Fence, RMW, CompareExchange - not implemented yet
      | .fence _ =>
          throw (.notImplemented "fence")
      | .rmw _ _ _ _ _ _ =>
          throw (.notImplemented "rmw")
      | .compareExchangeStrong _ _ _ _ _ _ =>
          throw (.notImplemented "compare_exchange_strong")
      | .compareExchangeWeak _ _ _ _ _ _ =>
          throw (.notImplemented "compare_exchange_weak")

  -- Eexcluded: wrapper for neg actions that enforces DA_neg annotation
  -- Corresponds to: core_reduction.lem:1326-1327 (Eexcluded n action case)
  -- When a neg action is transformed, it gets wrapped in Eexcluded(n, ...)
  -- which ensures the resulting annotation is DA_neg n [] fp regardless of
  -- the action's original polarity.
  --
  -- This is a key part of the neg action transformation mechanism:
  -- 1. Neg action encountered → transformed to unseq [Eexcluded n act; ctx]
  -- 2. Eexcluded n act executes → produces DA_neg n [] fp
  -- 3. At unseq completion, race detection checks DA_neg n vs other annotations
  | .excluded exclId paction, _ =>
    let act := paction.action.action
    match act with
    -- Store inside Eexcluded: always produces DA_neg exclId [] fp
    | .store isLocking tyPe ptrPe valPe _order =>
      let tyVal ← evalPexpr defaultPexprFuel st.env tyPe
      let ptrVal ← evalPexpr defaultPexprFuel st.env ptrPe
      let cval ← evalPexpr defaultPexprFuel st.env valPe
      match tyVal, ptrVal with
      | .ctype ty, .object (.pointer ptr) =>
        match memValueFromValue ty cval with
        | some mval =>
          let fp ← InterpM.liftMem (storeImpl ty isLocking ptr mval)
          let resultVal := Value.unit
          -- ALWAYS produce DA_neg with the exclusion ID from Eexcluded wrapper
          let dynAnnots : DynAnnotations := [.neg exclId [] fp]
          pure (.continue_ { st with arena := mkAnnotatedValueExpr arenaAnnots dynAnnots resultVal })
        | none =>
          throw (.typeError s!"store (excluded): value doesn't match type")
      | .ctype ty, .loaded (.specified (.pointer ptr)) =>
        match memValueFromValue ty cval with
        | some mval =>
          let fp ← InterpM.liftMem (storeImpl ty isLocking ptr mval)
          let resultVal := Value.unit
          let dynAnnots : DynAnnotations := [.neg exclId [] fp]
          pure (.continue_ { st with arena := mkAnnotatedValueExpr arenaAnnots dynAnnots resultVal })
        | none =>
          throw (.typeError s!"store (excluded): value doesn't match type")
      | _, _ =>
        throw (.typeError "store (excluded): expected ctype and pointer")

    -- Load inside Eexcluded: always produces DA_neg exclId [] fp
    | .load tyPe ptrPe _order =>
      let tyVal ← evalPexpr defaultPexprFuel st.env tyPe
      let ptrVal ← evalPexpr defaultPexprFuel st.env ptrPe
      match tyVal, ptrVal with
      | .ctype ty, .object (.pointer ptr) =>
        let (fp, mval) ← InterpM.liftMem (loadImpl ty ptr)
        let resultVal := valueFromMemValue mval
        -- ALWAYS produce DA_neg with the exclusion ID from Eexcluded wrapper
        let dynAnnots : DynAnnotations := [.neg exclId [] fp]
        pure (.continue_ { st with arena := mkAnnotatedValueExpr arenaAnnots dynAnnots resultVal })
      | .ctype ty, .loaded (.specified (.pointer ptr)) =>
        let (fp, mval) ← InterpM.liftMem (loadImpl ty ptr)
        let resultVal := valueFromMemValue mval
        let dynAnnots : DynAnnotations := [.neg exclId [] fp]
        pure (.continue_ { st with arena := mkAnnotatedValueExpr arenaAnnots dynAnnots resultVal })
      | _, _ =>
        throw (.typeError "load (excluded): expected ctype and pointer")

    -- Create inside Eexcluded: execute but no footprint (allocation, not memory access)
    -- Corresponds to: these actions don't produce footprints for race detection
    | .create alignPe sizePe prefix_ =>
      let alignVal ← evalPexpr defaultPexprFuel st.env alignPe
      let sizeVal ← evalPexpr defaultPexprFuel st.env sizePe
      match alignVal, sizeVal with
      | .object (.integer alignIv), .ctype ty =>
        let typeEnv ← InterpM.getTypeEnv
        let size := sizeof typeEnv ty
        let prefixName := prefix_.val
        let ptr ← InterpM.liftMem (allocateImpl prefixName size (some ty) alignIv.val.toNat .writable none)
        let resultVal := Value.object (.pointer ptr)
        -- No footprint annotations for allocation operations
        pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
      | _, _ =>
        throw (.typeError "create (excluded): expected integer alignment and ctype size")

    -- CreateReadonly inside Eexcluded: execute but no footprint
    | .createReadonly alignPe sizePe initPe prefix_ =>
      let alignVal ← evalPexpr defaultPexprFuel st.env alignPe
      let sizeVal ← evalPexpr defaultPexprFuel st.env sizePe
      let initVal ← evalPexpr defaultPexprFuel st.env initPe
      match alignVal, sizeVal with
      | .object (.integer alignIv), .ctype ty =>
        let typeEnv ← InterpM.getTypeEnv
        let size := sizeof typeEnv ty
        let prefixName := prefix_.val
        match memValueFromValue ty initVal with
        | some mval =>
          let ptr ← InterpM.liftMem (allocateImpl prefixName size (some ty) alignIv.val.toNat (.readonly .constQualified) (some mval))
          let resultVal := Value.object (.pointer ptr)
          pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
        | none =>
          throw (.typeError "createReadonly (excluded): value doesn't match type")
      | _, _ =>
        throw (.typeError "createReadonly (excluded): expected integer alignment and ctype size")

    -- Alloc inside Eexcluded: execute but no footprint (allocation, not memory access)
    | .alloc alignPe sizePe prefix_ =>
      let alignVal ← evalPexpr defaultPexprFuel st.env alignPe
      let sizeVal ← evalPexpr defaultPexprFuel st.env sizePe
      match alignVal, sizeVal with
      | .object (.integer alignIv), .object (.integer sizeIv) =>
        let prefixName := prefix_.val
        let ptr ← InterpM.liftMem (allocateImpl prefixName sizeIv.val.toNat none alignIv.val.toNat .writable none)
        let resultVal := Value.object (.pointer ptr)
        pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
      | _, _ =>
        throw (.typeError "alloc (excluded): expected integer alignment and size")

    -- Kill inside Eexcluded: execute but no footprint (deallocation, not memory access)
    | .kill kind ptrPe =>
      let ptrVal ← evalPexpr defaultPexprFuel st.env ptrPe
      match ptrVal with
      | .object (.pointer ptr) =>
        let isDynamic := match kind with
          | .dynamic => true
          | .static _ => false
        InterpM.liftMem (killImpl isDynamic ptr)
        let resultVal := Value.unit
        pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
      | .loaded (.specified (.pointer ptr)) =>
        let isDynamic := match kind with
          | .dynamic => true
          | .static _ => false
        InterpM.liftMem (killImpl isDynamic ptr)
        let resultVal := Value.unit
        pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
      | _ =>
        throw (.typeError "kill (excluded): expected pointer value")

    -- Atomic operations in Eexcluded - complex semantics, not yet implemented
    | .rmw _ _ _ _ _ _ => throw (.notImplemented "excluded wrapper on rmw action")
    | .compareExchangeStrong _ _ _ _ _ _ => throw (.notImplemented "excluded wrapper on CAS action")
    | .compareExchangeWeak _ _ _ _ _ _ => throw (.notImplemented "excluded wrapper on CAS action")
    | .fence _ => throw (.notImplemented "excluded wrapper on fence action")
    | .seqRmw _ _ _ _ _ => throw (.notImplemented "seqRmw forbidden for neg polarity")

  -- Eccall: C function call through pointer
  -- Corresponds to: core_run.lem:926-999
  | .ccall funPtr _funTy args, sk =>
    -- Step 1: Evaluate function pointer expression
    let funPtrVal ← evalPexpr defaultPexprFuel st.env funPtr
    -- Step 2: Extract function symbol from pointer value
    -- Corresponds to: core_run.lem:927-936 (valueFromPexpr and case_ptrval)
    let funSym ← match funPtrVal with
      | .loaded (.specified (.pointer pv)) =>
        match pv.base with
        | .function sym => pure sym
        | .concrete _ addr =>
          -- Look up in funptrmap
          -- Corresponds to: case_funsym_opt in impl_mem.ml:1816-1827
          let mem ← InterpM.getMemory
          match mem.funptrmap.get? addr with
          | some sym => pure sym
          | none => throw (.undefinedBehavior .ub_cerb003_invalidFunctionPointer none)
        | .null _ => throw (.undefinedBehavior .ub_cerb003_invalidFunctionPointer none)
      | _ => throw (.undefinedBehavior .ub_cerb003_invalidFunctionPointer none)
    -- Step 3: Evaluate arguments
    -- Corresponds to: core_run.lem:948-956
    let argVals ← args.mapM (evalPexpr defaultPexprFuel st.env)
    -- Step 4: Check for builtin functions before calling procedure
    -- Corresponds to: core_run.lem:1046-1127 (Impl BuiltinFunction cases)
    if funSym.name == some "exit" then
      -- exit(n) terminates immediately with the given value
      -- Corresponds to: core_run.lem:1122-1126
      -- For ccall, argVals are pointers to the actual arguments, so we need to load
      match argVals with
      | [.loaded (.specified (.pointer pv))] =>
        -- Load the exit code from the pointer
        let (_, mval) ← InterpM.liftMem (loadImpl (.basic (.integer (.signed .int_))) pv)
        let resultVal := valueFromMemValue mval
        pure (.done resultVal)
      | [.object (.pointer pv)] =>
        -- Pointer as object value - load the exit code
        let (_, mval) ← InterpM.liftMem (loadImpl (.basic (.integer (.signed .int_))) pv)
        let resultVal := valueFromMemValue mval
        pure (.done resultVal)
      | [exitVal] =>
        -- Direct value (e.g., from Eproc)
        pure (.done exitVal)
      | _ => throw (.illformedProgram "exit: wrong number of arguments")
    else if funSym.name == some "abort" then
      -- abort() terminates with signal exit code 127
      -- Cerberus treats this as defined behavior (prints SIGABRT to stderr)
      pure (.done (.loaded (.specified (.integer { val := 127, prov := .none }))))
    else
    -- Step 5: Call procedure
    -- Corresponds to: core_run.lem:958-971 (call_proc)
    match callProc file funSym argVals with
    | .ok (resolvedSym, (procEnv, body)) =>
      -- Push new stack frame with procedure environment
      -- Use resolvedSym (not funSym) so Erun can find labels in allLabeledConts
      let newStack := Stack.pushEmptyCont (some resolvedSym) sk
      pure (.continue_ { st with
        arena := body
        stack := newStack
        env := procEnv :: st.env  -- Push new scope
        currentProc := some resolvedSym
      })
    | .error err => throw err

  -- Ebound: bounds marker, push bound context and continue
  -- Corresponds to: core_run.lem:1643-1649 and Cbound in context
  -- The bound is tracked in the continuation for neg action transformation.
  | .bound e, .cons currentProcOpt cont parent =>
    let boundElem := ContElem.bound arenaAnnots
    pure (.continue_ { st with
      arena := e
      stack := .cons currentProcOpt (boundElem :: cont) parent
    })
  | .bound _, .empty =>
    throw (.illformedProgram "reached empty stack with Ebound")

  -- End: nondeterministic choice - return all branches
  -- Corresponds to: core_reduction.lem:433-435 (ND es)
  -- Audited: 2026-01-30
  -- Deviations: None
  | .nd es, _ =>
    match es with
    | [] => throw (.illformedProgram "empty nd")
    | [e] => pure (.continue_ { st with arena := e })
    | _ =>
      -- Return branches for all alternatives (matches Cerberus Step_nd2)
      let branches := es.map fun e => { st with arena := e }
      pure (.branches branches)

  -- Eunseq: unsequenced evaluation with race detection
  -- Corresponds to: core_reduction.lem:384-412 (one_step Eunseq case)
  -- Uses contextual decomposition to find all reducible positions
  | .unseq es, .cons currentProcOpt cont parent =>
    match es with
    | [] => throw (.illformedProgram "empty unseq")
    | [e] => pure (.continue_ { st with arena := e })
    | _ =>
      -- Check if all expressions are irreducible (values or annotated values)
      -- Corresponds to: core_reduction.lem:385 if List.for_all is_irreducible es
      if es.all isIrreducible then
        -- All values: collect and check for races
        -- Corresponds to: one_step_unseq_aux in core_reduction.lem:244-261
        match collectValuesCheckRace es with
        | .ok (cvals, combinedAnnots) =>
          -- Create tuple value wrapped in annotations
          -- Cerberus ALWAYS wraps in Eannot fps even if fps is empty (core_reduction.lem:370)
          -- The annotations must propagate outward for race detection in nested contexts
          let tupleVal := Value.tuple cvals
          let resultExpr := mkAnnotatedValueExpr arenaAnnots combinedAnnots tupleVal
          pure (.continue_ { st with arena := resultExpr })
        | .error err => throw err
      else
        -- Not all irreducible: use contextual decomposition to find ALL reducible sub-expressions
        -- Corresponds to: get_ctx_unseq_aux in core_reduction.lem:576-588
        -- Returns StepResult.branches with all possible next states for non-deterministic exploration
        let ctxPairs := getCtxUnseqAux arenaAnnots [] [] es
        match ctxPairs with
        | [] =>
          -- Should not happen if not all are irreducible
          throw (.illformedProgram "unseq: no reducible expressions found")
        | [(ctx, reducibleExpr)] =>
          -- Single reducible expression: continue deterministically
          -- Convert context to continuation elements and focus on the reducible expression
          let ctxContElems := contextToContElems ctx
          pure (.continue_ { st with
            arena := reducibleExpr
            stack := .cons currentProcOpt (ctxContElems ++ cont) parent
          })
        | pairs =>
          -- Multiple reducible expressions: return all possible branches
          -- Each branch focuses on a different reducible sub-expression
          -- The driver will choose which to explore (exhaustive, random, or pick first)
          let branchStates := pairs.map fun (ctx, reducibleExpr) =>
            -- Convert context to continuation elements
            let ctxContElems := contextToContElems ctx
            { st with
              arena := reducibleExpr
              stack := .cons currentProcOpt (ctxContElems ++ cont) parent
            }
          pure (.branches branchStates)

  | .unseq _, .empty =>
    throw (.illformedProgram "reached empty stack with Eunseq")

  -- Memop case
  -- Corresponds to: memop_exec in driver.lem:720-870
  -- Pattern matches on memop kind and evaluates accordingly
  | .memop op args, _ =>
    -- First evaluate all argument pexprs to values
    let argVals ← args.mapM (evalPexpr defaultPexprFuel st.env)
    -- Pattern match on memop kind with argument values
    let result ← match op, argVals with
    -- Pointer comparisons
    -- Corresponds to: driver.lem:779-802
    | .ptrEq, [.object (.pointer p1), .object (.pointer p2)] =>
      let b ← InterpM.liftMem (MemoryOps.eqPtrval p1 p2)
      pure (if b then Value.true_ else Value.false_)
    | .ptrNe, [.object (.pointer p1), .object (.pointer p2)] =>
      let b ← InterpM.liftMem (MemoryOps.nePtrval p1 p2)
      pure (if b then Value.true_ else Value.false_)
    | .ptrLt, [.object (.pointer p1), .object (.pointer p2)] =>
      let b ← InterpM.liftMem (MemoryOps.ltPtrval p1 p2)
      pure (if b then Value.true_ else Value.false_)
    | .ptrGt, [.object (.pointer p1), .object (.pointer p2)] =>
      let b ← InterpM.liftMem (MemoryOps.gtPtrval p1 p2)
      pure (if b then Value.true_ else Value.false_)
    | .ptrLe, [.object (.pointer p1), .object (.pointer p2)] =>
      let b ← InterpM.liftMem (MemoryOps.lePtrval p1 p2)
      pure (if b then Value.true_ else Value.false_)
    | .ptrGe, [.object (.pointer p1), .object (.pointer p2)] =>
      let b ← InterpM.liftMem (MemoryOps.gePtrval p1 p2)
      pure (if b then Value.true_ else Value.false_)

    -- Pointer difference
    -- Corresponds to: driver.lem:756-759
    | .ptrdiff, [.ctype ty, .object (.pointer p1), .object (.pointer p2)] =>
      let ival ← InterpM.liftMem (MemoryOps.diffPtrval ty p1 p2)
      pure (.object (.integer ival))

    -- Pointer/integer conversions
    -- Corresponds to: driver.lem:762-773
    | .intFromPtr, [.ctype _refTy, .ctype intTy, .object (.pointer p)] =>
      match intTy.ty with
      | .basic (.integer ity) =>
        let ival ← InterpM.liftMem (MemoryOps.intfromptr _refTy ity p)
        pure (.object (.integer ival))
      | _ => throw (.typeError s!"intFromPtr: expected integer ctype, got {repr intTy.ty}")
    | .ptrFromInt, [.ctype intTy, .ctype refTy, .object (.integer ival)] =>
      match intTy.ty with
      | .basic (.integer ity) =>
        let pval ← InterpM.liftMem (MemoryOps.ptrfromint ity refTy ival)
        pure (.object (.pointer pval))
      | _ => throw (.typeError s!"ptrFromInt: expected integer ctype, got {repr intTy.ty}")

    -- Pointer validity checks
    -- Corresponds to: driver.lem:775-777
    | .ptrValidForDeref, [.ctype refTy, .object (.pointer p)] =>
      let b ← InterpM.liftMem (MemoryOps.validForDeref refTy p)
      pure (if b then Value.true_ else Value.false_)
    | .ptrWellAligned, [.ctype refTy, .object (.pointer p)] =>
      let b ← InterpM.liftMem (MemoryOps.isWellAligned refTy p)
      pure (if b then Value.true_ else Value.false_)

    -- Array shift (pointer arithmetic)
    -- Corresponds to: driver.lem:823-830
    | .ptrArrayShift, [.object (.pointer p), .ctype ty, .object (.integer n)] =>
      let pval ← InterpM.liftMem (MemoryOps.effArrayShiftPtrval p ty n)
      pure (.object (.pointer pval))

    -- Member shift (struct field access)
    -- Corresponds to: driver.lem:832-839
    | .ptrMemberShift tagSym memberId, [.object (.pointer p)] =>
      let pval ← InterpM.liftMem (MemoryOps.effMemberShiftPtrval p tagSym memberId)
      pure (.object (.pointer pval))

    -- Memory operations
    -- Corresponds to: driver.lem:804-812
    | .memcpy, [.object (.pointer dst), .object (.pointer src), .object (.integer size)] =>
      let pval ← InterpM.liftMem (MemoryOps.memcpy dst src size)
      pure (.object (.pointer pval))
    | .memcmp, [.object (.pointer p1), .object (.pointer p2), .object (.integer size)] =>
      let ival ← InterpM.liftMem (MemoryOps.memcmp p1 p2 size)
      pure (.object (.integer ival))
    | .realloc, [.object (.integer align), .object (.pointer oldPtr), .object (.integer size)] =>
      let pval ← InterpM.liftMem (MemoryOps.realloc align oldPtr size)
      pure (.object (.pointer pval))

    -- Copy allocation ID
    -- Corresponds to: driver.lem:863-870
    | .copyAllocId, [.object (.pointer src), .object (.pointer dst)] =>
      -- Copy provenance from src to dst
      let pval := { dst with prov := src.prov }
      pure (.object (.pointer pval))

    -- Varargs
    -- Corresponds to: va_start in impl_mem.ml:2698-2704
    | .vaStart, [.list _ elems] =>
      -- Extract (ctype, pointer) pairs from the list
      let args ← elems.mapM fun v => do
        match v with
        | .tuple [.ctype cty, .object (.pointer ptr)] => pure (cty, ptr)
        | _ => throw (.typeError "va_start: expected (ctype, pointer) pairs")
      -- Get next varargs ID and store the args
      let mem ← InterpM.getMemory
      let id := mem.nextVarargsId
      let newMem := { mem with
        varargs := mem.varargs.insert id (0, args)
        nextVarargsId := id + 1
      }
      InterpM.setMemory newMem
      -- Return IV(Prov_none, id) as an integer value
      pure (.object (.integer { val := id, prov := .none }))

    -- Corresponds to: va_copy in impl_mem.ml:2706-2721
    | .vaCopy, [.object (.integer iv)] =>
      match iv.prov with
      | .none =>
        let id := iv.val.toNat
        let mem ← InterpM.getMemory
        match mem.varargs[id]? with
        | some args =>
          let newId := mem.nextVarargsId
          let newMem := { mem with
            varargs := mem.varargs.insert newId args
            nextVarargsId := newId + 1
          }
          InterpM.setMemory newMem
          pure (.object (.integer { val := newId, prov := .none }))
        | none => throw (.typeError "va_copy: not initialized")
      | _ => throw (.typeError "va_copy: invalid va_list")

    -- Corresponds to: va_arg in impl_mem.ml:2723-2741
    | .vaArg, [.object (.integer iv), .ctype _ty] =>
      match iv.prov with
      | .none =>
        let id := iv.val.toNat
        let mem ← InterpM.getMemory
        match mem.varargs[id]? with
        | some (i, args) =>
          match args[i]? with
          | some (_, ptr) =>
            -- Update index
            let newMem := { mem with varargs := mem.varargs.insert id (i + 1, args) }
            InterpM.setMemory newMem
            -- Return the pointer
            pure (.object (.pointer ptr))
          | none => throw (.typeError "va_arg: invalid number of arguments")
        | none => throw (.typeError "va_arg: not initialized")
      | _ => throw (.typeError "va_arg: invalid va_list")

    -- Corresponds to: va_end in impl_mem.ml:2743-2754
    | .vaEnd, [.object (.integer iv)] =>
      match iv.prov with
      | .none =>
        let id := iv.val.toNat
        let mem ← InterpM.getMemory
        match mem.varargs[id]? with
        | some _ =>
          let newMem := { mem with varargs := mem.varargs.erase id }
          InterpM.setMemory newMem
          pure .unit
        | none => throw (.typeError "va_end: not initialized")
      | _ => throw (.typeError "va_end: invalid va_list")

    | .vaStart, _ => throw (.typeError "va_start: expected list argument")
    | .vaCopy, _ => throw (.typeError "va_copy: expected integer argument")
    | .vaArg, _ => throw (.typeError "va_arg: expected (integer, ctype) arguments")
    | .vaEnd, _ => throw (.typeError "va_end: expected integer argument")

    -- CHERI intrinsics - not yet implemented
    | .cheriIntrinsic name, _ => throw (.notImplemented s!"CHERI intrinsic: {name}")

    | _, _ => throw (.typeError "memop called with unexpected arguments")

    -- Return the result as a pure value
    pure (.continue_ { st with arena := mkValueExpr arenaAnnots result })

  -- Concurrency cases
  | .par _, _ =>
    throw (.notImplemented "par (parallel execution)")

  | .wait _, _ =>
    throw (.notImplemented "wait")

  -- Dynamic annotations (Eannot)
  -- Corresponds to: core_reduction.lem Eannot cases
  -- {A}v is a value - we need to apply continuations while preserving the annotation
  | .annot dynAnnots inner, stack =>
    -- Check if inner is a value (Epure(PEval v))
    match valueFromExpr inner with
    | some _cval =>
      -- {A}v is a value - apply continuations while preserving annotation
      match stack with
      | .empty =>
        -- Empty stack: this annotated value is the final result
        -- (The annotation will be stripped by the driver, but for unseq race checking
        -- we need it to propagate through)
        pure (.continue_ { st with arena := inner })
      | .cons currentProcOpt cont parent =>
        match cont with
        | [] =>
          -- Empty continuation, pop to parent frame
          -- The annotated value continues to parent's continuation
          let env' := match st.env with
            | [] => [{}]
            | _ :: rest => if rest.isEmpty then [{}] else rest
          pure (.continue_ { st with
            arena := arena  -- arena is the {A}v
            stack := parent
            env := env'
          })
        | elem :: rest =>
          -- Handle ONE continuation element at a time (same approach as .pure case)
          -- The annotation stays with the value as it propagates
          match elem with
          | .wseq wseqAnnots pat e2 =>
              -- Corresponds to: core_reduction.lem:383-391 LETW-ANNOT rule
              -- letw pat = {A}v in E2 --> {A} { v / pat } E2
              -- NOTE: Cerberus passes annotations through unchanged (no neg-to-pos conversion)
              match valueFromExpr inner with
              | some cval =>
                  match st.updateEnv pat cval with
                  | some st' =>
                    let wrappedE2 : AExpr := { annots := wseqAnnots, expr := .annot dynAnnots e2 }
                    pure (.continue_ { st' with arena := wrappedE2, stack := .cons currentProcOpt rest parent })
                  | none => throw .patternMatchFailed
              | none => throw (.illformedProgram "expected value in annotated expression")
          | .sseq sseqAnnots pat e2 =>
              -- Corresponds to: core_reduction.lem:402-410 LETS-ANNOT rule
              -- lets pat = {A}v in E2 --> {A} { v / pat } E2
              -- NOTE: Cerberus passes annotations through unchanged (no neg-to-pos conversion)
              match valueFromExpr inner with
              | some cval =>
                  match st.updateEnv pat cval with
                  | some st' =>
                    let wrappedE2 : AExpr := { annots := sseqAnnots, expr := .annot dynAnnots e2 }
                    pure (.continue_ { st' with arena := wrappedE2, stack := .cons currentProcOpt rest parent })
                  | none => throw .patternMatchFailed
              | none => throw (.illformedProgram "expected value in annotated expression")
          | .unseq annots done remaining =>
              -- Add annotated value to done list (keep annotation for race detection)
              let newDone := done ++ [arena]  -- arena is {A}v
              match remaining with
              | [] =>
                  -- All branches done, rebuild unseq for race checking
                  let unseqExpr : AExpr := { annots, expr := .unseq newDone }
                  pure (.continue_ { st with arena := unseqExpr, stack := .cons currentProcOpt rest parent })
              | next :: moreRemaining =>
                  let newElem := ContElem.unseq annots newDone moreRemaining
                  pure (.continue_ { st with arena := next, stack := .cons currentProcOpt (newElem :: rest) parent })
          | .bound _ =>
              -- bound({A}v) → {A}v (pass through, matching Cerberus)
              pure (.continue_ { st with arena := arena, stack := .cons currentProcOpt rest parent })
          | .annot outerAnnots outerDynAnnots =>
              -- Merge annotations: {A'}{A}v → {A'A}v
              let mergedAnnots := outerDynAnnots ++ dynAnnots
              let mergedExpr : AExpr := { annots := outerAnnots, expr := .annot mergedAnnots inner }
              pure (.continue_ { st with arena := mergedExpr, stack := .cons currentProcOpt rest parent })
    | none =>
      -- inner is not a value - check for nested annotations or continue reducing
      match inner.expr with
      | .annot innerAnnots innerInner =>
        -- {A}{A'}e --> {AA'}e (merge annotations)
        -- Corresponds to: core_reduction.lem ANNOT-MERGE rule (line 291-294)
        -- Note: Race checking happens ONLY in Eunseq (one_step_unseq_aux),
        -- NOT when merging annotations from strong/weak sequences.
        let mergedAnnots := dynAnnots ++ innerAnnots
        let mergedExpr : AExpr := { annots := [], expr := .annot mergedAnnots innerInner }
        pure (.continue_ { st with arena := mergedExpr })
      | .pure pe =>
        -- {A}pure(pe) where pe needs evaluation - evaluate and keep annotation
        let cval ← evalPexpr defaultPexprFuel st.env pe
        let resultExpr := mkAnnotatedValueExpr arenaAnnots dynAnnots cval
        pure (.continue_ { st with arena := resultExpr })
      | _ =>
        -- {A}e where e needs reduction
        -- Push annotation continuation and step into e
        -- This matches Cerberus's Cannot context handling (core_reduction.lem:602-603)
        match stack with
        | .cons currentProcOpt cont parent =>
          let newCont := .annot arenaAnnots dynAnnots :: cont
          pure (.continue_ { st with
            arena := inner
            stack := .cons currentProcOpt newCont parent
          })
        | .empty =>
          -- No stack frame - create one with just the annot continuation
          throw (.illformedProgram "annotation without stack frame")

/-! ## Driver Loop

Run steps until done or error.
-/

/-- Run the interpreter until completion or error.
    Returns the final value or an error.
    For non-deterministic branches, picks the first branch (deterministic execution).
    Use NDDriver for exhaustive exploration of all branches. -/
def runUntilDone (st : ThreadState) (file : File) (allLabeledConts : HashMap Sym LabeledConts)
    (fuel : Nat := 1000000) : InterpM Value := do
  match fuel with
  | 0 => throw (.illformedProgram "execution fuel exhausted")
  | fuel' + 1 =>
  match ← step st file allLabeledConts with
  | .done v => pure v
  | .continue_ st' => runUntilDone st' file allLabeledConts fuel'
  | .branches states =>
    -- Deterministic mode: pick first branch
    -- For exhaustive exploration, use NDDriver instead
    match states with
    | [] => throw (.illformedProgram "empty branches")
    | st' :: _ => runUntilDone st' file allLabeledConts fuel'
  | .error err => throw err
  termination_by fuel

/-! ## Global Variable Initialization

Corresponds to: driver_globals in driver.lem:1541-1618

Global variables are initialized before main() runs:
1. Extract GlobalDef entries from file.globs (skip GlobalDecl)
2. For each global (sym, bTy, expr):
   - Run the interpreter with expr as arena
   - Get the resulting value (typically a pointer)
   - Bind sym to this value in the environment
3. Pass the resulting environment to main
-/

/-- Run a single expression to completion and return the value.
    Corresponds to: driver2 loop in driver.lem
    Audited: 2026-01-01
    Deviations: Simplified - no concurrency support -/
def runExprToValue (expr : AExpr) (env : List (HashMap Sym Value))
    (file : File) (fuel : Nat := 100000000) : InterpM Value := do
  -- Use a minimal stack with empty continuation (like Cerberus)
  -- Corresponds to: Stack_cons Nothing [] Stack_empty in driver.lem
  let st : ThreadState := {
    arena := expr
    stack := .cons none [] .empty
    env := env
    currentProc := none
  }
  runUntilDone st file {} fuel

/-- Initialize a single global variable.
    Corresponds to: the mapM_ body in driver.lem:1564-1616
    Audited: 2026-01-01
    Deviations: None -/
def initOneGlobal (file : File) (sym : Sym) (bTy : BaseType) (expr : AExpr)
    (env : List (HashMap Sym Value)) : InterpM (List (HashMap Sym Value)) := do
  -- Evaluate the initializer expression
  let cval ← runExprToValue expr env file
  -- Bind the symbol in the environment
  -- Corresponds to: update_env (Pattern [] (CaseBase (Just glob_sym, glob_bTy))) cval env
  let pat : APattern := { annots := [], pat := .base (some sym) bTy }
  match matchPattern pat cval with
  | some bindings => pure (bindAllInEnv bindings env)
  | none =>
    -- For simple base pattern, just bind directly
    pure (bindInEnv sym cval env)

/-- Initialize all global variables.
    Corresponds to: driver_globals in driver.lem:1541-1618
    Audited: 2026-01-01
    Deviations:
    - No spawn_thread (sequential only)
    - No exec_loc tracking -/
def initGlobals (file : File) : InterpM (List (HashMap Sym Value)) := do
  -- Start with empty environment (one scope)
  let emptyMap : HashMap Sym Value := {}
  let mut env : List (HashMap Sym Value) := [emptyMap]

  -- Extract GlobalDef entries (skip GlobalDecl)
  -- Corresponds to: driver.lem:1558-1562
  let globDefs := file.globs.filterMap fun (sym, decl) =>
    match decl with
    | .def_ bTy _cTy expr => some (sym, bTy, expr)
    | .decl _ _ => none

  -- Initialize each global in order
  -- Corresponds to: mapM_ in driver.lem:1564-1617
  for (sym, bTy, expr) in globDefs do
    env ← initOneGlobal file sym bTy expr env

  pure env

/-- Convert a string to a null-terminated char array memory value.
    Corresponds to: driver.lem:1630-1638
    ```lem
    let mem_vals = List.map (fun c -> Mem.integer_mval Ctype.Char (decode c)) (toCharList arg_str) in
    Mem.array_mval (mem_vals ++ [Mem.integer_mval Ctype.Char 0])
    ``` -/
def stringToCharArrayMval (s : String) : MemValue :=
  let charVals := s.toList.map fun c =>
    integerValueMval .char ⟨c.toNat, .none⟩
  -- Add null terminator
  let withNull := charVals ++ [integerValueMval .char ⟨0, .none⟩]
  arrayMval withNull

/-- Prepare argc and argv arguments for two-arg main.
    Corresponds to: prepare_main_args in driver.lem:1627-1698

    Cerberus structure:
    ```lem
    let prepare_main_args loc callconv tid0 main_sym arg_strs argc_sym argv_sym =
      (* 1. Build string memory values from arg_strs *)
      let args_mem_val_tys = List.map (...) arg_strs in
      let number_of_args = integerFromNat (List.length args_mem_val_tys) in
      (* 2. Allocate each argv string *)
      ND.foldlM (...) [] args_mem_val_tys >>= fun ptr_vals_rev ->
      (* 3. Allocate argv array [ptr0, ..., ptrN, null] *)
      liftMem (Mem.allocate_object ... argv_array_ty ...) >>= fun argv_array_ptr_val ->
      (* 4. For Normal_callconv: allocate argc and argv pointer *)
      match callconv with
      | Core.Normal_callconv ->
          (* allocate argc, store value *)
          (* allocate argv (char**), store pointer to array *)
          Mem.return (Vobject(OVpointer argc_ptr), Vobject(OVpointer argv_ptr))
    ```

    Audited: 2026-01-14
    Deviations:
    - Uses allocateImpl with init value instead of allocate_object + store (equivalent)
    - Simplified prefixes (no Symbol.PrefSource with loc/sym, just strings)
    - No tid0 parameter (sequential only, no thread tracking) -/
def prepareMainArgs (args : List String) : InterpM (Value × Value) := do
  let typeEnv ← InterpM.getTypeEnv

  -- Type definitions matching Cerberus:
  -- Ctype.signed_int, Ctype.char, Ctype.pointer_to_char
  let signedIntTy := Ctype.integer (.signed .int_)
  let charTy := Ctype.integer .char
  let charPtrTy := Ctype.pointer .none charTy  -- char*
  let charPtrPtrTy := Ctype.pointer .none charPtrTy  -- char**

  -- Step 1: Allocate each argument string
  -- Corresponds to: driver.lem:1629-1652 (building args_mem_val_tys and allocating strings)
  -- Cerberus: ND.foldlM (fun ptr_vals (arg_mem_val, arg_ty) -> ...) [] args_mem_val_tys
  let mut argPtrs : List PointerValue := []
  for arg in args do
    let argMval := stringToCharArrayMval arg
    let argArrayTy := Ctype.mk' (.array charTy.ty (some (arg.length + 1)))  -- +1 for null
    let argSize := sizeof typeEnv argArrayTy
    -- Cerberus: Mem.allocate_object tid0 (Symbol.PrefOther "argv refs") ...
    let argPtr ← InterpM.liftMem (allocateImpl "argv refs" argSize (some argArrayTy) 1 .writable (some argMval))
    argPtrs := argPtrs ++ [argPtr]

  -- Step 2: Build and allocate argv array [ptr0, ..., ptrN, null]
  -- Corresponds to: driver.lem:1654-1670
  -- Cerberus: argv_array_ty = Array pointer_to_char (1 + length(ptr_vals_rev))
  -- Cerberus: argv_array_mem_val = array_mval(map pointer_mval (reverse(null :: ptr_vals_rev)))
  -- Note: Cerberus builds in reverse then reverses; we build forward and append null
  let nullCharPtr := nullPtrval charTy
  let argvArrayElems := argPtrs.map (pointerMval charTy ·) ++ [pointerMval charTy nullCharPtr]
  let argvArrayMval := arrayMval argvArrayElems
  let argvArrayLen := args.length + 1  -- argc + 1 for null terminator
  let argvArrayTy := Ctype.mk' (.array charPtrTy.ty (some argvArrayLen))
  let argvArraySize := sizeof typeEnv argvArrayTy
  let argvArrayAlign := alignof typeEnv argvArrayTy
  -- Cerberus: Mem.allocate_object tid0 pref (Mem.alignof_ival argv_array_ty) argv_array_ty Nothing Nothing
  let argvArrayPtr ← InterpM.liftMem (allocateImpl "argv array" argvArraySize (some argvArrayTy) argvArrayAlign .writable (some argvArrayMval))

  -- Step 3: Allocate argv pointer (char**) pointing to argv array
  -- Corresponds to: driver.lem:1680-1687 (Normal_callconv case)
  -- Cerberus comment: "because of argument promotions, the char *argv[] is turned into a char **argv
  --   so two objects are allocated: an array and a pointer to that array"
  -- Cerberus: argv_ty = mk_ctype_pointer no_qualifiers pointer_to_char
  let argvMval := pointerMval charPtrTy argvArrayPtr
  let argvSize := sizeof typeEnv charPtrPtrTy
  let argvAlign := alignof typeEnv charPtrPtrTy
  let argvPtr ← InterpM.liftMem (allocateImpl "argv" argvSize (some charPtrPtrTy) argvAlign .writable (some argvMval))

  -- Step 4: Allocate argc (signed int with value = number of args)
  -- Corresponds to: driver.lem:1674-1678
  -- Cerberus: let number_of_args = integerFromNat (List.length args_mem_val_tys) in
  -- Cerberus: argc_mem_val = Mem.integer_mval (Ctype.Signed Ctype.Int_) number_of_args
  let argc := args.length
  let argcMval := integerValueMval (.signed .int_) ⟨argc, .none⟩
  let argcSize := sizeof typeEnv signedIntTy
  let argcAlign := alignof typeEnv signedIntTy
  let argcPtr ← InterpM.liftMem (allocateImpl "argc" argcSize (some signedIntTy) argcAlign .writable (some argcMval))

  -- Return (argc_cval, argv_cval) as object pointers
  -- Corresponds to: driver.lem:1689-1691
  -- Cerberus: Mem.return (Core.Vobject (Core.OVpointer argc_ptr_val), Core.Vobject (Core.OVpointer argv_ptr_val))
  let argcVal := Value.object (.pointer argcPtr)
  let argvVal := Value.object (.pointer argvPtr)
  pure (argcVal, argvVal)

/-- Get main function's parameter count.
    Corresponds to: pattern match in driver.lem:1736-1737
    ```lem
    match params with
      | [(argc_sym, _); (argv_sym, _)] -> (* 2-arg main *)
      | [] -> (* 0-arg main, handled elsewhere *)
    ```
    Returns Some n if main is a Proc/Fun with n parameters, None otherwise. -/
def getMainParamCount (file : File) : Option Nat := do
  let mainSym ← file.main
  let (_, decl) ← file.funs.find? fun (s, _) => s == mainSym
  match decl with
  | .proc _ _ _ params _ => some params.length
  | .fun_ _ params _ => some params.length
  | _ => none

/-- Initialize thread state for running main.
    Corresponds to: driver.lem:1710-1860 (drive function, main setup portion)

    Cerberus structure (driver.lem:1717-1830):
    ```lem
    match post_globals_dr_st.core_file.Core.main with
      | Just sym -> ND.return sym
      | Nothing -> ND.kill (DErr_other "no startup function")
    end >>= fun main_sym ->
    match Map.lookup main_sym funs with
      | Just (Core.Proc loc _ _ params e) ->
          match params with
            | [(argc_sym, _); (argv_sym, _)] ->
                prepare_main_args ... >>= fun (argc_cval, argv_cval) ->
                (* add argc/argv to env *)
            | [] -> (* no args case *)
          ...
          update_thread_state tid0 <| arena= expr; stack= Stack_empty; ... |>
    ```

    Audited: 2026-01-14
    Deviations:
    - Globals initialized separately in initGlobals (not inline here)
    - Uses callProc to set up environment (Cerberus manually inserts argc/argv into env)
    - No thread spawning (sequential only)

    The `args` parameter corresponds to `arg_strs` in driver.lem.
    Cerberus prepends "cmdname" to args (pipeline.ml:621,625). -/
def initThreadState (file : File) (globalEnv : List (HashMap Sym Value))
    (args : List String := ["cmdname"]) : InterpM ThreadState := do
  -- Find main function
  -- Corresponds to: driver.lem:1712-1717
  match file.main with
  | none => throw (.illformedProgram "no main function defined")
  | some mainSym =>
    -- Check if main takes argc/argv (2 params) or no params (0 params)
    -- Corresponds to: driver.lem:1736-1737 pattern match on params
    let mainArgs ← match getMainParamCount file with
      | some 0 => pure []
      | some 2 => do
        -- Corresponds to: driver.lem:1812 prepare_main_args call
        -- Cerberus: prepare_main_args loc callconv tid0 main_sym arg_strs argc_sym argv_sym
        let (argcVal, argvVal) ← prepareMainArgs args
        pure [argcVal, argvVal]
      | some n => throw (.illformedProgram s!"main has {n} parameters, expected 0 or 2")
      | none => throw (.illformedProgram "could not determine main parameter count")

    -- Set up procedure call with args
    -- Corresponds to: driver.lem:1814-1830 (adding argc/argv to env)
    match callProc file mainSym mainArgs with
    | .ok (resolvedSym, (procEnv, body)) =>
      -- Merge global env with procedure env
      -- Corresponds to: driver.lem:1817-1827 env setup
      let combinedEnv := match globalEnv with
        | [] => [procEnv]
        | baseEnv :: rest => procEnv :: baseEnv :: rest
      -- Corresponds to: driver.lem:1849-1857 update_thread_state
      -- Use resolvedSym (not mainSym) so Erun can find labels in allLabeledConts
      pure {
        arena := body
        stack := .cons (some resolvedSym) [] .empty
        env := combinedEnv
        currentProc := some resolvedSym
      }
    | .error err => throw err

end CerbLean.Semantics
