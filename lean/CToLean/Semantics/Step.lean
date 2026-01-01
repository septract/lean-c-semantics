/-
  Small-step execution semantics
  Corresponds to: cerberus/frontend/model/core_run.lem (core_thread_step2)

  CRITICAL: This file must match Cerberus semantics EXACTLY.
  Each case is documented with its Cerberus correspondence.
-/

import CToLean.Semantics.Monad
import CToLean.Semantics.State
import CToLean.Semantics.Env
import CToLean.Semantics.Eval
import CToLean.Memory.Interface
import Std.Data.HashMap

namespace CToLean.Semantics

open CToLean.Core
open CToLean.Memory
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

/-- Look up a procedure and return (env, body).
    Corresponds to: call_proc in core_run.lem:30-70
    Audited: 2025-01-01
    Deviations: We don't handle core_extern (external symbol remapping) -/
def callProc (file : File) (psym : Sym) (cvals : List Value)
    : Except InterpError (HashMap Sym Value × AExpr) := do
  -- Look up in stdlib first, then funs (matches Cerberus order)
  let procOpt := match file.stdlib.find? fun (s, _) => s == psym with
    | some x => some x
    | none => file.funs.find? fun (s, _) => s == psym
  match procOpt with
  | some (_, .proc _loc _markerEnv _retTy params body) =>
    if params.length != cvals.length then
      throw (.illformedProgram s!"calling procedure '{psym.name}' with wrong number of args")
    -- Build environment: env = foldl2 (fun acc (sym, _) cval -> Map.insert sym cval acc) Map.empty params cvals
    let emptyMap : HashMap Sym Value := {}
    let env := params.zip cvals |>.foldl (fun acc ((sym, _), cval) => acc.insert sym cval) emptyMap
    pure (env, body)
  | some (_, .fun_ _ _ _) =>
    throw (.illformedProgram s!"call_proc: '{psym.name}' is a fun, not a proc")
  | some (_, .procDecl _ _ _) =>
    throw (.illformedProgram s!"call_proc: '{psym.name}' is a procDecl (forward declaration)")
  | some (_, .builtinDecl _ _ _) =>
    throw (.illformedProgram s!"call_proc: '{psym.name}' is a builtinDecl")
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
partial def step (st : ThreadState) (file : File) (labeledConts : LabeledConts)
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
      let cval ← evalPexpr st.env pe
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
        -- Apply continuation to wrap the result
        let wrappedExpr := applyContinuation parentCont (mkValueExpr arenaAnnots cval)
        pure (.continue_ { st with
          arena := wrappedExpr
          stack := .cons parentProcOpt [] parentStack
          env := env'
        })

      -- Non-empty continuation -> apply it
      -- Corresponds to: core_run.lem:1599-1605
      | _, _ =>
        let wrappedExpr := applyContinuation cont (mkValueExpr arenaAnnots cval)
        pure (.continue_ { st with
          arena := wrappedExpr
          stack := .cons currentProcOpt [] parent
        })

    | none =>
      -- Need to evaluate the pure expression
      let cval ← evalPexpr st.env pe
      pure (.continue_ { st with arena := mkValueExpr arenaAnnots cval })

  -- Elet pat pe1 e2: evaluate pe1, bind pattern, continue with e2
  -- Corresponds to: core_run.lem:837-865
  | .let_ pat pe1 e2, _ =>
    let cval ← evalPexpr st.env pe1
    match st.updateEnv pat cval with
    | some st' => pure (.continue_ { st' with arena := e2 })
    | none => throw .patternMatchFailed

  -- Eif: evaluate condition and branch
  -- Corresponds to: core_run.lem:870-924
  | .if_ cond then_ else_, .cons _ _ _ =>
    let condVal ← evalPexpr st.env cond
    match condVal with
    | .true_ => pure (.continue_ { st with arena := then_ })
    | .false_ => pure (.continue_ { st with arena := else_ })
    | _ => throw (.typeError "if condition must be boolean")

  | .if_ _ _ _, .empty =>
    throw (.illformedProgram "reached empty stack with Eif")

  -- Ecase: evaluate scrutinee and match branches
  -- Corresponds to: core_run.lem:785-835
  | .case_ scrut branches, _ =>
    let scrutVal ← evalPexpr st.env scrut
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
  -- Corresponds to: core_run.lem:1408-1445
  | .wseq pat e1 e2, .cons currentProcOpt cont parent =>
    match valueFromExpr e1 with
    | some cval =>
      -- e1 is a value, bind and continue with e2
      match st.updateEnv pat cval with
      | some st' => pure (.continue_ { st' with arena := e2 })
      | none => throw .patternMatchFailed
    | none =>
      match e1.expr with
      | .pure pe1 =>
        -- Evaluate pure expression
        let cval ← evalPexpr st.env pe1
        match st.updateEnv pat cval with
        | some st' => pure (.continue_ { st' with arena := e2 })
        | none => throw .patternMatchFailed
      | _ =>
        -- Focus on e1, push continuation
        let contElem := ContElem.wseq arenaAnnots pat e2
        pure (.continue_ { st with
          arena := e1
          stack := .cons currentProcOpt (contElem :: cont) parent
        })

  | .wseq _ _ _, .empty =>
    throw (.illformedProgram "reached empty stack with Ewseq")

  -- Esseq pat e1 e2: strong sequencing
  -- Corresponds to: core_run.lem:1450-1489
  | .sseq pat e1 e2, .cons currentProcOpt cont parent =>
    match valueFromExpr e1 with
    | some cval =>
      -- e1 is a value, bind and continue with e2
      match st.updateEnv pat cval with
      | some st' => pure (.continue_ { st' with arena := e2 })
      | none => throw .patternMatchFailed
    | none =>
      match e1.expr with
      | .pure pe1 =>
        -- Evaluate pure expression
        let cval ← evalPexpr st.env pe1
        match st.updateEnv pat cval with
        | some st' => pure (.continue_ { st' with arena := e2 })
        | none => throw .patternMatchFailed
      | _ =>
        -- Focus on e1, push continuation
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
      let cval ← evalPexpr acc.env pe
      pure (acc.bindSym sym cval)
    pure (.continue_ { st' with arena := body })

  -- Erun: jump to labeled continuation
  -- Corresponds to: core_run.lem:1509-1530
  | .run sym pes, .cons (some currentProc) _cont parent =>
    match labeledConts[sym]? with
    | none =>
      throw (.illformedProgram s!"Erun couldn't resolve label: '{sym.name}' for procedure '{currentProc.name}'")
    | some labeledCont =>
      -- Evaluate arguments
      let cvals ← pes.mapM (evalPexpr st.env)
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
      let cvals ← pes.mapM (evalPexpr st.env)
      -- Look up and call procedure
      match callProc file psym cvals with
      | .ok (procEnv, body) =>
        -- Push new stack frame with procedure environment
        let newStack := Stack.pushEmptyCont (some psym) sk
        pure (.continue_ { st with
          arena := body
          stack := newStack
          env := procEnv :: st.env  -- Push new scope
          currentProc := some psym
        })
      | .error err => throw err
    | .impl ic =>
      throw (.notImplemented s!"impl proc: {repr ic}")

  -- Eaction: execute memory action
  -- For now, throw not implemented - will be expanded
  | .action _paction, _ =>
    throw (.notImplemented "Eaction (memory operations)")

  -- Eccall: C function call through pointer
  | .ccall _funPtr _funTy _args, _ =>
    throw (.notImplemented "Eccall")

  -- Ebound: bounds marker, just unwrap
  -- Corresponds to: core_run.lem:1643-1649
  | .bound e, _ =>
    pure (.continue_ { st with arena := e })

  -- End: nondeterministic choice - pick first (deterministic for testing)
  -- Corresponds to: core_run.lem:1618-1623
  | .nd es, _ =>
    match es with
    | [] => throw (.illformedProgram "empty nd")
    | e :: _ => pure (.continue_ { st with arena := e })

  -- Eunseq: unsequenced evaluation - evaluate left to right (deterministic)
  -- Corresponds to: core_run.lem:1369-1402
  | .unseq es, .cons currentProcOpt cont parent =>
    match es with
    | [] => throw (.illformedProgram "empty unseq")
    | [e] => pure (.continue_ { st with arena := e })
    | _ =>
      -- First check if all elements are pure (Epure)
      -- Corresponds to: core_run.lem:1373-1377
      match toPures es with
      | some pes =>
        -- All elements are pure, convert to tuple
        let tupleExpr : AExpr := { annots := arenaAnnots, expr := .pure (mkTuplePexpr pes) }
        pure (.continue_ { st with arena := tupleExpr })
      | none =>
        -- Not all pure, focus on first non-pure element
        -- For deterministic execution, we go left to right
        match es.findIdx? (fun e => toPure e |>.isNone) with
        | some idx =>
          let e := es[idx]!
          let done := es.take idx
          let remaining := es.drop (idx + 1)
          let contElem := ContElem.unseq arenaAnnots done remaining
          pure (.continue_ { st with
            arena := e
            stack := .cons currentProcOpt (contElem :: cont) parent
          })
        | none =>
          -- Should not happen if toPures returned none
          throw (.illformedProgram "unseq: inconsistent state")

  | .unseq _, .empty =>
    throw (.illformedProgram "reached empty stack with Eunseq")

  -- Memop case
  | .memop _ _, _ =>
    throw (.notImplemented "memop")

  -- Concurrency cases
  | .par _, _ =>
    throw (.notImplemented "par (parallel execution)")

  | .wait _, _ =>
    throw (.notImplemented "wait")

/-! ## Driver Loop

Run steps until done or error.
-/

/-- Run the interpreter until completion or error.
    Returns the final value or an error. -/
partial def runUntilDone (st : ThreadState) (file : File) (labeledConts : LabeledConts)
    (fuel : Nat := 1000000) : InterpM Value := do
  if fuel == 0 then
    throw (.illformedProgram "execution fuel exhausted")
  match ← step st file labeledConts with
  | .done v => pure v
  | .continue_ st' => runUntilDone st' file labeledConts (fuel - 1)
  | .error err => throw err

/-- Initialize thread state for running main.
    Corresponds to the initial state setup in Cerberus. -/
def initThreadState (file : File) : Except InterpError ThreadState := do
  -- Find main function
  match file.main with
  | none => throw (.illformedProgram "no main function defined")
  | some mainSym =>
    match callProc file mainSym [] with
    | .ok (procEnv, body) =>
      pure {
        arena := body
        stack := .cons (some mainSym) [] .empty
        env := [procEnv]
        currentProc := some mainSym
      }
    | .error err => throw err

end CToLean.Semantics
