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

/-! ## Value Conversion Helpers

Corresponds to: memValueFromValue and valueFromMemValue in core_aux.lem:114-200
These convert between Core Values and Memory MemValues for load/store operations.
-/

/-- Strip atomic qualifier from a Ctype_.
    Corresponds to: unatomic_ in ctype.lem -/
def unatomic_ : Ctype_ → Ctype_
  | .atomic ty => unatomic_ ty
  | ty => ty

/-- Convert a Core Value to a MemValue for storing to memory.
    Corresponds to: memValueFromValue in core_aux.lem:137-200
    Audited: 2026-01-01
    Deviations: Simplified - doesn't handle all cases -/
partial def memValueFromValue (ty : Ctype) (v : Value) : Option MemValue :=
  let ty' := unatomic_ ty.ty
  match ty', v with
  | _, .unit => none
  | _, .true_ => none
  | _, .false_ => none
  | _, .list _ _ => none
  | _, .tuple _ => none
  | _, .ctype _ => none
  | _, .loaded (.unspecified ty'') => some (.unspecified ty'')
  | .basic (.integer ity), .object (.integer iv) => some (.integer ity iv)
  | .basic (.integer ity), .loaded (.specified (.integer iv)) => some (.integer ity iv)
  | .byte, .object (.integer iv) => some (.integer (.unsigned .ichar) iv)
  | .byte, .loaded (.specified (.integer iv)) => some (.integer (.unsigned .ichar) iv)
  | .basic (.floating fty), .object (.floating fv) => some (.floating fty fv)
  | .basic (.floating fty), .loaded (.specified (.floating fv)) => some (.floating fty fv)
  | .pointer _ refTy, .object (.pointer pv) =>
    some (.pointer { annots := [], ty := refTy } pv)
  | .pointer _ refTy, .loaded (.specified (.pointer pv)) =>
    some (.pointer { annots := [], ty := refTy } pv)
  | .array elemTy _, .loaded (.specified (.array lvs)) =>
    let elemCty : Ctype := { annots := [], ty := elemTy }
    let mvalsOpt := lvs.mapM fun lv =>
      memValueFromValue elemCty (.loaded lv)
    mvalsOpt.map MemValue.array
  | .struct_ tag, .loaded (.specified (.struct_ tag' members)) =>
    if tag == tag' then
      -- Convert StructMember list to (Identifier × Ctype × MemValue) list
      let memberList := members.map fun m => (m.name, m.ty, m.value)
      some (.struct_ tag memberList)
    else none
  | .union_ tag, .loaded (.specified (.union_ tag' ident mv)) =>
    if tag == tag' then some (.union_ tag ident mv) else none
  | _, _ => none

/-- Convert a MemValue to a Core Value after loading from memory.
    Corresponds to: valueFromMemValue in core_aux.lem:114-135
    Audited: 2026-01-01
    Deviations: Returns just the value (not the object type) -/
def valueFromMemValue (mv : MemValue) : Value :=
  match mv with
  | .unspecified ty => .loaded (.unspecified ty)
  | .integer _ity iv => .loaded (.specified (.integer iv))
  | .floating _fty fv => .loaded (.specified (.floating fv))
  | .pointer _ty pv => .loaded (.specified (.pointer pv))
  | .array elems =>
    let lvs := elems.map fun mv' =>
      match valueFromMemValue mv' with
      | .loaded lv => lv
      | .object ov => .specified ov
      | _ => .unspecified .void
    .loaded (.specified (.array lvs))
  | .struct_ tag members =>
    -- Convert (Identifier × Ctype × MemValue) list to StructMember list
    let structMembers := members.map fun (name, ty, value) =>
      { name, ty, value : StructMember }
    .loaded (.specified (.struct_ tag structMembers))
  | .union_ tag ident mv' => .loaded (.specified (.union_ tag ident mv'))

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
partial def step (st : ThreadState) (file : File) (allLabeledConts : HashMap Sym LabeledConts)
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
    -- Two-level lookup: first by procedure, then by label
    -- Corresponds to: Maybe.bind (Map.lookup proc_sym st.labeled) (Map.lookup sym)
    let procConts : Option LabeledConts := Std.HashMap.get? allLabeledConts currentProc
    match procConts.bind (fun conts => Std.HashMap.get? conts sym) with
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
  -- Corresponds to: core_action_step in core_run.lem:275-650
  | .action paction, _ =>
    let act := paction.action.action
    match act with
    -- Create: allocate memory for a typed object
    -- Corresponds to: core_run.lem:297-338 (Create case)
    | .create alignPe sizePe prefix_ =>
      let alignVal ← evalPexpr st.env alignPe
      let sizeVal ← evalPexpr st.env sizePe
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
      let alignVal ← evalPexpr st.env alignPe
      let sizeVal ← evalPexpr st.env sizePe
      let initVal ← evalPexpr st.env initPe
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
      let alignVal ← evalPexpr st.env alignPe
      let sizeVal ← evalPexpr st.env sizePe
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
      let ptrVal ← evalPexpr st.env ptrPe
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

    -- Store: store value to memory
    -- Corresponds to: core_run.lem:505-569 (Store case)
    | .store isLocking tyPe ptrPe valPe _order =>
      let tyVal ← evalPexpr st.env tyPe
      let ptrVal ← evalPexpr st.env ptrPe
      let cval ← evalPexpr st.env valPe
      match tyVal, ptrVal with
      | .ctype ty, .object (.pointer ptr) =>
        match memValueFromValue ty cval with
        | some mval =>
          let _ ← InterpM.liftMem (storeImpl ty isLocking ptr mval)
          let resultVal := Value.unit
          pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
        | none =>
          throw (.typeError s!"store: value doesn't match type")
      | .ctype ty, .loaded (.specified (.pointer ptr)) =>
        match memValueFromValue ty cval with
        | some mval =>
          let _ ← InterpM.liftMem (storeImpl ty isLocking ptr mval)
          let resultVal := Value.unit
          pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
        | none =>
          throw (.typeError s!"store: value doesn't match type")
      | _, _ =>
        throw (.typeError "store: expected ctype and pointer")

    -- Load: load value from memory
    -- Corresponds to: core_run.lem:579-612 (Load case)
    | .load tyPe ptrPe _order =>
      let tyVal ← evalPexpr st.env tyPe
      let ptrVal ← evalPexpr st.env ptrPe
      match tyVal, ptrVal with
      | .ctype ty, .object (.pointer ptr) =>
        let (_, mval) ← InterpM.liftMem (loadImpl ty ptr)
        let resultVal := valueFromMemValue mval
        pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
      | .ctype ty, .loaded (.specified (.pointer ptr)) =>
        let (_, mval) ← InterpM.liftMem (loadImpl ty ptr)
        let resultVal := valueFromMemValue mval
        pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
      | _, _ =>
        throw (.typeError "load: expected ctype and pointer")

    -- SeqRMW: sequential read-modify-write (increment/decrement)
    -- Corresponds to: core_reduction.lem:1214-1276 and driver.lem:704-714
    -- Audited: 2026-01-01
    -- Deviations: Simplified - no exclusion tracking for negative polarity
    --
    -- Algorithm (matching SeqRMWRequest2 in driver.lem:704-714):
    -- 1. Evaluate pe1 (type) and pe2 (pointer)
    -- 2. Load current value from memory: mval ← Mem.load ty ptrval
    -- 3. Bind sym to loaded value (valueFromMemValue mval) in environment
    -- 4. Evaluate pe3 (update expression) with sym bound
    -- 5. Convert result to mval': memValueFromValue ty cval3
    -- 6. Store new value: Mem.store ty false ptrval mval'
    -- 7. Return old value (if not with_forward) or new value (if with_forward)
    | .seqRmw withForward tyPe ptrPe sym valPe =>
      let tyVal ← evalPexpr st.env tyPe
      let ptrVal ← evalPexpr st.env ptrPe
      match tyVal, ptrVal with
      | .ctype ty, .object (.pointer ptr) =>
        -- Step 2: Load current value
        let (_, mval) ← InterpM.liftMem (loadImpl ty ptr)
        -- Step 3: Bind sym to loaded value in environment
        -- Corresponds to: Map.insert sym (snd (Caux.valueFromMemValue mval)) x :: xs
        let loadedVal := valueFromMemValue mval
        let newEnv := bindInEnv sym loadedVal st.env
        -- Step 4: Evaluate update expression with sym bound
        let cval3 ← evalPexpr newEnv valPe
        -- Step 5: Convert to MemValue
        -- Corresponds to: memValueFromValue (Ctype.Ctype [] (Ctype.unatomic_ ty)) cval3
        let ty' : Ctype := { annots := [], ty := unatomic_ ty.ty }
        match memValueFromValue ty' cval3 with
        | some mval' =>
          -- Step 6: Store new value
          let _ ← InterpM.liftMem (storeImpl ty false ptr mval')
          -- Step 7: Return appropriate value
          -- Corresponds to: Caux.valueFromMemValue (if with_forward then mval' else mval)
          let resultVal := if withForward then valueFromMemValue mval' else loadedVal
          pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
        | none =>
          throw (.typeError "seq_rmw: update expression doesn't match lvalue type")
      | .ctype ty, .loaded (.specified (.pointer ptr)) =>
        -- Same as above but pointer is loaded value
        let (_, mval) ← InterpM.liftMem (loadImpl ty ptr)
        let loadedVal := valueFromMemValue mval
        let newEnv := bindInEnv sym loadedVal st.env
        let cval3 ← evalPexpr newEnv valPe
        let ty' : Ctype := { annots := [], ty := unatomic_ ty.ty }
        match memValueFromValue ty' cval3 with
        | some mval' =>
          let _ ← InterpM.liftMem (storeImpl ty false ptr mval')
          let resultVal := if withForward then valueFromMemValue mval' else loadedVal
          pure (.continue_ { st with arena := mkValueExpr arenaAnnots resultVal })
        | none =>
          throw (.typeError "seq_rmw: update expression doesn't match lvalue type")
      | _, _ =>
        throw (.typeError "seq_rmw: expected ctype and pointer")

    -- Fence, RMW, CompareExchange - not implemented yet
    | .fence _ =>
      throw (.notImplemented "fence")
    | .rmw _ _ _ _ _ _ =>
      throw (.notImplemented "rmw")
    | .compareExchangeStrong _ _ _ _ _ _ =>
      throw (.notImplemented "compare_exchange_strong")
    | .compareExchangeWeak _ _ _ _ _ _ =>
      throw (.notImplemented "compare_exchange_weak")

  -- Eccall: C function call through pointer
  -- Corresponds to: core_run.lem:926-999
  | .ccall funPtr _funTy args, sk =>
    -- Step 1: Evaluate function pointer expression
    let funPtrVal ← evalPexpr st.env funPtr
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
    let argVals ← args.mapM (evalPexpr st.env)
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
    | .ok (procEnv, body) =>
      -- Push new stack frame with procedure environment
      let newStack := Stack.pushEmptyCont (some funSym) sk
      pure (.continue_ { st with
        arena := body
        stack := newStack
        env := procEnv :: st.env  -- Push new scope
        currentProc := some funSym
      })
    | .error err => throw err

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
  -- Corresponds to: memop_exec in driver.lem:720-870
  -- Pattern matches on memop kind and evaluates accordingly
  | .memop op args, _ =>
    -- First evaluate all argument pexprs to values
    let argVals ← args.mapM (evalPexpr st.env)
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
    | .intFromPtr, [.ctype _refTy, .ctype (.basic (.integer ity)), .object (.pointer p)] =>
      let ival ← InterpM.liftMem (MemoryOps.intfromptr _refTy ity p)
      pure (.object (.integer ival))
    | .ptrFromInt, [.ctype (.basic (.integer ity)), .ctype refTy, .object (.integer ival)] =>
      let pval ← InterpM.liftMem (MemoryOps.ptrfromint ity refTy ival)
      pure (.object (.pointer pval))

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

    -- Varargs - not yet implemented
    | .vaStart, _ => throw (.notImplemented "va_start")
    | .vaCopy, _ => throw (.notImplemented "va_copy")
    | .vaArg, _ => throw (.notImplemented "va_arg")
    | .vaEnd, _ => throw (.notImplemented "va_end")

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

/-! ## Driver Loop

Run steps until done or error.
-/

/-- Run the interpreter until completion or error.
    Returns the final value or an error. -/
partial def runUntilDone (st : ThreadState) (file : File) (allLabeledConts : HashMap Sym LabeledConts)
    (fuel : Nat := 1000000) : InterpM Value := do
  if fuel == 0 then
    throw (.illformedProgram "execution fuel exhausted")
  match ← step st file allLabeledConts with
  | .done v => pure v
  | .continue_ st' => runUntilDone st' file allLabeledConts (fuel - 1)
  | .error err => throw err

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
partial def runExprToValue (expr : AExpr) (env : List (HashMap Sym Value))
    (file : File) (fuel : Nat := 100000) : InterpM Value := do
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

/-- Initialize thread state for running main.
    Corresponds to the initial state setup in Cerberus driver.lem.
    Audited: 2026-01-01
    Deviations: Simplified - globals initialized inline -/
def initThreadState (file : File) (globalEnv : List (HashMap Sym Value))
    : Except InterpError ThreadState := do
  -- Find main function
  match file.main with
  | none => throw (.illformedProgram "no main function defined")
  | some mainSym =>
    match callProc file mainSym [] with
    | .ok (procEnv, body) =>
      -- Merge global env with procedure env
      -- Global env is the base, procedure env is pushed on top
      let combinedEnv := match globalEnv with
        | [] => [procEnv]
        | baseEnv :: rest => procEnv :: baseEnv :: rest
      pure {
        arena := body
        stack := .cons (some mainSym) [] .empty
        env := combinedEnv
        currentProc := some mainSym
      }
    | .error err => throw err

end CToLean.Semantics
