/-
  Effectful expression execution
  Based on cerberus/frontend/model/core_run.lem (core_thread_step)
-/

import CToLean.Semantics.Eval

namespace CToLean.Semantics

open CToLean.Core
open CToLean.Memory

/-! ## Memory Actions

Execute memory operations (create, load, store, kill).
-/

/-- Convert Value to MemValue for storing -/
def valueToMemValue (v : Value) : Option MemValue :=
  match v with
  | .object ov =>
    match ov with
    | .integer iv => some (.integer (.signed .int_) iv)
    | .floating fv => some (.floating .double fv)
    | .pointer pv => some (.pointer .void pv)
    | _ => none
  | .loaded lv =>
    match lv with
    | .specified ov =>
      match ov with
      | .integer iv => some (.integer (.signed .int_) iv)
      | .floating fv => some (.floating .double fv)
      | .pointer pv => some (.pointer .void pv)
      | _ => none
    | .unspecified ty => some (.unspecified ty)
  | _ => none

/-- Convert MemValue to Value for loading -/
def memValueToValue (mv : MemValue) : Value :=
  match mv with
  | .unspecified ty => .loaded (.unspecified ty)
  | .integer _ iv => .loaded (.specified (.integer iv))
  | .floating _ fv => .loaded (.specified (.floating fv))
  | .pointer _ pv => .loaded (.specified (.pointer pv))
  | .array elems =>
    let loadedElems := elems.map fun mv' =>
      match mv' with
      | .unspecified ty => LoadedValue.unspecified ty
      | .integer _ iv => .specified (.integer iv)
      | .floating _ fv => .specified (.floating fv)
      | .pointer _ pv => .specified (.pointer pv)
      | _ => .unspecified .void
    .object (.array loadedElems)
  | .struct_ tag members =>
    let structMembers := members.map fun (name, ty, mv') =>
      let memVal := match mv' with
        | .integer _ iv => .integer (.signed .int_) iv
        | _ => mv'
      { name, ty, value := memVal : StructMember }
    .object (.struct_ tag structMembers)
  | .union_ tag member mv' =>
    .object (.union_ tag member mv')

/-! ## Mutually Recursive Execution Functions -/

mutual

/-- Execute a memory action -/
partial def execAction (env : EvalEnv) (action : AAction) : InterpM Value := do
  match action.action with
  | .create alignExpr sizeExpr prefix_ =>
    -- Allocate local variable
    let alignVal ← evalPexpr env alignExpr
    let sizeVal ← evalPexpr env sizeExpr
    -- Extract alignment (must be integer)
    let alignInt ← match valueToInt alignVal with
      | some iv => pure iv.val.toNat
      | none => InterpM.throwTypeError "create: align must be integer"
    -- Extract size - can be integer or ctype (compute sizeof for ctype)
    let sizeInt ← match sizeVal with
      | .ctype ty =>
        let env ← InterpM.getTypeEnv
        pure (sizeof env ty)
      | _ =>
        match valueToInt sizeVal with
        | some iv => pure iv.val.toNat
        | none => InterpM.throwTypeError "create: size must be integer or ctype"
    let ptr ← InterpM.liftMem do
      allocateImpl prefix_.val sizeInt none alignInt .writable none
    pure (.object (.pointer ptr))

  | .createReadonly alignExpr sizeExpr initExpr prefix_ =>
    -- Allocate read-only memory (e.g., string literal)
    let alignVal ← evalPexpr env alignExpr
    let sizeVal ← evalPexpr env sizeExpr
    let initVal ← evalPexpr env initExpr
    match valueToInt alignVal, valueToInt sizeVal with
    | some alignIv, some sizeIv =>
      let initMem := valueToMemValue initVal
      let ptr ← InterpM.liftMem do
        allocateImpl prefix_.val sizeIv.val.toNat none alignIv.val.toNat (.readonly .ordinary) initMem
      pure (.object (.pointer ptr))
    | _, _ =>
      InterpM.throwTypeError "create_readonly requires integer align and size"

  | .alloc alignExpr sizeExpr prefix_ =>
    -- Dynamic allocation (malloc-style)
    let alignVal ← evalPexpr env alignExpr
    let sizeVal ← evalPexpr env sizeExpr
    match valueToInt alignVal, valueToInt sizeVal with
    | some alignIv, some sizeIv =>
      let ptr ← InterpM.liftMem do
        allocateImpl prefix_.val sizeIv.val.toNat none alignIv.val.toNat .writable none
      pure (.object (.pointer ptr))
    | _, _ =>
      InterpM.throwTypeError "alloc requires integer align and size"

  | .kill kind ptrExpr =>
    let ptrVal ← evalPexpr env ptrExpr
    match ptrVal with
    | .object (.pointer pv) =>
      let isDynamic := match kind with
        | .dynamic => true
        | .static _ => false
      InterpM.liftMem (killImpl isDynamic pv)
      pure .unit
    | _ =>
      InterpM.throwTypeError "kill requires pointer"

  | .store locking tyExpr ptrExpr valExpr _order =>
    let tyVal ← evalPexpr env tyExpr
    let ptrVal ← evalPexpr env ptrExpr
    let storeVal ← evalPexpr env valExpr
    match tyVal, ptrVal with
    | .ctype ty, .object (.pointer pv) =>
      match valueToMemValue storeVal with
      | some mv =>
        let _ ← InterpM.liftMem (storeImpl ty locking pv mv)
        pure .unit
      | none =>
        InterpM.throwTypeError s!"cannot convert value to memory value for store"
    | _, _ =>
      InterpM.throwTypeError "store requires ctype, pointer, and value"

  | .load tyExpr ptrExpr _order =>
    let tyVal ← evalPexpr env tyExpr
    let ptrVal ← evalPexpr env ptrExpr
    match tyVal, ptrVal with
    | .ctype ty, .object (.pointer pv) =>
      let (_, mv) ← InterpM.liftMem (loadImpl ty pv)
      pure (memValueToValue mv)
    | _, _ =>
      InterpM.throwTypeError "load requires ctype and pointer"

  | .rmw _ _ _ _ _ _ =>
    InterpM.throwNotImpl "rmw (atomic read-modify-write)"

  | .fence _ =>
    InterpM.throwNotImpl "fence"

  | .compareExchangeStrong _ _ _ _ _ _ =>
    InterpM.throwNotImpl "compare_exchange_strong"

  | .compareExchangeWeak _ _ _ _ _ _ =>
    InterpM.throwNotImpl "compare_exchange_weak"

  | .seqRmw isUpdate tyExpr ptrExpr sym valExpr =>
    -- Sequenced read-modify-write (for ++, --, +=, etc.)
    -- 1. Evaluate type and pointer
    let tyVal ← evalPexpr env tyExpr
    let ptrVal ← evalPexpr env ptrExpr
    match tyVal, ptrVal with
    | .ctype ty, .object (.pointer pv) =>
      -- 2. Load current value
      let (_, mv) ← InterpM.liftMem (loadImpl ty pv)
      let loadedVal := memValueToValue mv
      -- 3. Bind loaded value to sym and evaluate update expression
      let env' := env.bind sym loadedVal
      let newVal ← evalPexpr env' valExpr
      -- 4. Convert new value to mem value and store
      match valueToMemValue newVal with
      | some newMv =>
        let _ ← InterpM.liftMem (storeImpl ty false pv newMv)
        -- 5. Return old or new value depending on isUpdate
        if isUpdate then
          pure newVal  -- pre-increment: return new value
        else
          pure loadedVal  -- post-increment: return old value
      | none =>
        InterpM.throwTypeError "seq_rmw: cannot convert update value to memory value"
    | _, _ =>
      InterpM.throwTypeError "seq_rmw requires ctype and pointer"

/-- Execute a builtin function -/
partial def execBuiltin (sym : Sym) (args : List Value) : InterpM Value := do
  match sym.name with
  | "printf" =>
    -- Stub: just ignore arguments
    InterpM.writeStdout ""
    pure (.object (.integer { val := 0, prov := .none }))
  | "malloc" =>
    match args with
    | [sizeVal] =>
      match valueToInt sizeVal with
      | some sizeIv =>
        let ptr ← InterpM.liftMem do
          allocateImpl "malloc" sizeIv.val.toNat none 8 .writable none
        pure (.object (.pointer ptr))
      | none => InterpM.throwTypeError "malloc requires integer size"
    | _ => InterpM.throwTypeError "malloc requires one argument"
  | "free" =>
    match args with
    | [ptrVal] =>
      match ptrVal with
      | .object (.pointer pv) =>
        InterpM.liftMem (killImpl true pv)
        pure .unit
      | _ => InterpM.throwTypeError "free requires pointer"
    | _ => InterpM.throwTypeError "free requires one argument"
  | _ =>
    InterpM.throwNotImpl s!"builtin: {sym.name}"

/-- Call a procedure -/
partial def callProc (_env : EvalEnv) (sym : Sym) (args : List Value) : InterpM Value := do
  let file ← InterpM.getFile
  -- Look up in user functions (try by exact match first, then by name)
  -- Note: Name-based lookup is needed because function pointers from JSON have different symbol IDs
  let funDecl := match file.funs.find? fun (s, _) => s == sym with
                 | some d => some d
                 | none => file.funs.find? fun (s, _) => s.name == sym.name
  match funDecl with
  | some (_, .proc _loc _retTy params body) =>
    if args.length != params.length then
      InterpM.throwTypeError s!"wrong number of arguments for {sym.name}"
    let bindings := params.zip args |>.map fun ((p, _), v) => (p, v)
    -- Pre-collect all labeled continuations from the body
    let callEnv := EvalEnv.empty.bindAll bindings |>.withConts body
    execExpr callEnv body
  | some (_, .fun_ _retTy params body) =>
    if args.length != params.length then
      InterpM.throwTypeError s!"wrong number of arguments for {sym.name}"
    let bindings := params.zip args |>.map fun ((p, _), v) => (p, v)
    let callEnv := EvalEnv.empty.bindAll bindings
    evalPexpr callEnv body
  | some (_, .procDecl _loc _retTy _paramTys) =>
    InterpM.throwNotImpl s!"forward-declared proc: {sym.name}"
  | some (_, .builtinDecl _loc _retTy _paramTys) =>
    -- Built-in function
    execBuiltin sym args
  | none =>
    -- Check stdlib (also with name fallback)
    let stdlibDecl := match file.stdlib.find? fun (s, _) => s == sym with
                      | some d => some d
                      | none => file.stdlib.find? fun (s, _) => s.name == sym.name
    match stdlibDecl with
    | some (_, .proc _loc _retTy params body) =>
      if args.length != params.length then
        InterpM.throwTypeError s!"wrong number of arguments for {sym.name}"
      let bindings := params.zip args |>.map fun ((p, _), v) => (p, v)
      -- Pre-collect all labeled continuations from the body
      let callEnv := EvalEnv.empty.bindAll bindings |>.withConts body
      execExpr callEnv body
    | some (_, .fun_ _retTy params body) =>
      if args.length != params.length then
        InterpM.throwTypeError s!"wrong number of arguments for {sym.name}"
      let bindings := params.zip args |>.map fun ((p, _), v) => (p, v)
      let callEnv := EvalEnv.empty.bindAll bindings
      evalPexpr callEnv body
    | _ =>
      -- Try as builtin
      execBuiltin sym args

/-- Execute an effectful expression -/
partial def execExpr (env : EvalEnv) (expr : AExpr) : InterpM Value := do
  match expr.expr with
  | .pure pe =>
    evalPexpr env pe

  | .memop _op _args =>
    InterpM.throwNotImpl "memop"

  | .action paction =>
    execAction env paction.action

  | .case_ scrut branches =>
    let scrutVal ← evalPexpr env scrut
    let rec tryBranches : List (APattern × Expr) → InterpM Value
      | [] => throw .patternMatchFailed
      | (pat, body) :: rest =>
        match matchPattern pat scrutVal with
        | some bindings =>
          let env' := env.bindAll bindings
          execExpr env' ⟨[], body⟩
        | none => tryBranches rest
    tryBranches branches

  | .let_ pat e1 e2 =>
    let v1 ← evalPexpr env e1
    match matchPattern pat v1 with
    | some bindings =>
      let env' := env.bindAll bindings
      execExpr env' ⟨[], e2⟩
    | none => throw .patternMatchFailed

  | .if_ cond then_ else_ =>
    let condVal ← evalPexpr env cond
    match condVal with
    | .true_ => execExpr env ⟨[], then_⟩
    | .false_ => execExpr env ⟨[], else_⟩
    | _ => InterpM.throwTypeError "if condition must be boolean"

  | .sseq pat e1 e2 =>
    -- Strong sequencing: evaluate e1, bind result, evaluate e2
    let v1 ← execExpr env ⟨[], e1⟩
    match matchPattern pat v1 with
    | some bindings =>
      let env' := env.bindAll bindings
      execExpr env' ⟨[], e2⟩
    | none => throw .patternMatchFailed

  | .wseq pat e1 e2 =>
    -- Weak sequencing: same as strong for sequential execution
    let v1 ← execExpr env ⟨[], e1⟩
    match matchPattern pat v1 with
    | some bindings =>
      let env' := env.bindAll bindings
      execExpr env' ⟨[], e2⟩
    | none => throw .patternMatchFailed

  | .bound e =>
    -- Bounds marker - just evaluate inner expression
    execExpr env ⟨[], e⟩

  | .save _retSym _retTy args body =>
    -- Save: evaluate default values, bind parameters, execute body
    -- Note: continuations are pre-collected at procedure entry (see callProc)
    let env' ← args.foldlM (init := env) fun acc (sym, _, valExpr) => do
      let v ← evalPexpr acc valExpr
      pure (acc.bind sym v)
    execExpr env' ⟨[], body⟩

  | .run label argExprs =>
    -- Run: look up pre-collected continuation and execute it
    -- This is a non-local jump - we don't return to the caller
    let argVals ← argExprs.mapM (evalPexpr env)
    match env.lookupCont label with
    | none =>
      InterpM.throwIllformed s!"run: label not found: {label.name}"
    | some cont =>
      -- Bind argument values to parameters
      if argVals.length != cont.params.length then
        InterpM.throwTypeError s!"run {label.name}: wrong number of arguments"
      -- Evaluate default values and bind with provided arguments
      let env' ← cont.params.zip argVals |>.foldlM (init := env) fun acc ((sym, _ty, _), v) => do
        pure (acc.bind sym v)
      -- Execute the continuation body
      let result ← execExpr env' ⟨[], cont.body⟩
      -- Throw the result as an exception to escape the current execution context
      throw (.returnFromSave label [result])

  | .unseq es =>
    -- Unsequenced: for now, evaluate left-to-right (deterministic)
    -- This may miss some UB from sequence point violations
    let vals ← es.mapM (execExpr env ⟨[], ·⟩)
    pure (.tuple vals)

  | .nd es =>
    -- Nondeterministic choice: pick first (deterministic for testing)
    match es with
    | [] => InterpM.throwIllformed "empty nd"
    | e :: _ => execExpr env ⟨[], e⟩

  | .ccall funPtrExpr _funTyExpr argExprs =>
    -- C function call through pointer
    let funPtrVal ← evalPexpr env funPtrExpr
    let argVals ← argExprs.mapM (evalPexpr env)
    -- Extract function symbol from pointer value (can be object or loaded)
    let callFunPtr (pv : PointerValue) : InterpM Value :=
      match pv.base with
      | .function sym => callProc env sym argVals
      | _ => InterpM.throwNotImpl "indirect function call (non-function pointer)"
    match funPtrVal with
    | .object (.pointer pv) => callFunPtr pv
    | .loaded (.specified (.pointer pv)) => callFunPtr pv
    | _ =>
      InterpM.throwTypeError "ccall requires function pointer"

  | .proc name argExprs =>
    -- Direct procedure call
    let argVals ← argExprs.mapM (evalPexpr env)
    match name with
    | .sym s => callProc env s argVals
    | .impl ic => InterpM.throwNotImpl s!"impl proc: {repr ic}"

  | .par _es =>
    InterpM.throwNotImpl "par (parallel execution)"

  | .wait _tid =>
    InterpM.throwNotImpl "wait"

end

end CToLean.Semantics
