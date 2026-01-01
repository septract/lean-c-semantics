/-
  Interpreter monad and core types
  Corresponds to: cerberus/frontend/model/core_run.lem

  The monad structure follows Cerberus's execution model:
  - Reader for file and type environment (immutable during execution)
  - State for memory and I/O (mutable)
  - Except for errors and undefined behavior

  Cerberus uses:
  - `core_run_state` in core_run_aux.lem:235 for global execution state
  - `Exception` monad throughout for error handling
  - `Undefined.t` for tracking undefined behavior (undefined.lem)
-/

import CToLean.Core.File
import CToLean.Memory.Concrete

namespace CToLean.Semantics

open CToLean.Core
open CToLean.Memory

/-! ## Interpreter Errors

Corresponds to: Error handling in Cerberus
- `core_run_cause` in errors.lem:48 for execution errors
- `Errors.error` for general errors
-/

/-- Interpreter error type.
    Corresponds to: core_run_cause in errors.lem:48 -/
inductive InterpError where
  | undefinedBehavior (ub : UndefinedBehavior) (loc : Option Loc)
  | memoryError (err : MemError)
  | typeError (msg : String)
  | notImplemented (feature : String)
  | illformedProgram (msg : String)
  | symbolNotFound (sym : Sym)
  | patternMatchFailed
  | returnFromSave (label : Sym) (args : List Value)
  deriving Inhabited

instance : ToString InterpError where
  toString
    | .undefinedBehavior ub loc =>
      let locStr := loc.map (s!" at {repr ·}") |>.getD ""
      s!"undefined behavior: {ub}{locStr}"
    | .memoryError err => s!"memory error: {err}"
    | .typeError msg => s!"type error: {msg}"
    | .notImplemented feat => s!"not implemented: {feat}"
    | .illformedProgram msg => s!"ill-formed program: {msg}"
    | .symbolNotFound sym => s!"symbol not found: {sym.name}"
    | .patternMatchFailed => "pattern match failed"
    | .returnFromSave label _ => s!"return via save/run: {label.name}"

/-! ## Interpreter State -/

/-- Interpreter environment (read-only) -/
structure InterpEnv where
  /-- Program being executed -/
  file : File
  /-- Type environment for sizeof/alignof -/
  typeEnv : TypeEnv
  deriving Inhabited

/-- Interpreter state (mutable) -/
structure InterpState where
  /-- Memory state -/
  memory : MemState := {}
  /-- Captured stdout -/
  stdout : String := ""
  /-- Captured stderr -/
  stderr : String := ""
  deriving Inhabited

/-! ## Interpreter Monad -/

/-- Interpreter monad: Reader (env) + State (memory, stdout) + Except (errors) -/
abbrev InterpM := ReaderT InterpEnv (StateT InterpState (Except InterpError))

namespace InterpM

/-- Get the program file -/
def getFile : InterpM File := do
  let env ← read
  pure env.file

/-- Get the type environment -/
def getTypeEnv : InterpM TypeEnv := do
  let env ← read
  pure env.typeEnv

/-- Get current memory state -/
def getMemory : InterpM MemState := do
  let st ← get
  pure st.memory

/-- Update memory state -/
def setMemory (mem : MemState) : InterpM Unit := do
  modify fun s => { s with memory := mem }

/-- Modify memory state -/
def modifyMemory (f : MemState → MemState) : InterpM Unit := do
  modify fun s => { s with memory := f s.memory }

/-- Write to stdout -/
def writeStdout (s : String) : InterpM Unit := do
  modify fun st => { st with stdout := st.stdout ++ s }

/-- Write to stderr -/
def writeStderr (s : String) : InterpM Unit := do
  modify fun st => { st with stderr := st.stderr ++ s }

/-- Throw undefined behavior error -/
def throwUB (ub : UndefinedBehavior) (loc : Option Loc := none) : InterpM α :=
  throw (.undefinedBehavior ub loc)

/-- Throw not implemented error -/
def throwNotImpl (feature : String) : InterpM α :=
  throw (.notImplemented feature)

/-- Throw type error -/
def throwTypeError (msg : String) : InterpM α :=
  throw (.typeError msg)

/-- Throw ill-formed program error -/
def throwIllformed (msg : String) : InterpM α :=
  throw (.illformedProgram msg)

/-- Lift a memory operation into the interpreter monad -/
def liftMem (m : ConcreteMemM α) : InterpM α := do
  let env ← getTypeEnv
  let st ← get
  match (m.run env).run st.memory with
  | .ok (result, newMem) =>
    setMemory newMem
    pure result
  | .error err =>
    throw (.memoryError err)

/-- Catch returnFromSave exception and extract the return value.
    This should be used at function call boundaries to catch returns via save/run. -/
def catchReturn (m : InterpM Value) : InterpM Value := do
  let interpEnv ← read
  let state ← get
  match (m.run interpEnv).run state with
  | .ok (v, newState) =>
    set newState
    pure v
  | .error (.returnFromSave _label args) =>
    -- Return via save/run - extract the value
    match args with
    | [v] => pure v
    | _ => throw (.illformedProgram "return with wrong number of arguments")
  | .error e =>
    throw e

end InterpM

/-! ## Running the Interpreter -/

/-- Run the interpreter with given file and type environment -/
def runInterpM (file : File) (typeEnv : TypeEnv) (m : InterpM α)
    (initState : InterpState := {}) : Except InterpError (α × InterpState) :=
  let env : InterpEnv := { file, typeEnv }
  (m.run env).run initState

/-- Run the interpreter, returning only the result -/
def runInterpM' (file : File) (typeEnv : TypeEnv) (m : InterpM α)
    (initState : InterpState := {}) : Except InterpError α :=
  (·.1) <$> runInterpM file typeEnv m initState

end CToLean.Semantics
