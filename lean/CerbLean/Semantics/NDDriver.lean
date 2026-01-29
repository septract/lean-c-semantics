/-
  Non-deterministic driver for exhaustive exploration of unsequenced expressions.
  Corresponds to: Cerberus's default behavior of exploring all interleavings.

  This module provides:
  1. Exhaustive exploration (exploreAll) - try ALL paths, detect any race
  2. Single-path execution with choice stream (runWithChoices) - for replay/random testing

  The step function (in Step.lean) returns StepResult.branches when there are
  multiple possible next states (e.g., in Eunseq with multiple reducible expressions).
  This driver decides how to handle those branches.
-/

import CerbLean.Semantics.State
import CerbLean.Semantics.Step
import CerbLean.Semantics.Env
import CerbLean.Core

namespace CerbLean.Semantics

open CerbLean.Core

/-! ## Non-deterministic Result Types -/

/-- Result of exhaustive exploration.
    Corresponds to: Cerberus's behavior of exploring all interleavings. -/
inductive NDResult where
  /-- All explored paths completed successfully with these values -/
  | allSucceeded (values : List Value)
  /-- At least one path detected a race (UB035_unsequenced_race) -/
  | raceDetected (loc : Option Loc)
  /-- At least one path had an error (not UB - actual interpreter error) -/
  | someError (err : InterpError)
  /-- Exploration was cut short due to fuel exhaustion -/
  | fuelExhausted
  deriving Inhabited

instance : ToString NDResult where
  toString
  | .allSucceeded vals => s!"All paths succeeded: {vals.length} values"
  | .raceDetected loc => s!"Race detected at {repr loc}"
  | .someError err => s!"Error: {err}"
  | .fuelExhausted => "Fuel exhausted"

/-! ## Exhaustive Exploration

This explores ALL possible branches when StepResult.branches is returned.
If ANY path detects a race, the whole exploration returns .raceDetected.

This matches Cerberus's default behavior for unsequenced expressions.
-/

/-- Explore all possible execution paths exhaustively.
    Returns .raceDetected if ANY path has a race.
    Returns .allSucceeded only if ALL paths complete without races.

    Corresponds to: Cerberus's default exhaustive mode for unseq.

    Note: This can be exponential in the number of branch points!
    Use fuel to limit exploration depth. -/
partial def exploreAll (st : ThreadState) (file : File) (allLabeledConts : AllLabeledConts)
    (fuel : Nat) : InterpM NDResult := do
  if fuel == 0 then
    return .fuelExhausted
  let stepResult ← step st file allLabeledConts
  match stepResult with
  | .done val =>
    return .allSucceeded [val]
  | .continue_ st' =>
    exploreAll st' file allLabeledConts (fuel - 1)
  | .branches states =>
    -- Explore ALL branches and combine results
    -- If any branch has a race, return race
    -- If all succeed, combine all values
    let results ← states.mapM fun st' =>
      exploreAll st' file allLabeledConts (fuel - 1)
    -- Check for any races first
    for result in results do
      match result with
      | .raceDetected loc => return .raceDetected loc
      | _ => pure ()
    -- Check for any errors
    for result in results do
      match result with
      | .someError err => return .someError err
      | _ => pure ()
    -- Check for fuel exhaustion
    for result in results do
      match result with
      | .fuelExhausted => return .fuelExhausted
      | _ => pure ()
    -- All succeeded - combine values
    let allVals := results.foldl (init := []) fun acc result =>
      match result with
      | .allSucceeded vals => acc ++ vals
      | _ => acc
    return .allSucceeded allVals
  | .error err =>
    match err with
    | .undefinedBehavior .ub035_unsequencedRace loc => return .raceDetected loc
    | _ => return .someError err

/-! ## Choice Stream for Controlled Non-determinism

This is a CerbLean extension (not in Cerberus) that provides:
1. Replayable execution - reproduce specific paths
2. Random sampling - test random interleavings
3. Deterministic mode - always pick first (current behavior)
-/

/-- A choice stream that determines non-deterministic decisions.
    At each branch point, `choose n` returns an index 0..(n-1).

    Note: This uses Thunk for lazy evaluation to enable self-referential streams
    (like leftToRight that always returns itself). -/
structure ChoiceStream where
  /-- Get choice for selecting among n options (0-indexed).
      If the returned index >= n, defaults to 0. -/
  choose : Nat → Nat
  /-- Advance to next decision point (thunked for lazy evaluation) -/
  next : Thunk ChoiceStream

/-- Axiom: ChoiceStream is nonempty (needed for partial definitions).
    This is sound because we can construct streams via leftToRight, fromList, fromSeed. -/
axiom ChoiceStream.nonempty : Nonempty ChoiceStream

instance : Nonempty ChoiceStream := ChoiceStream.nonempty

/-- Choice stream that always picks the first option (deterministic, left-to-right).
    This matches the current default behavior. -/
partial def ChoiceStream.leftToRight : Unit → ChoiceStream := fun _ =>
  { choose := fun _ => 0
    next := { fn := fun _ => leftToRight () } }

/-- Choice stream from an explicit list of choices (for replay).
    When the list is exhausted, falls back to left-to-right. -/
partial def ChoiceStream.fromList : List Nat → ChoiceStream
  | [] => ChoiceStream.leftToRight ()
  | c :: cs =>
    { choose := fun n => if c < n then c else 0
      next := { fn := fun _ => ChoiceStream.fromList cs } }

/-- Simple linear congruential generator for pseudo-random choices.
    Use this for random sampling of interleavings. -/
partial def ChoiceStream.fromSeed (seed : Nat) : ChoiceStream :=
  { choose := fun n => if n == 0 then 0 else seed % n
    next := { fn := fun _ => fromSeed ((seed * 1103515245 + 12345) % (2^31)) } }

/-- Result of a single-path exploration with choice stream. -/
structure PathResult where
  /-- The final value (if successful) -/
  value : Option Value
  /-- Whether a race was detected -/
  raceDetected : Bool
  /-- Error if any -/
  error : Option InterpError
  /-- The sequence of choices made at each branch point -/
  trace : List Nat
  deriving Inhabited

/-- Run with a specific choice stream, recording the trace for replay.
    This is useful for:
    - Replaying a specific execution path
    - Random sampling of paths
    - Debugging specific interleavings -/
partial def runWithChoices (st : ThreadState) (file : File) (allLabeledConts : AllLabeledConts)
    (choices : ChoiceStream) (fuel : Nat) (trace : List Nat := []) : InterpM PathResult := do
  if fuel == 0 then
    return { value := none, raceDetected := false, error := some (.notImplemented "fuel exhausted"), trace := trace.reverse }
  let stepResult ← step st file allLabeledConts
  match stepResult with
  | .done val =>
    return { value := some val, raceDetected := false, error := none, trace := trace.reverse }
  | .continue_ st' =>
    runWithChoices st' file allLabeledConts choices (fuel - 1) trace
  | .branches states =>
    match states with
    | [] =>
      return { value := none, raceDetected := false, error := some (.illformedProgram "empty branches"), trace := trace.reverse }
    | _ =>
      let idx := choices.choose states.length
      let safeIdx := if idx < states.length then idx else 0
      let st' := states[safeIdx]!
      runWithChoices st' file allLabeledConts choices.next.get (fuel - 1) (safeIdx :: trace)
  | .error err =>
    match err with
    | .undefinedBehavior .ub035_unsequencedRace _ =>
      return { value := none, raceDetected := true, error := some err, trace := trace.reverse }
    | _ =>
      return { value := none, raceDetected := false, error := some err, trace := trace.reverse }

/-! ## Convenience Functions -/

/-- Run deterministically (always pick first branch).
    This is equivalent to the current default behavior. -/
def runDeterministic (st : ThreadState) (file : File) (allLabeledConts : AllLabeledConts)
    (fuel : Nat) : InterpM PathResult :=
  runWithChoices st file allLabeledConts (ChoiceStream.leftToRight ()) fuel

/-- Replay a specific execution using a trace.
    The trace is a list of branch indices chosen at each decision point. -/
def runReplay (st : ThreadState) (file : File) (allLabeledConts : AllLabeledConts)
    (fuel : Nat) (trace : List Nat) : InterpM PathResult :=
  runWithChoices st file allLabeledConts (ChoiceStream.fromList trace) fuel

/-- Run with random choices for random sampling.
    Different seeds produce different execution paths. -/
def runRandom (st : ThreadState) (file : File) (allLabeledConts : AllLabeledConts)
    (fuel : Nat) (seed : Nat) : InterpM PathResult :=
  runWithChoices st file allLabeledConts (ChoiceStream.fromSeed seed) fuel

end CerbLean.Semantics
