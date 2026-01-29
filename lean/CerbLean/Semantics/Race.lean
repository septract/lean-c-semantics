/-
  Race detection for unsequenced expressions
  Corresponds to: cerberus/frontend/model/core_reduction.lem:200-231

  This module implements race detection for unsequenced expressions,
  detecting UB035_unsequenced_race when memory accesses in an unseq
  expression conflict without proper sequencing.

  CRITICAL: Must match Cerberus semantics exactly.
-/

import CerbLean.Core.DynAnnot

namespace CerbLean.Semantics

open CerbLean.Core
open CerbLean.Memory

/-! ## Race Detection

Corresponds to: core_reduction.lem:200-227

Two annotations indicate a race if:
1. Their footprints overlap (at least one is a write)
2. Neither annotation is "excluded" from the other via sequencing

The exclusion mechanism works as follows:
- When a weak sequence `let weak x = e1 in e2` is evaluated, e1 gets a fresh
  exclusion ID, and e2's annotations include that ID in their exclusion set
- This means e2's accesses are sequenced after e1's, so they don't race
- Strong sequences work similarly but with positive annotations
-/

/-- Check if a single pair of annotations indicates a race.
    Corresponds to: inner logic of do_race in core_reduction.lem:202-226
    Audited: 2026-01-28
    Deviations: None -/
def checkRacePair (da1 da2 : DynAnnotation) : Bool :=
  match da1, da2 with
  | .neg id1 exclusion1 fp1, .neg id2 exclusion2 fp2 =>
    -- Both negative: race if neither excludes the other AND footprints overlap
    if exclusion2.elem id1 || exclusion1.elem id2 then
      false
    else
      fp1.overlaps fp2
  | .neg id1 _exclusion1 fp1, .pos exclusion2 fp2 =>
    -- Neg vs Pos: race if pos doesn't exclude neg AND footprints overlap
    if exclusion2.elem id1 then
      false
    else
      fp1.overlaps fp2
  | .pos exclusion1 fp1, .neg id2 _exclusion2 fp2 =>
    -- Pos vs Neg: race if pos doesn't exclude neg AND footprints overlap
    if exclusion1.elem id2 then
      false
    else
      fp1.overlaps fp2
  | .pos _exclusion1 fp1, .pos _exclusion2 fp2 =>
    -- Both positive: always check footprints (no exclusion IDs to compare)
    fp1.overlaps fp2

/-- Check if two sets of annotations indicate a race condition.
    Race occurs when ANY pair of annotations has overlapping footprints
    and neither is excluded from the other.
    Corresponds to: do_race in core_reduction.lem:200-226
    Audited: 2026-01-28
    Deviations: None -/
def doRace (xs1 xs2 : DynAnnotations) : Bool :=
  xs1.any fun da1 => xs2.any fun da2 => checkRacePair da1 da2

/-- Combine two sets of dynamic annotations.
    Corresponds to: combine_dyn_annotations in core_reduction.lem:229-231
    Audited: 2026-01-28
    Deviations: None -/
def combineDynAnnotations (xs1 xs2 : DynAnnotations) : DynAnnotations :=
  xs1 ++ xs2

/-! ## Helpers for building annotations -/

/-- Create a negative annotation for a read access -/
def mkReadAnnotNeg (id : Nat) (exclusionSet : List Nat) (base size : Nat) : DynAnnotation :=
  .neg id exclusionSet { kind := .read, base, size }

/-- Create a negative annotation for a write access -/
def mkWriteAnnotNeg (id : Nat) (exclusionSet : List Nat) (base size : Nat) : DynAnnotation :=
  .neg id exclusionSet { kind := .write, base, size }

/-- Create a positive annotation for a read access -/
def mkReadAnnotPos (exclusionSet : List Nat) (base size : Nat) : DynAnnotation :=
  .pos exclusionSet { kind := .read, base, size }

/-- Create a positive annotation for a write access -/
def mkWriteAnnotPos (exclusionSet : List Nat) (base size : Nat) : DynAnnotation :=
  .pos exclusionSet { kind := .write, base, size }

end CerbLean.Semantics
