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

/-! ## Neg Action Transformation Helpers

When a neg action (store/load) executes, Cerberus performs a transformation that:
1. Creates a fresh exclusion ID n
2. Adds n to ALL context annotations' exclusion sets
3. The action's annotation has ID = n
4. Race check happens between action and modified context

This prevents false positives for properly sequenced code while detecting
actual races in unsequenced code.

Corresponds to: neg_action_trans in core_reduction.lem:1285-1302
-/

/-- Add an exclusion ID to a single annotation's exclusion set.
    Corresponds to: inner logic of add_exclusion in core_reduction.lem:935-940 -/
def addExclusionToAnnot (n : Nat) : DynAnnotation → DynAnnotation
  | .neg id es fp => .neg id (n :: es) fp
  | .pos es fp => .pos (n :: es) fp

/-- Add an exclusion ID to all annotations' exclusion sets.
    Corresponds to: add_exclusion in core_reduction.lem:925-944 -/
def addExclusionToAnnots (n : Nat) (annots : DynAnnotations) : DynAnnotations :=
  annots.map (addExclusionToAnnot n)

/-- Convert a neg annotation to pos, adding the neg ID to the exclusion set.
    Used when wseq completes - the neg ID becomes part of the exclusion set
    to prevent races with later operations.
    Corresponds to: dyn_annot_neg_to_pos in core_reduction.lem
    - DA_neg(Some n, es, fp) → DA_pos([n] ++ es, fp)
    - DA_neg(None, es, fp) → DA_pos(es, fp)  (shouldn't happen in practice)
    - DA_pos(es, fp) → DA_pos(es, fp) -/
def dynAnnotNegToPos : DynAnnotation → DynAnnotation
  | .neg id es fp => .pos (id :: es) fp
  | .pos es fp => .pos es fp

/-- Convert all annotations using neg-to-pos conversion.
    Used when wseq completes. -/
def dynAnnotsNegToPos (annots : DynAnnotations) : DynAnnotations :=
  annots.map dynAnnotNegToPos

/-- Check if two sets of annotations would race, ignoring exclusion sets.
    This is used for neg action race checking, where the action is conceptually
    executed with pos polarity (inside Eexcluded), so we just check footprint overlap.
    Corresponds to: pos/pos race check in Cerberus's neg action transformation unseq.

    In Cerberus, the neg action transformation:
    1. Converts the action to Pos polarity (inside Eexcluded(n, Eaction Pos ...))
    2. The Eexcluded wrapper adds n to resulting annotations
    3. Race check in the unseq is pos/pos, which just checks footprint overlap -/
def doRaceFootprintOnly (xs1 xs2 : DynAnnotations) : Bool :=
  xs1.any fun da1 =>
    xs2.any fun da2 =>
      da1.footprint.overlaps da2.footprint

end CerbLean.Semantics
