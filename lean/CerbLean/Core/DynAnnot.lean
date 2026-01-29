/-
  Dynamic annotations for unsequenced expression race detection
  Corresponds to: cerberus/frontend/model/core.lem:300-312

  These annotations track memory footprints during evaluation of unsequenced
  expressions to detect race conditions (UB035_unsequenced_race).

  CRITICAL: Must match Cerberus semantics exactly.
-/

import CerbLean.Memory.Types

namespace CerbLean.Core

open CerbLean.Memory

/-! ## Dynamic Annotation

Corresponds to: core.lem:300-302
```lem
type dyn_annotation =
  | DA_neg of nat * list nat * Mem.footprint (* the nat is its unique "exclusion ID", the list is its "exclusion set" *)
  | DA_pos of list nat * Mem.footprint (* the list of nat is its "exclusion set" *)
```

Dynamic annotations are used to track memory accesses during evaluation of unsequenced
expressions. They enable race detection by recording which memory locations are accessed
and which operations are "excluded" from racing with each other due to sequencing.

- **DA_neg (negative polarity)**: Created by weak sequencing (Ewseq). Has a unique ID
  that can be added to other annotations' exclusion sets to prevent false race detection.

- **DA_pos (positive polarity)**: Created by strong sequencing (Esseq). Has only an
  exclusion set, no unique ID.

The exclusion sets implement the C standard's sequencing rules:
- Operations within the same sequence point don't race
- The comma operator creates sequence points
- Function call arguments are sequenced before the call
-/

/-- Dynamic annotation for tracking memory accesses in unsequenced expressions.
    Corresponds to: dyn_annotation in core.lem:300-302
    Audited: 2026-01-28
    Deviations: None -/
inductive DynAnnotation where
  /-- Negative polarity annotation (from weak sequencing).
      - `id`: Unique exclusion ID for this annotation
      - `exclusionSet`: IDs that this annotation is sequenced after
      - `footprint`: Memory region accessed -/
  | neg (id : Nat) (exclusionSet : List Nat) (footprint : Footprint)
  /-- Positive polarity annotation (from strong sequencing).
      - `exclusionSet`: IDs that this annotation is sequenced after
      - `footprint`: Memory region accessed -/
  | pos (exclusionSet : List Nat) (footprint : Footprint)
  deriving Repr, BEq, Inhabited

/-- List of dynamic annotations.
    Corresponds to: list dyn_annotation in Cerberus -/
abbrev DynAnnotations := List DynAnnotation

/-- Empty dynamic annotations -/
def DynAnnotations.empty : DynAnnotations := []

/-- Get the footprint from a dynamic annotation -/
def DynAnnotation.footprint : DynAnnotation → Footprint
  | .neg _ _ fp => fp
  | .pos _ fp => fp

/-- Get the exclusion set from a dynamic annotation -/
def DynAnnotation.exclusionSet : DynAnnotation → List Nat
  | .neg _ excl _ => excl
  | .pos excl _ => excl

/-- Get the exclusion ID if this is a negative annotation -/
def DynAnnotation.exclusionId? : DynAnnotation → Option Nat
  | .neg id _ _ => some id
  | .pos _ _ => none

instance : ToString DynAnnotation where
  toString
    | .neg id excl fp => s!"DA_neg({id}, {excl}, {repr fp})"
    | .pos excl fp => s!"DA_pos({excl}, {repr fp})"

end CerbLean.Core
