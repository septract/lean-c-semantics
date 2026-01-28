# muCore Transformation Plan

**Date:** 2026-01-28
**Status:** Proposal
**Author:** Claude (with user guidance)

## Overview

This document outlines a plan to properly handle the Core → muCore transformation that CN requires, while keeping our interpreter working on raw Core (matching Cerberus).

## Background

### The Problem

CN works on **muCore**, a transformed version of Core IR where:
- `Esave` nodes are extracted into a separate label map
- `Esave` is replaced with `Erun` in the body
- Return continuations are explicitly marked

Our implementation currently:
- Parses raw Core from Cerberus JSON export
- Runs the interpreter on raw Core (correct - matches Cerberus)
- Runs CN type checking on raw Core (incorrect - CN expects muCore)

This causes issues like the return value showing `a_526` instead of the actual return value, because:
- Raw Core: `run ret_523(VALUE); ...; save ret_523 (a_526 := default) in pure(a_526)`
- The `save` defines a continuation, `run` calls it with the actual return value
- But our CPS-style checker continues past `run` and reaches `pure(a_526)`

### How Cerberus/CN Handle This

1. **Cerberus interpreter** (`core_run.lem`): Works on raw Core
   - `Esave`: Evaluates default args, binds parameters, enters body
   - `Erun`: Looks up label in dynamic `labeled` map, jumps to continuation

2. **CN type checker** (`core_to_mucore.ml`, `check.ml`): Works on muCore
   - Transformation extracts saves into `mi_label_defs` map
   - Body has `Esave` replaced with `Erun`
   - Return labels marked as `Mi_Return` (terminal, uninhabited return type)

## Proposed Architecture

### Key Design Decision: One AST with Predicates

Rather than creating two separate AST types (RawCore and MuCore), we use:
- **Single Core AST** (as we have now)
- **Predicates** to characterize well-formedness: `isRawCore`, `isMuCore`
- **Wrapper types** where needed for API clarity

This approach:
- Avoids code duplication
- Makes the transformation theorem cleaner: `transform e = e' ∧ isRawCore e → isMuCore e'`
- Allows sharing infrastructure (substitution, pretty-printing, etc.)
- Matches our verification goals (proving equivalence, not runtime safety)

### Pipeline

```
                                    ┌─────────────────────────┐
                                    │                         │
C source → Cerberus → Core JSON → Lean Parser → Core AST ────┤
                                                   │          │
                                                   │          │
                                    ┌──────────────┘          │
                                    │                         │
                                    ▼                         ▼
                            ┌──────────────┐         ┌──────────────┐
                            │ Interpreter  │         │  Transform   │
                            │ (raw Core)   │         │ (extract     │
                            │              │         │  labels)     │
                            └──────────────┘         └──────────────┘
                                                            │
                                                            ▼
                                                    ┌──────────────┐
                                                    │ CN Type      │
                                                    │ Checker      │
                                                    │ (muCore +    │
                                                    │  LabelDefs)  │
                                                    └──────────────┘
```

## Detailed Design

### 1. Well-Formedness Predicates

```lean
/-- An expression is "raw Core" if Erun only appears inside Esave bodies -/
def isRawCore : Expr → Prop := ...

/-- An expression is "muCore" if it contains no Esave nodes -/
def isMuCore : Expr → Prop := ...

/-- A Core file is raw if all function bodies are raw -/
def File.isRawCore (f : File) : Prop := ...

/-- A muCore procedure: transformed body + extracted labels -/
structure MuProc where
  body : AExpr
  labels : LabelDefs
  h_body : isMuCore body.expr
```

### 2. Label Definitions Structure

Matching `milicore.ml`:

```lean
/-- A labeled continuation (non-return) -/
structure LabelInfo where
  loc : Loc
  /-- C-level parameter types (for CN's logical typing) -/
  cParams : List (Option Sym × (Ctype × PassByValueOrPointer))
  /-- Core-level parameters -/
  params : List (Sym × BaseType)
  /-- Continuation body -/
  body : AExpr
  /-- Original annotations -/
  annots : List Annot

/-- A label definition: either a return point or a regular label -/
inductive LabelDef where
  | return_ : Loc → LabelDef
  | label : LabelInfo → LabelDef

/-- Map from label symbol to its definition -/
abbrev LabelDefs := Std.HashMap Sym LabelDef
```

### 3. Transformation Functions

#### 3.1 Collect Saves

Corresponds to `Core_aux.m_collect_saves`:

```lean
/-- Collect all Esave nodes from an expression into a LabelDefs map.
    Recursively processes save bodies to find nested saves. -/
def collectSaves (e : AExpr) : LabelDefs := ...
```

#### 3.2 Remove Saves

Corresponds to `milicore.remove_save`:

```lean
/-- Replace all Esave nodes with Erun nodes.
    Esave(sym, ty, [(s₁,bt₁,pe₁), ...], body) → Erun(sym, [pe₁, ...])

    Note: This discards the body - it's already captured in LabelDefs. -/
def removeSave (e : AExpr) : AExpr := ...
```

#### 3.3 Transform Procedure

Corresponds to `milicore.core_to_micore__funmap_decl`:

```lean
/-- Transform a raw Core procedure to muCore form.
    Returns the transformed body and extracted label definitions. -/
def transformProc (body : AExpr) (annots : List Annot) : MuProc :=
  let labels := collectSaves body
  let body' := removeSave body
  { body := body', labels := labels, h_body := ... }
```

### 4. Return Label Detection

CN uses annotations to detect return labels, not naming conventions:

```lean
/-- Check if annotations indicate this is a return continuation -/
def Annot.isReturn (annots : List Annot) : Bool :=
  annots.any fun a => match a with
    | .label .return_ => true
    | _ => false
```

We need to ensure our parser captures the `LAreturn` annotation from Cerberus.

### 5. Updated CN Type Checker

The type checker changes to work on muCore:

```lean
/-- Check a muCore expression with label definitions available -/
def checkMuExprK (labels : LabelDefs) (e : AExpr) (k : IndexTerm → TypingM Unit) : TypingM Unit :=
  match e.expr with
  | .run label args =>
    match labels.get? label with
    | some (.return_ _) =>
      -- Return label: this is terminal, the argument IS the return value
      if h : args.length = 1 then
        checkPexprK args[0] fun returnVal =>
          -- Pass return value to continuation (for postcondition checking)
          k returnVal
      else
        TypingM.throw "return label expects exactly one argument"
    | some (.label info) =>
      -- Regular label: check args match params, then check label body
      checkLabelCall labels info args k
    | none =>
      TypingM.throw s!"unknown label: {label}"

  -- No Esave case needed - they've been removed
  | ... => ...
```

### 6. Interpreter (No Changes Needed)

The interpreter continues to work on raw Core. It already handles `Esave` and `Erun` correctly by:
- Building `LabeledContinuations` map at procedure entry
- Looking up labels dynamically on `Erun`

This matches Cerberus's `core_run.lem` behavior.

## Implementation Plan

### Phase 1: Infrastructure

1. **Add LabelDef types** to `CerbLean/Core/`
   - `LabelInfo` structure
   - `LabelDef` inductive
   - `LabelDefs` type alias

2. **Add well-formedness predicates**
   - `isRawCore` predicate on `Expr`
   - `isMuCore` predicate on `Expr`
   - Basic lemmas (decidability, etc.)

3. **Ensure annotation parsing**
   - Verify `LAreturn` annotation is parsed from JSON
   - Add `Annot.isReturn` helper

### Phase 2: Transformation

4. **Implement `collectSaves`**
   - Walk expression tree
   - Collect `Esave` nodes into map
   - Handle nested saves (saves inside save bodies)
   - Detect return labels via annotation

5. **Implement `removeSave`**
   - Walk expression tree
   - Replace `Esave` with `Erun`
   - Preserve all other structure

6. **Implement `transformProc`**
   - Combine collection and removal
   - Package into `MuProc` structure

### Phase 3: CN Type Checker Updates

7. **Update `TypingState`**
   - Add `labels : LabelDefs` field
   - Add accessors

8. **Update expression checking**
   - Remove inline `Esave` handling
   - Update `Erun` to use label lookup
   - Handle return labels as terminal

9. **Update function checking entry point**
   - Transform procedure before checking
   - Pass `LabelDefs` to checker

### Phase 4: Testing and Validation

10. **Unit tests for transformation**
    - Test `collectSaves` extracts all saves
    - Test `removeSave` eliminates all saves
    - Test return label detection

11. **Integration tests**
    - Verify existing CN tests still pass
    - Verify return value is correct in postconditions
    - Test `tests/cn/006-pure-constraint.c` specifically

### Phase 5: Documentation and Cleanup

12. **Audit comments**
    - Document correspondence to `milicore.ml`
    - Document correspondence to `core_to_mucore.ml`

13. **Update CLAUDE.md**
    - Document the transformation pipeline
    - Document when raw Core vs muCore is used

## Soundness Considerations

### Transformation Correctness

We should eventually prove (or at least state):

```lean
/-- The transformation preserves execution semantics -/
theorem transform_preserves_semantics (e : AExpr) (h : isRawCore e.expr) :
    ∀ env, eval (transformProc e).body env = eval e env
```

This justifies using CN verification results on muCore to conclude properties of raw Core execution.

### Current Pragmatic Approach

For now, we trust the transformation matches Cerberus's `milicore.ml` exactly. The transformation is:
- Simple (just extraction and replacement)
- Well-understood (used in production CN)
- Auditable (we can compare line-by-line with OCaml)

## Open Questions

1. **Nested functions**: Do we need to handle saves inside nested function definitions? (Probably not for initial implementation)

2. **Loop labels**: How do loop break/continue labels interact with this? (CN inlines these separately in `milicore_label_inline.ml`)

3. **Annotation completeness**: Does our JSON export include all annotations needed for return detection?

## References

- `cerberus/ocaml_frontend/milicore.ml` - Core → muCore transformation
- `cerberus/ocaml_frontend/milicore_label_inline.ml` - Label inlining
- `cerberus/frontend/model/core_run.lem` - Cerberus interpreter (raw Core)
- `tmp/cn/lib/core_to_mucore.ml` - CN's muCore processing
- `tmp/cn/lib/check.ml` - CN type checker (works on muCore)
