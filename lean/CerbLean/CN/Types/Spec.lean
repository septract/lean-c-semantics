/-
  CN Function Specifications
  Corresponds to: cn/lib/argumentTypes.ml and cn/lib/logicalReturnTypes.ml

  Function specifications in CN consist of:
  - Preconditions (requires): what the function expects
  - Postconditions (ensures): what the function guarantees

  Each consists of a sequence of clauses:
  - Resource clauses: `take v = Owned<T>(p)` - ownership transfer
  - Constraint clauses: `x > 0` - pure assertions

  Audited: 2025-01-17 against cn/lib/argumentTypes.ml, logicalReturnTypes.ml
  Deviations: Simplified for minimal subset
-/

import CerbLean.CN.Types.Resource

namespace CerbLean.CN.Types

open CerbLean.Core (Sym Loc)

/-! ## Specification Clauses

A clause is either:
- A resource binding: `take v = Resource(...)` - binds a value from memory
- A constraint: pure assertion that must hold
-/

/-- A clause in a CN specification
    This is a simplified representation for our minimal subset.
    Full CN has more complex clause types in ArgumentTypes.t and LogicalReturnTypes.t -/
inductive Clause where
  /-- Resource binding: `take <name> = <resource>` -/
  | resource (name : Sym) (resource : Resource)
  /-- Pure constraint assertion -/
  | constraint (assertion : IndexTerm)
  deriving Inhabited

/-! ## Function Specifications

Corresponds to the structure of CN function contracts:
```c
int foo(int *p)
/*@ requires take v = Owned<int>(p);
             v >= 0;
    ensures take v2 = Owned<int>(p);
            v2 == v + 1;
            return == v2; @*/
```
-/

/-- Precondition (requires clause)
    Corresponds to ArgumentTypes in cn/lib/argumentTypes.ml -/
structure Precondition where
  /-- List of clauses in the precondition -/
  clauses : List Clause
  deriving Inhabited

/-- Postcondition (ensures clause)
    Corresponds to LogicalReturnTypes in cn/lib/logicalReturnTypes.ml -/
structure Postcondition where
  /-- List of clauses in the postcondition -/
  clauses : List Clause
  deriving Inhabited

/-! ## Substitution for Clauses and Postconditions

Corresponds to: LRT.subst in cn/lib/logicalReturnTypes.ml
Used to substitute the return symbol with the actual return value.
-/

/-- Substitute in a clause -/
def Clause.subst (σ : Subst) : Clause → Clause
  | .resource n r => .resource n r  -- TODO: subst in resource if needed
  | .constraint assertion => .constraint (assertion.subst σ)

/-- Substitute in a postcondition.
    Corresponds to: LRT.subst in logicalReturnTypes.ml -/
def Postcondition.subst (σ : Subst) (post : Postcondition) : Postcondition :=
  { clauses := post.clauses.map (Clause.subst σ) }

/-- Complete function specification
    Combines precondition and postcondition.

    Corresponds to: RT.Computational in cn/lib/returnTypes.ml
    The return symbol is created fresh during parsing and used for
    `return` references in the postcondition. During type checking,
    this symbol is substituted with the actual return value.

    Audited: 2026-01-27 against cn/lib/returnTypes.ml, core_to_mucore.ml:1164 -/
structure FunctionSpec where
  /-- Symbol for the return value, used in postcondition constraints.
      This is created fresh during parsing and resolved when `return`
      appears in the ensures clause.
      Corresponds to: ret_s in core_to_mucore.ml line 1164 -/
  returnSym : Sym
  /-- Precondition (requires) -/
  requires : Precondition
  /-- Postcondition (ensures) -/
  ensures : Postcondition
  /-- Whether the function is marked as trusted (no verification) -/
  trusted : Bool := false
  deriving Inhabited

/-! ## Raw CN Annotation

Before parsing, CN annotations are raw text extracted from magic comments.
This structure holds the raw annotation along with location information.
-/

/-- Raw CN annotation text from source code
    This is what we extract from the JSON before parsing -/
structure RawAnnotation where
  /-- Source location of the annotation -/
  loc : Loc
  /-- Raw text of the annotation -/
  text : String
  deriving Repr, Inhabited

/-- Function with its CN annotations (raw, unparsed) -/
structure FunctionAnnotations where
  /-- Symbol of the function -/
  sym : Sym
  /-- List of raw CN annotations -/
  annotations : List RawAnnotation
  deriving Repr, Inhabited

end CerbLean.CN.Types
