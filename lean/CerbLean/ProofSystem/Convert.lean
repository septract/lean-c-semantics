/-
  Conversions from CN Types to SLProp

  Converts CN specification types (Resources, Clauses, Preconditions,
  Postconditions, FunctionSpecs) into separation-logic propositions (SLProp).

  This is the bridge between CN's type system representation and the
  proof system's separation-logic assertions.
-/

import CerbLean.ProofSystem.SLProp
import CerbLean.CN.Types.Spec

namespace CerbLean.ProofSystem

open CerbLean.CN.Types
open CerbLean.Core (Sym Ctype)

/-- Convert a CN resource to an SLProp.

    A resource is a request (what memory is being accessed) paired with an
    output (the value obtained). This maps to:
    - `Owned<ct>(ptr) == val` for simple ownership
    - `Pred(name, ptr, iargs) == oarg` for user-defined predicates
    - `each qp oarg` for quantified predicates (arrays/ranges) -/
def SLProp.ofResource (res : Resource) : SLProp :=
  match res.request with
  | .p predicate =>
    match predicate.name with
    | .owned (some ct) initState =>
      .owned ct initState predicate.pointer res.output.value
    | .owned none _initState =>
      -- Unresolved Owned type: make unsatisfiable rather than silently dropping.
      -- In CN, the type should have been resolved during type checking
      -- (resolution in resourceInference.ml). If we reach here, the type
      -- was never resolved — the proof obligation becomes False.
      .pure (.t (AnnotTerm.mk (.const (.bool false)) .bool default))
    | .pname name =>
      .pred name predicate.pointer predicate.iargs res.output.value
  | .q qpred =>
    .each qpred res.output.value

/-- Convert a list of CN resources to a single SLProp via separating conjunction. -/
def SLProp.ofResources (rs : List Resource) : SLProp :=
  SLProp.starAll (rs.map SLProp.ofResource)

/-- Convert clauses to SLProp preserving telescope scoping.
    Resource clauses (`take name = res`) wrap subsequent clauses in
    `SLProp.ex name ty (...)` where `name` is bound in the rest.
    Constraint clauses become pure assertions separating-conjoined with the rest.
    Let-binding clauses scope over subsequent clauses. -/
def SLProp.ofClausesScoped : List Clause → SLProp
  | [] => .emp
  | .resource name res :: rest =>
    let resSL := SLProp.ofResource res
    let restSL := SLProp.ofClausesScoped rest
    let bt := res.output.value.bt
    .ex name bt (.star resSL restSL)
  | .constraint assertion :: rest =>
    .star (.pure (.t assertion)) (SLProp.ofClausesScoped rest)
  | .letBinding name value :: rest =>
    -- Encode `let x = e; ...` as `∃x:τ. (x == e) ∗ rest`
    -- This properly scopes x over subsequent clauses.
    let bt := value.bt
    let eqTerm := AnnotTerm.mk
      (.binop .eq (AnnotTerm.mk (.sym name) bt default) value)
      .bool default
    .ex name bt (.star (.pure (.t eqTerm)) (SLProp.ofClausesScoped rest))

/-- Convert a list of CN clauses to a single SLProp via separating conjunction.

    Uses telescope scoping to preserve sequential variable bindings from
    resource and let-binding clauses. -/
def SLProp.ofClauses (clauses : List Clause) : SLProp :=
  SLProp.ofClausesScoped clauses

/-- Convert a CN precondition to an SLProp.

    A precondition is a list of clauses describing what resources the
    function requires at entry. -/
def SLProp.ofPrecondition (pre : Precondition) : SLProp :=
  SLProp.ofClauses pre.clauses

/-- Convert a CN postcondition to an SLProp.

    A postcondition is a list of clauses describing what resources the
    function guarantees at exit. -/
def SLProp.ofPostcondition (post : Postcondition) : SLProp :=
  SLProp.ofClauses post.clauses

/-- Convert a CN function specification to a pair of SLProps.

    Returns `(precondition, postcondition)` as separation-logic propositions. -/
def SLProp.ofSpec (spec : FunctionSpec) : SLProp × SLProp :=
  (SLProp.ofPrecondition spec.requires, SLProp.ofPostcondition spec.ensures)

end CerbLean.ProofSystem
