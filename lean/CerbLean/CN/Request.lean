/-
  CN Resource Requests (Separation Logic Predicates)
  Corresponds to: cn/lib/request.ml

  Resource requests represent ownership predicates in CN's separation logic.
  They describe what memory resources a function requires (in preconditions)
  or produces (in postconditions).

  Audited: 2025-01-17 against cn/lib/request.ml
  Deviations: None significant
-/

import CerbLean.CN.Terms
import CerbLean.Core.Ctype

namespace CerbLean.CN

open CerbLean.Core (Sym Ctype Loc)

/-! ## Initialization State

Corresponds to: cn/lib/request.ml lines 6-9
```ocaml
type init =
  | Init
  | Uninit
```
-/

/-- Initialization state for owned memory
    Corresponds to: init in request.ml lines 6-9
    Audited: 2025-01-17
    Deviations: None -/
inductive Init where
  /-- Memory is initialized (readable and writable) -/
  | init
  /-- Memory is uninitialized (writable only) -/
  | uninit
  deriving Repr, BEq, Inhabited, DecidableEq

/-! ## Resource Names

Corresponds to: cn/lib/request.ml lines 11-16
```ocaml
type name =
  | Owned of Sctypes.t * init
  | PName of Sym.t
```
-/

/-- Resource predicate names
    Corresponds to: name in request.ml lines 11-16
    Audited: 2025-01-17
    Deviations: None -/
inductive ResourceName where
  /-- Built-in ownership predicate: RW<ct> (init) or W<ct> (uninit) -/
  | owned (ct : Ctype) (initState : Init)
  /-- User-defined predicate by name -/
  | pname (name : Sym)
  deriving Repr, Inhabited

/-! ## Simple Predicates

Corresponds to: cn/lib/request.ml lines 41-49 (Predicate module)
```ocaml
module Predicate = struct
  type t =
    { name : name;
      pointer : IT.t;
      iargs : IT.t list
    }
```

Simple predicates represent non-quantified resource ownership:
- `Owned<int>(p)` - pointer p owns an int
- `MyPredicate(p, arg1, arg2)` - user-defined predicate
-/

/-- Simple (non-quantified) resource predicate
    Corresponds to: Predicate.t in request.ml lines 44-48
    Audited: 2025-01-17
    Deviations: None -/
structure Predicate where
  /-- The predicate name (Owned<T> or user-defined) -/
  name : ResourceName
  /-- The pointer argument -/
  pointer : IndexTerm
  /-- Additional index arguments -/
  iargs : List IndexTerm
  deriving Inhabited

/-! ## Quantified Predicates

Corresponds to: cn/lib/request.ml lines 73-83 (QPredicate module)
```ocaml
module QPredicate = struct
  type t =
    { name : name;
      pointer : IT.t;
      q : Sym.t * BaseTypes.t;
      q_loc : Locations.t;
      step : Sctypes.ctype;
      permission : IT.t;
      iargs : IT.t list
    }
```

Quantified predicates represent ownership over arrays/ranges:
- `each (i32 i; 0 <= i && i < n) { Owned<int>(p + i) }`
-/

/-- Quantified resource predicate (for arrays/ranges)
    Corresponds to: QPredicate.t in request.ml lines 74-83
    Audited: 2025-01-17
    Deviations: None -/
structure QPredicate where
  /-- The predicate name (Owned<T> or user-defined) -/
  name : ResourceName
  /-- Base pointer -/
  pointer : IndexTerm
  /-- Quantified variable (symbol and type) -/
  q : Sym × BaseType
  /-- Location of quantifier declaration -/
  qLoc : Loc
  /-- Element stride (C type for array indexing) -/
  step : Ctype
  /-- Permission guard: which indices are valid (function of q) -/
  permission : IndexTerm
  /-- Additional index arguments (functions of q) -/
  iargs : List IndexTerm
  deriving Inhabited

/-! ## Resource Requests

Corresponds to: cn/lib/request.ml lines 151-154
```ocaml
type t =
  | P of Predicate.t
  | Q of QPredicate.t
```
-/

/-- Resource request (simple or quantified)
    Corresponds to: t in request.ml lines 151-154
    Audited: 2025-01-17
    Deviations: None -/
inductive Request where
  /-- Simple predicate -/
  | p (pred : Predicate)
  /-- Quantified predicate -/
  | q (qpred : QPredicate)
  deriving Inhabited

/-! ## Resource (Request with Output)

Corresponds to: cn/lib/resource.ml lines 4-12
```ocaml
type output = O of IT.t
type predicate = Req.Predicate.t * output
type qpredicate = Req.QPredicate.t * output
type t = Req.t * output
```

A Resource is a Request paired with an output value (the value obtained
from the memory location). In `take v = Owned<int>(p)`, the output is `v`.
-/

/-- Output value from a resource
    Corresponds to: output in resource.ml line 4
    Audited: 2025-01-17
    Deviations: None -/
structure Output where
  value : IndexTerm
  deriving Inhabited

/-- Resource: request paired with output value
    Corresponds to: t in resource.ml line 12
    Audited: 2025-01-17
    Deviations: None -/
structure Resource where
  request : Request
  output : Output
  deriving Inhabited

end CerbLean.CN
