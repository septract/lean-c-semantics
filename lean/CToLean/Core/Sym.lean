/-
  Symbols and identifiers for Core IR
  Based on cerberus/frontend/model/symbol.lem
-/

namespace CToLean.Core

/-- Symbol identifier (unique ID for variables, functions, etc.) -/
structure Sym where
  id : Nat
  name : Option String := none
  deriving Repr, BEq, Hashable, Inhabited

/-- C identifier (struct/union member names, etc.) -/
structure Identifier where
  name : String
  deriving Repr, BEq, Hashable, Inhabited

/-- Symbol prefix for allocation naming -/
structure SymPrefix where
  val : String
  deriving Repr, BEq, Inhabited

end CToLean.Core
