/-
  CN Types Module

  Aggregates all CN type definitions:
  - Base: Base types (Bool, Integer, Loc, etc.)
  - Term: Index terms (constants, operators, expressions)
  - Constraint: Logical constraints for verification
  - Resource: Predicates and resources for separation logic
  - Spec: Function specifications (pre/postconditions)
-/

import CerbLean.CN.Types.Base
import CerbLean.CN.Types.Term
import CerbLean.CN.Types.Constraint
import CerbLean.CN.Types.Resource
import CerbLean.CN.Types.Spec

namespace CerbLean.CN.Types

-- Re-export commonly used types at the CN.Types level
-- (They're already accessible via CerbLean.CN.Types.BaseType etc.)

end CerbLean.CN.Types
