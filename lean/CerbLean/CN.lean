/-
  CN Types for Separation Logic Specifications

  This module provides Lean types corresponding to CN's specification language.
  CN is a verification tool built on top of Cerberus that adds separation-logic
  refinement types to C programs.

  Import this module to get access to all CN types.

  Key types:
  - BaseType: CN's type system for specifications
  - IndexTerm: Expression language for specifications
  - Request/Resource: Separation logic ownership predicates
  - FunctionSpec: Function contracts (requires/ensures)

  Reference: https://github.com/rems-project/cn
-/

import CerbLean.CN.BaseTypes
import CerbLean.CN.Terms
import CerbLean.CN.LogicalConstraints
import CerbLean.CN.Request
import CerbLean.CN.Spec
import CerbLean.CN.Parser
import CerbLean.CN.PrettyPrint
import CerbLean.CN.Semantics
import CerbLean.CN.TypeChecking
