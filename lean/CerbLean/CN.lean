/-
  CN Types for Separation Logic Specifications

  This module provides Lean types corresponding to CN's specification language.
  CN is a verification tool built on top of Cerberus that adds separation-logic
  refinement types to C programs.

  Import this module to get access to all CN types and functionality.

  Module structure:
  - Types/: Core type definitions (BaseType, IndexTerm, Resource, Spec)
  - TypeChecking/: Type checking and verification
  - Semantics/: Formal semantics and theorems
  - Parser: CN annotation parser
  - PrettyPrint: Pretty-printer for CN specs

  Reference: https://github.com/rems-project/cn
-/

import CerbLean.CN.Types
import CerbLean.CN.Parser
import CerbLean.CN.PrettyPrint
import CerbLean.CN.Semantics
import CerbLean.CN.TypeChecking
