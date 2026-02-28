/-
  Core Proof System — Separation Logic over Core AST

  A type system where well-typedness implies memory safety.
  Well-typed Core expressions preserve separation-logic heap invariants.

  Module structure:
  - SLProp: Separation logic propositions (ownership, pure constraints, star)
  - HasType: Typing rules (Hoare-triple-style with frame rule)
  - Models: Semantic interpretation (SLProp satisfaction on concrete heaps)
  - Convert: CN specification types → SLProp conversion
  - Soundness/: Soundness proof (well-typed → no UB)
  - Examples/: Concrete typing derivations for validation
-/

import CerbLean.ProofSystem.SLProp
import CerbLean.ProofSystem.HasType
import CerbLean.ProofSystem.Models
import CerbLean.ProofSystem.Convert
import CerbLean.ProofSystem.Soundness.Defs
import CerbLean.ProofSystem.Soundness.Pure
import CerbLean.ProofSystem.Soundness.Action
import CerbLean.ProofSystem.Soundness.Expr
import CerbLean.ProofSystem.Soundness.Main
import CerbLean.ProofSystem.Examples.ReturnLiteral
import CerbLean.ProofSystem.Examples.LoadStore
import CerbLean.ProofSystem.Examples.Loop
