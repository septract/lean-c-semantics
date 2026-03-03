/-
  Infrastructure Lemmas for PureHasType Soundness

  Lemmas about evalPexpr needed for the main PureHasType.soundness proof:
  annotation irrelevance, fuel monotonicity, state preservation,
  env lookup equivalence, and type-preservation of arithmetic helpers.

  Created: 2026-03-02
-/

import CerbLean.ProofSystem.Soundness.Defs
import CerbLean.Semantics.Eval

namespace CerbLean.ProofSystem.Soundness

open CerbLean.Core (Sym Ctype Identifier APexpr Pexpr Annots Binop Iop Value
                     IntegerType File PointerValue)
open CerbLean.CN.Types (BaseType)
open CerbLean.CN.Semantics (Valuation)
open CerbLean.Semantics (InterpM InterpState InterpEnv InterpError
                          evalPexpr evalBinop convertInt wrapIntOp
                          lookupEnv bindAllInEnv matchPattern mkAPexpr)
open CerbLean.Memory (TypeEnv)
open CerbLean.ProofSystem (Ctx valueHasType intTypeToBaseType opResultType
                            CNBaseType)
open Std (HashMap)

/-! ## L1: Annotation Irrelevance

    evalPexpr only inspects `pe.expr`, never `pe.annots` or `pe.ty`.
    This lets us bridge PureHasType (which uses `⟨annots, coreTy, e⟩`)
    with recursive evalPexpr calls (which use `mkAPexpr e = ⟨[], none, e⟩`). -/

/-- evalPexpr ignores annotations and coreTy, matching only on `.expr`. -/
theorem evalPexpr_annot_irrelevant
    {fuel : Nat} {env : List (HashMap Sym Value)}
    {a₁ a₂ : Annots} {t₁ t₂ : Option CerbLean.Core.BaseType} {e : Pexpr} :
    evalPexpr fuel env ⟨a₁, t₁, e⟩ = evalPexpr fuel env ⟨a₂, t₂, e⟩ := by
  sorry

/-! ## L2: Fuel Monotonicity

    If evalPexpr succeeds with fuel₁, it succeeds with fuel₂ ≥ fuel₁
    and returns the same result. -/

/-- evalPexpr is monotone in fuel: more fuel gives the same result. -/
theorem evalPexpr_fuel_mono
    {fuel₁ fuel₂ : Nat} {env : List (HashMap Sym Value)}
    {pe : APexpr} {r : InterpEnv} {s : InterpState}
    {v : Value} {s' : InterpState}
    (hle : fuel₁ ≤ fuel₂)
    (hok : ((evalPexpr fuel₁ env pe).run r).run s = .ok (v, s')) :
    ((evalPexpr fuel₂ env pe).run r).run s = .ok (v, s') := by
  sorry

/-! ## L3: State Preservation

    Pure expression evaluation does not modify the interpreter state's
    memory. (It may update stdout/stderr/nextExclusionId, but NOT memory.) -/

/-- evalPexpr preserves memory state. -/
theorem evalPexpr_preserves_memory
    {fuel : Nat} {env : List (HashMap Sym Value)}
    {pe : APexpr} {r : InterpEnv} {s : InterpState}
    {v : Value} {s' : InterpState}
    (hok : ((evalPexpr fuel env pe).run r).run s = .ok (v, s')) :
    s'.memory = s.memory := by
  sorry

/-! ## L4: Environment Lookup Equivalence

    The soundness definitions use `envLookup` (List.findSome?-based)
    while the interpreter uses `lookupEnv` (manual recursion).
    These are extensionally equal. -/

/-- envLookup and lookupEnv agree on all inputs. -/
theorem envLookup_eq_lookupEnv
    {env : List (HashMap Sym Value)} {s : Sym} :
    envLookup env s = lookupEnv s env := by
  sorry

/-! ## L5: evalBinop Type Preservation

    If both operands are well-typed and the operator's result type is
    defined, evalBinop produces a value of that type. -/

/-- evalBinop preserves types according to opResultType. -/
theorem evalBinop_preserves_type
    {binop : Binop} {v₁ v₂ : Value} {τ₁ τ₂ τ : CNBaseType}
    {r : InterpEnv} {s : InterpState}
    {v : Value} {s' : InterpState}
    (hv₁ : valueHasType v₁ τ₁) (hv₂ : valueHasType v₂ τ₂)
    (hop : opResultType binop τ₁ τ₂ = some τ)
    (hok : ((evalBinop binop v₁ v₂).run r).run s = .ok (v, s')) :
    valueHasType v τ := by
  sorry

/-! ## L6: convertInt Type Preservation

    convertInt always produces `.object (.integer ...)` which satisfies
    `valueHasType _ (intTypeToBaseType ity)`. -/

/-- convertInt produces a value of the target integer type. -/
theorem convertInt_preserves_type
    {ity : IntegerType} {v : Value}
    {r : InterpEnv} {s : InterpState}
    {v' : Value} {s' : InterpState}
    (hok : ((convertInt ity v).run r).run s = .ok (v', s')) :
    valueHasType v' (intTypeToBaseType ity) := by
  sorry

/-! ## L7: wrapIntOp Type Preservation

    wrapIntOp always produces `.object (.integer ...)` which satisfies
    `valueHasType _ (intTypeToBaseType ity)`. -/

/-- wrapIntOp produces a value of the target integer type. -/
theorem wrapIntOp_preserves_type
    {ity : IntegerType} {iop : Iop} {v₁ v₂ : Value}
    {r : InterpEnv} {s : InterpState}
    {v' : Value} {s' : InterpState}
    (hok : ((wrapIntOp ity iop v₁ v₂).run r).run s = .ok (v', s')) :
    valueHasType v' (intTypeToBaseType ity) := by
  sorry

/-! ## L8: EnvCompat → lookupEnv Success

    If the typing context says a variable has type τ, and the environment
    is compatible with the context, then the interpreter can look up
    that variable and the result is well-typed. -/

/-- EnvCompat guarantees lookupEnv succeeds for context variables. -/
theorem EnvCompat_lookup
    {env : List (HashMap Sym Value)} {Γ : Ctx} {ρ : Valuation}
    {s : Sym} {τ : CNBaseType}
    (henv : EnvCompat env Γ.vars ρ)
    (hlook : Γ.lookupVar s = some τ) :
    ∃ v, lookupEnv s env = some v ∧ valueHasType v τ := by
  sorry

/-! ## L9: EnvCompat Extension

    Adding a well-typed binding to both the environment and context
    preserves EnvCompat. Used in the `let_` case. -/

/-- EnvCompat is preserved by extending both env and context with a
    well-typed binding. -/
theorem EnvCompat_bind
    {env : List (HashMap Sym Value)} {Γ : Ctx} {ρ : Valuation}
    {s : Sym} {v : Value} {τ : CNBaseType}
    (henv : EnvCompat env Γ.vars ρ)
    (hvt : valueHasType v τ) :
    ∀ ρ', ValuationExtends ρ ρ' →
      (∃ hv, ρ'.lookup s = some hv ∧ (∀ τ', valueHasType v τ' → CerbLean.ProofSystem.heapValueHasType hv τ')) →
      EnvCompat (bindAllInEnv [(s, v)] env) (Γ.addVar s τ).vars ρ' := by
  sorry

/-! ## L10: matchPattern Produces Valid Bindings

    If matchPattern succeeds, the bindings are consistent with the
    scrutinee value. For base patterns `(some x) bty`, the binding
    is `[(x, v)]`. -/

/-- matchPattern with a base pattern `(some x) bty` always returns `[(x, v)]`. -/
theorem matchPattern_base_some
    {patAnnots : Annots} {x : Sym} {bty : CerbLean.Core.BaseType} {v : Value} :
    matchPattern ⟨patAnnots, .base (some x) bty⟩ v = some [(x, v)] := by
  sorry

/-! ## L11: evalPexpr on .ctype Values

    If evalPexpr succeeds and valueHasType v .ctype, then v = .ctype _ .
    Needed for the isScalar/isInteger/isSigned/isUnsigned cases. -/

/-- A value with type .ctype is a .ctype constructor. -/
theorem valueHasType_ctype_form {v : Value}
    (h : valueHasType v .ctype) :
    ∃ ct, v = .ctype ct := by
  sorry

/-! ## L12: evalPexpr on .bool Values

    If valueHasType v .bool, then v = .true_ or v = .false_.
    Needed for if_, not_ cases. -/

/-- A value with type .bool is either .true_ or .false_.
    NOTE: This is incorrect as stated — `.loaded (.unspecified ct)` with
    `ctypeToBaseType ct = some .bool` also satisfies `valueHasType v .bool`.
    Need to tighten `valueHasType` or add "interpreter-compatible" qualifier. -/
theorem valueHasType_bool_form {v : Value}
    (h : valueHasType v .bool) :
    v = .true_ ∨ v = .false_ := by
  sorry

/-! ## L13: evalPexpr on .loc Values

    If valueHasType v .loc, then v is a pointer (.loaded or .object form).
    Needed for arrayShift/memberShift cases. -/

/-- A value with type .loc is a pointer. -/
theorem valueHasType_loc_form {v : Value}
    (h : valueHasType v .loc) :
    (∃ pv, v = .loaded (.specified (.pointer pv))) ∨
    (∃ pv, v = .object (.pointer pv)) := by
  sorry

end CerbLean.ProofSystem.Soundness
