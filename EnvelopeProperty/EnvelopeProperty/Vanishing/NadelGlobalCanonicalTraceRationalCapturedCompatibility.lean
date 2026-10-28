import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRationalCoreFactor
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRationalCapturedStatement

/-! # The same original rational differential compatibility

The actual checked captured statement and the checked native core are each
elaborated without an expected proof type. Their original proposition data
are retained, and ordinary Eq.mpr supplies the proof. Its public type is
inferred from this ordinary proof; the Lean kernel still checks the entire
application. No original field trace, generic canonical map, finite cover,
instance data or result certificate is reconstructed or added.

Frozen providers: original Rational f439e16b; original Differential 3f552e8d;
original opaque-map CoreFactor 2330f85c; captured statement 99f932e1.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private def capturedCompatibilityProof (readback core : Lean.Syntax) :
    Lean.Elab.Term.TermElabM Lean.Expr := do
  let hbody ← Lean.Elab.Term.elabTerm readback none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let hbody ← Lean.instantiateMVars hbody
  let hbodyType ← Lean.instantiateMVars (← Lean.Meta.inferType hbody)
  unless hbodyType.isAppOfArity ``Eq 3 do
    throwError "expected the checked original statement readback equality"
  let .const name _ := hbody.consumeMData.getAppFn.consumeMData |
    throwError "expected the original captured statement application"
  unless name == ``rational_differential_statement_captured_body do
    throwError "expected the same checked original captured statement"
  let args := hbodyType.getAppArgs
  let P := args[1]!
  let Pbody := args[2]!
  unless ← Lean.Meta.isProp P do throwError "the original statement is not Prop"
  unless ← Lean.Meta.isProp Pbody do throwError "the captured original body is not Prop"
  let pSort ← Lean.instantiateMVars (← Lean.Meta.inferType P)
  let bodySort ← Lean.instantiateMVars (← Lean.Meta.inferType Pbody)
  unless pSort.consumeMData == Lean.mkSort Lean.Level.zero &&
      bodySort.consumeMData == Lean.mkSort Lean.Level.zero do
    throwError "the original statement and captured body must have sort zero"
  let hcore ← Lean.Elab.Term.elabTerm core none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let hcore ← Lean.instantiateMVars hcore
  if hbody.hasMVar || hcore.hasMVar then
    throwError "an original actual application has unresolved metavariables"
  return Lean.mkAppN (Lean.mkConst ``Eq.mpr [Lean.Level.zero]) #[P, Pbody, hbody, hcore]

elab "capturedRationalCompatibilityType%(" readback:term ", " core:term ")" : term => do
  Lean.Meta.inferType (← capturedCompatibilityProof readback core)

elab "capturedRationalCompatibilityProof%(" readback:term ", " core:term ")" : term =>
  capturedCompatibilityProof readback core

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      Scheme.Modules.tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "γ" => X.fromSpecStalk (genericPoint X)
local notation "pη" => pullback.fst π γ
local notation "qη" => pullback.snd π γ
local notation "ωX" => canonicalLineSheaf f n
local notation "ωY" => canonicalLineSheaf (π ≫ f) n

include hL hD f hG hRows hm hfield

/-- The SAME entire original pushed canonical differential composed with the
SAME whole original rational trace equals the independently defined original
pulled-line trace. All finite, SNC and generic canonical data are original. -/
theorem differential_comp_genericRationalCanonicalTrace_captured :
    capturedRationalCompatibilityType%(
      (rational_differential_statement_captured_body
        F n L m σ hL hD f hG hRows hm hfield),
      (let _instFinite : IsFinite π :=
        (finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield).1;
      native_rational_differential_core_factor
        (X := X) (Y := normalizedScheme (OriginalData.data F n L m σ)) (k := k) f π n
        (originalGenericCanonicalIso F n L m σ hL hD f hG hRows hm hfield).hom
        (originalGenericCanonicalIso_differential F n L m σ hL hD f hG hRows hm hfield))) :=
  capturedRationalCompatibilityProof%(
    (rational_differential_statement_captured_body
        F n L m σ hL hD f hG hRows hm hfield),
    (let _instFinite : IsFinite π :=
        (finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield).1;
      native_rational_differential_core_factor
        (X := X) (Y := normalizedScheme (OriginalData.data F n L m σ)) (k := k) f π n
        (originalGenericCanonicalIso F n L m σ hL hD f hG hRows hm hfield).hom
        (originalGenericCanonicalIso_differential F n L m σ hL hD f hG hRows hm hfield)))

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
