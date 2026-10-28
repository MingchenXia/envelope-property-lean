import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceOriginalLineTraceSquare
import EnvelopeProperty.AlgGeom.AdjunctionUnitTarget
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRegularPulledLine
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericCanonicalUnit
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRationalCapturedPullbackBody

/-! # Rational restriction of the same actual regular pulled-line trace

Only the original geometric cover inputs occur in the public theorem.
The original structure-trace factor supplies the scalar square inside
the proof. The rational map is the exact original stored construction.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

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
local notation "pη" => CategoryTheory.Limits.pullback.fst π γ
local notation "qη" => CategoryTheory.Limits.pullback.snd π γ
local notation "ωX" => canonicalLineSheaf f n

include hL hD f hG hRows hm hfield

/-- The original actual regular pulled-canonical trace has exactly the
original whole-generic rational restriction. Every comparison and PF
is derived internally from the original geometric cover data. -/
theorem regularPulledCanonicalTrace_rational_restriction :
    regularPulledCanonicalTrace F n L m σ hL hD f hG hRows hm hfield ≫
      genericCanonicalInclusion f n =
    genericRationalPullbackCanonicalTrace F n L m σ hL hD f hG hRows hm hfield := by
  let : IsFinite π := (finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield).1
  have h := originalGenericLineTrace_nativeRestriction π ωX (canonicalLineSheaf_isInvertible f n)
    (NadelGlobalStructureTrace.originalStructureTrace F n L m σ hL hD f hG hRows hm hfield)
    (NadelGlobalStructureTrace.originalStructureTrace_factor F n L m σ hL hD f hG hRows hm hfield)
  rw [genericCanonicalInclusion_eq_adjunction_unit f n]
  rw [genericRationalPullbackCanonicalTrace_captured_body F n L m σ hL hD f hG hRows hm hfield]
  dsimp (config := { proj := false, zetaDelta := false }) only [regularPulledCanonicalTrace]
  dsimp (config := { proj := false, zetaDelta := false }) only at h
  refine AdjunctionUnitTarget.unit_composite_explicit_target
    (pullback γ) (pushforward γ) (pullbackPushforwardAdjunction γ) _ _ ?_
  exact h
end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
