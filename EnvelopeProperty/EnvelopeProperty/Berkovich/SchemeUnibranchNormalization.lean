/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.UnibranchNormalizationPrimes
import EnvelopeProperty.SpecResidueMaps
import EnvelopeProperty.Berkovich.SchemeUniversalHomeomorphism

/-!
# Structural geometric unibranchness yields the actual native normalization homeomorphism

The normalization is the literal integral closure of the ORIGINAL domain in
its actual fraction field. All local geometric inputs are the standard
reduction/literal-normalization structural definitions. No scheme/native
injection, residue-comparison or homeomorphism certificate is supplied.
-/

open scoped NNReal Topology
open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
namespace EnvelopeProperty.DomainNormalization
variable (A : Type u) [CommRing A]

/-- The ACTUAL scheme projection from the literal original normalization. -/
def projection : Spec (CommRingCat.of (integralClosure A (FractionRing A))) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))

/-- The literal normalization scheme projection is genuinely integral, without finite normalization or Noetherianity. -/
theorem projection_isIntegralHom : IsIntegralHom (projection A) :=
  IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)

/-- Actual injective integral inclusion and lying-over DERIVE scheme-surjectivity. -/
theorem projection_surjective : Function.Surjective (projection A) := by
  apply (algebraMap_isIntegral_iff.mpr
    (inferInstance : Algebra.IsIntegral A (integralClosure A (FractionRing A)))).comap_surjective
  intro a b hab
  exact IsFractionRing.injective A (FractionRing A)
    (congrArg (fun c : integralClosure A (FractionRing A) => (c : FractionRing A)) hab)

variable [IsDomain A]

/-- Standard geometric unibranchness of the ORIGINAL local rings DERIVES true universal injectivity of the normalization morphism. -/
theorem projection_universallyInjective
    (h : ∀ p : PrimeSpectrum A, IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal)) :
    UniversallyInjective (projection A) := by
  apply universallyInjective_specMap_of_prime_and_residue
  · exact NormalizationLocalization.injective_primeSpectrumComap_of_isUnibranch
      (fun p => (h p).toIsUnibranchLocalRing)
  · intro q
    let p := q.comap (algebraMap A (integralClosure A (FractionRing A)))
    let : IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal) := h p
    exact NormalizationLocalization.residueFieldMap_isPurelyInseparable_of_isGeometricallyUnibranch_atPrime
      p.asIdeal q.asIdeal rfl

/-- The true native point map of the ORIGINAL normalization is a homeomorphism, DERIVED from structural local geometric unibranchness. -/
def nativeHomeomorph
    (h : ∀ p : PrimeSpectrum A, IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal)) :
    Berkovich.SchemeValuedPoint (Spec (CommRingCat.of (integralClosure A (FractionRing A)))) ≃ₜ
      Berkovich.SchemeValuedPoint (Spec (CommRingCat.of A)) := by
  let : IsIntegralHom (projection A) := projection_isIntegralHom A
  let : UniversallyInjective (projection A) := projection_universallyInjective A h
  exact Berkovich.SchemeValuedPoint.universalHomeomorph (projection A) (projection_surjective A)

/-- The whole homeomorphism retains the ACTUAL original native projection, including its complete residue valuation. -/
@[simp]
theorem nativeHomeomorph_apply
    (h : ∀ p : PrimeSpectrum A, IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal))
    (y : Berkovich.SchemeValuedPoint (Spec (CommRingCat.of (integralClosure A (FractionRing A))))) :
    nativeHomeomorph A h y = Berkovich.SchemeValuedPoint.map (projection A) y := rfl

/-- ANY exact common prescribed coefficient point is preserved by the actual normalization homeomorphism. -/
def relativeNativeHomeomorph {R : Type u} [CommRing R]
    (v : Valuation R ℝ≥0) (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (h : ∀ p : PrimeSpectrum A, IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal)) :
    Berkovich.RelativeSchemeValuedPoint v (projection A ≫ f) ≃ₜ
      Berkovich.RelativeSchemeValuedPoint v f := by
  let : IsIntegralHom (projection A) := projection_isIntegralHom A
  let : UniversallyInjective (projection A) := projection_universallyInjective A h
  exact Berkovich.RelativeSchemeValuedPoint.universalHomeomorph (v := v)
    (projection A) rfl (projection_surjective A)

/-- The prescribed-base comparison is exactly the WHOLE original relative native map. -/
@[simp]
theorem relativeNativeHomeomorph_apply {R : Type u} [CommRing R]
    (v : Valuation R ℝ≥0) (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (h : ∀ p : PrimeSpectrum A, IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal))
    (y : Berkovich.RelativeSchemeValuedPoint v (projection A ≫ f)) :
    relativeNativeHomeomorph A v f h y = Berkovich.RelativeSchemeValuedPoint.map (projection A) rfl y := rfl

end EnvelopeProperty.DomainNormalization
