/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Actual fraction rings from original algebraic coefficient denominators

For an injective algebraic extension of domains, actual nonzero coefficient
images are cofinal among nonzero divisors. The original fraction-ring algebra
map is therefore the actual coefficient localization. The literal localization
comparison retains every original element and fraction. No integral, finite,
separable, normal or generic-comparison certificate is required.
-/

open scoped nonZeroDivisors
noncomputable section
namespace EnvelopeProperty.AlgebraicFraction
variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [Algebra.IsAlgebraic A B]

/-- Original nonzero coefficient denominators are genuine nonzero divisors and are cofinal by actual divisibility. -/
theorem coefficient_denominators (hinj : Function.Injective (algebraMap A B)) :
    Algebra.algebraMapSubmonoid B A⁰ ≤ B⁰ ∧
      ∀ b ∈ B⁰, ∃ a ∈ Algebra.algebraMapSubmonoid B A⁰, b ∣ a := by
  constructor
  · exact map_le_nonZeroDivisors_of_injective _ hinj le_rfl
  · intro b hb
    obtain ⟨a, ha, hdvd⟩ := (show IsAlgebraic A b from Algebra.IsAlgebraic.isAlgebraic b).exists_nonzero_dvd hb
    exact ⟨algebraMap A B a, ⟨a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩, hdvd⟩

/-- The two genuine localization properties agree for the specified original algebra map. -/
theorem isFractionRing_iff_coefficientLocalization
    (L : Type*) [CommRing L] [Algebra B L]
    (hinj : Function.Injective (algebraMap A B)) :
    IsFractionRing B L ↔ IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L := by
  obtain ⟨hle, hcofinal⟩ := coefficient_denominators hinj
  exact (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid B A⁰) B⁰ hle hcofinal).symm

/-- The genuine original fraction ring is a coefficient localization without altering its original map. -/
theorem fraction_isLocalization
    (L : Type*) [CommRing L] [Algebra B L] [IsFractionRing B L]
    (hinj : Function.Injective (algebraMap A B)) :
    IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
  (isFractionRing_iff_coefficientLocalization L hinj).mp inferInstance

/-- The literal original coefficient localization has a canonical whole algebra equivalence with the true original fraction ring. -/
def coefficientLocalizationEquiv
    (L : Type*) [CommRing L] [Algebra B L] [IsFractionRing B L]
    (hinj : Function.Injective (algebraMap A B)) :
    Localization (Algebra.algebraMapSubmonoid B A⁰) ≃ₐ[B] L := by
  let := fraction_isLocalization L hinj
  exact IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B A⁰) _ _

/-- Every original ring element survives the actual generic comparison. -/
theorem coefficientLocalizationEquiv_algebraMap
    (L : Type*) [CommRing L] [Algebra B L] [IsFractionRing B L]
    (hinj : Function.Injective (algebraMap A B)) (b : B) :
    coefficientLocalizationEquiv L hinj
      (algebraMap B (Localization (Algebra.algebraMapSubmonoid B A⁰)) b) =
      algebraMap B L b :=
  (coefficientLocalizationEquiv L hinj).commutes b

/-- Every entire original numerator and actual coefficient denominator is preserved. -/
theorem coefficientLocalizationEquiv_mk'
    (L : Type*) [CommRing L] [Algebra B L] [IsFractionRing B L]
    (hinj : Function.Injective (algebraMap A B))
    (b : B) (s : Algebra.algebraMapSubmonoid B A⁰) :
    coefficientLocalizationEquiv L hinj
      (IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid B A⁰)) b s) =
      letI := fraction_isLocalization L hinj
      IsLocalization.mk' L b s := by
  let := fraction_isLocalization L hinj
  exact IsLocalization.algEquiv_mk' b s

end EnvelopeProperty.AlgebraicFraction
