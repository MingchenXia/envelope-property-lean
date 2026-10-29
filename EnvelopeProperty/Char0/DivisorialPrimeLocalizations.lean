/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.ValuativeMultiplierIdeal
import EnvelopeProperty.Algebra.NormalDVR
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Actual prime-localization DVR subalgebras in the original function field

The actual canonical localization image retains the literal original field,
source inclusion, fraction field and essentially finite-type structure.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (E : Subalgebra k K) [IsFractionRing E K] (P : Ideal E) [P.IsPrime]

/-- The actual prime localization of the actual source, as a literal subalgebra
of its original fraction field over the original ground field. -/
def primeLocalizationSubalgebra : Subalgebra k K :=
  (Localization.subalgebra K P.primeCompl P.primeCompl_le_nonZeroDivisors).restrictScalars k

/-- The actual localization image contains every original source element. -/
theorem le_primeLocalizationSubalgebra : E ≤ primeLocalizationSubalgebra E P := by
  intro x hx
  exact (Localization.subalgebra K P.primeCompl P.primeCompl_le_nonZeroDivisors).algebraMap_mem ⟨x, hx⟩

/-- The literal original-source inclusion is the actual prime localization map. -/
theorem isLocalization_primeLocalizationSubalgebra :
    letI : Algebra E (primeLocalizationSubalgebra E P) :=
      (Subalgebra.inclusion (le_primeLocalizationSubalgebra E P)).toAlgebra
    IsLocalization P.primeCompl (primeLocalizationSubalgebra E P) := by
  exact inferInstanceAs (IsLocalization P.primeCompl
    (Localization.subalgebra K P.primeCompl P.primeCompl_le_nonZeroDivisors))

/-- The actual canonical prime-localization image has the original actual fraction field. -/
theorem isFractionRing_primeLocalizationSubalgebra :
    IsFractionRing (primeLocalizationSubalgebra E P) K := by
  exact inferInstanceAs (IsFractionRing
    (Localization.subalgebra K P.primeCompl P.primeCompl_le_nonZeroDivisors) K)

/-- The actual prime localization is canonically isomorphic to its literal image,
commuting with the original source ring map. -/
def primeLocalizationAlgEquiv :
    letI : Algebra E (primeLocalizationSubalgebra E P) :=
      (Subalgebra.inclusion (le_primeLocalizationSubalgebra E P)).toAlgebra
    Localization.AtPrime P ≃ₐ[E] primeLocalizationSubalgebra E P := by
  let _ : Algebra E (primeLocalizationSubalgebra E P) :=
    (Subalgebra.inclusion (le_primeLocalizationSubalgebra E P)).toAlgebra
  let := isLocalization_primeLocalizationSubalgebra E P
  exact IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) (primeLocalizationSubalgebra E P)

/-- The literal image of an actual DVR prime localization is itself an actual DVR. -/
theorem isDiscreteValuationRing_primeLocalizationSubalgebra
    [IsDiscreteValuationRing (Localization.AtPrime P)] :
    IsDiscreteValuationRing (primeLocalizationSubalgebra E P) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (primeLocalizationAlgEquiv E P)

/-- The actual prime-localization image is essentially of finite type over the
original ground field whenever the actual source is. -/
theorem essFiniteType_primeLocalizationSubalgebra [Algebra.EssFiniteType k E] :
    Algebra.EssFiniteType k (primeLocalizationSubalgebra E P) := by
  let _ : Algebra E (primeLocalizationSubalgebra E P) :=
    (Subalgebra.inclusion (le_primeLocalizationSubalgebra E P)).toAlgebra
  have : IsScalarTower k E (primeLocalizationSubalgebra E P) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := isLocalization_primeLocalizationSubalgebra E P
  let := Algebra.EssFiniteType.of_isLocalization (primeLocalizationSubalgebra E P) P.primeCompl
  exact Algebra.EssFiniteType.comp k E (primeLocalizationSubalgebra E P)

/-- A principal-ideal minimal prime in an actual normal Noetherian source gives
an actual divisorial DVR inside the original actual function field. -/
theorem isDiscreteValuationRing_primeLocalizationSubalgebra_of_minimalPrimes
    [IsNoetherianRing E] [IsIntegrallyClosed E] {g : E} (hg : g ≠ 0)
    (hP : P ∈ (span {g}).minimalPrimes) :
    IsDiscreteValuationRing (primeLocalizationSubalgebra E P) := by
  have : IsDiscreteValuationRing (Localization.AtPrime P) :=
    isDiscreteValuationRing_localization_of_mem_minimalPrimes hg hP
  exact isDiscreteValuationRing_primeLocalizationSubalgebra E P

/-- Divisibility of original source functions is unchanged by passing from the
abstract prime localization to its actual literal function-field image. -/
theorem dvd_in_primeLocalizationSubalgebra_iff (f g : E) :
    letI : Algebra E (primeLocalizationSubalgebra E P) :=
      (Subalgebra.inclusion (le_primeLocalizationSubalgebra E P)).toAlgebra
    algebraMap E (primeLocalizationSubalgebra E P) f ∣
      algebraMap E (primeLocalizationSubalgebra E P) g ↔
        algebraMap E (Localization.AtPrime P) f ∣ algebraMap E (Localization.AtPrime P) g := by
  let _ : Algebra E (primeLocalizationSubalgebra E P) :=
    (Subalgebra.inclusion (le_primeLocalizationSubalgebra E P)).toAlgebra
  rw [← (primeLocalizationAlgEquiv E P).commutes f,
    ← (primeLocalizationAlgEquiv E P).commutes g]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(primeLocalizationAlgEquiv E P).symm a, ?_⟩
    apply (primeLocalizationAlgEquiv E P).injective
    rw [map_mul, AlgEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨a, ha⟩
    exact ⟨primeLocalizationAlgEquiv E P a, by rw [← map_mul, ha]⟩

end EnvelopeProperty.Char0
