import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-! # Genuine coefficient maps retain the SAME whole original DVR fraction valuation -/
open IsDiscreteValuationRing
noncomputable section
namespace EnvelopeProperty.DVRFractionValuationTransport
variable {R K F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field F] [Algebra R F] [IsFractionRing R F]

/-- The WHOLE native original maximal-ideal valuation commutes with genuine original fraction-field maps. -/
theorem valuation_comap (φ : K →+* F)
    (hφ : ∀ r : R, φ (algebraMap R K r) = algebraMap R F r) :
    ((maximalIdeal R).valuation F).comap φ = (maximalIdeal R).valuation K := by
  have hc (r : R) : ((maximalIdeal R).valuation F).comap φ (algebraMap R K r) =
      (maximalIdeal R).valuation K (algebraMap R K r) := by
    change (maximalIdeal R).valuation F (φ (algebraMap R K r)) = _
    rw [hφ, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  apply Valuation.ext
  intro a
  obtain ⟨r, t, ht, rfl⟩ := IsFractionRing.div_surjective R a
  simp only [map_div₀, hc]

end EnvelopeProperty.DVRFractionValuationTransport
