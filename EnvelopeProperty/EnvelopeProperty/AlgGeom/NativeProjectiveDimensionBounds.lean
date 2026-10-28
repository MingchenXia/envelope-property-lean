import EnvelopeProperty.AlgGeom.IntegralSchemeDimension
import EnvelopeProperty.AlgGeom.ProjectiveFactorizationRingIso

/-! # Finite whole dimension of the actual projective scheme -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u

namespace EnvelopeProperty.NativeProjectiveDimensionBounds

/-- The actual projective space has the bound supplied by its original coordinate charts. -/
theorem projectiveSpace_dimension_le (k : Type u) [Field k] (d : ℕ) :
    topologicalKrullDim (DeJongAlterations.projectiveSpace k d) ≤ d := by
  apply IntegralSchemeDimension.topologicalKrullDim_le_of_openCover _ d
    (DeJongAlterations.Geometry.Segre.coordinateCover k d)
  intro i
  let j : Fin (d + 1) := i
  change topologicalKrullDim
    (PrimeSpectrum (DeJongAlterations.Geometry.ProjectiveIdeal.CoordinateRing k j)) ≤ d
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  change ringKrullDim (MvPolynomial {l : Fin (d + 1) // l ≠ j} k) ≤ d
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  have hc : Nat.card {l : Fin (d + 1) // l ≠ j} = d := by
    exact (Nat.card_congr (finSuccAboveEquiv j)).symm.trans (by simp)
  rw [hc]

/-- Any original closed projective embedding bounds the SAME whole scheme, including
an empty, reducible or nonreduced scheme. -/
theorem dimension_le_of_closedImmersion {k : Type u} [Field k] {X : Scheme.{u}} {d : ℕ}
    (i : X ⟶ DeJongAlterations.projectiveSpace k d) [IsClosedImmersion i] :
    topologicalKrullDim X ≤ d := by
  exact IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom i d
    (projectiveSpace_dimension_le k d)

/-- Native projectivity internally supplies an actual finite whole-dimension bound.
No additional embedding, dimension, integrality or reducedness hypothesis is supplied. -/
theorem exists_dimension_le_of_isProjective {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p] :
    ∃ d : ℕ, topologicalKrullDim X ≤ d := by
  obtain ⟨d, i, hi, -⟩ := ProjectiveFactorizationRingIso.of_isProjective p
  exact ⟨d, @dimension_le_of_closedImmersion k _ X d i hi⟩

end EnvelopeProperty.NativeProjectiveDimensionBounds
