/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.CanonicalDifferentialMap

/-!
# The genuine relative canonical map has the actual differential determinant

The arbitrary actual source differential basis need not consist of
coordinate differentials. The all-original-functions Jacobian image is
computed from the entire genuine canonical map.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open Module Ideal
open scoped Classical TensorProduct

variable {k R A : Type*} [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A] {n : ℕ}

/-- Pullback of the genuine source canonical generator is the actual wedge of
its differential images. -/
theorem affineCanonicalDifferentialMap_volumeForm
    (bR : Basis (Fin n) R (KaehlerDifferential k R)) :
    affineCanonicalDifferentialMap (k := k) (R := R) (A := A) n
      ((1 : A) ⊗ₜ[R] differentialVolumeForm bR) =
        exteriorPower.ιMulti A n (fun j => KaehlerDifferential.map k k R A (bR j)) := by
  simpa only [differentialVolumeForm, one_smul] using
    (affineCanonicalDifferentialMap_tmul_wedge (k := k) (R := R) (A := A) n 1 bR)

/-- The coefficient of the genuine relative canonical map is exactly the
actual determinant of the genuine differential map. -/
theorem differentialVolumeCoordinate_affineCanonicalDifferentialMap_volumeForm
    (bR : Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) :
    differentialVolumeCoordinate bA
      (affineCanonicalDifferentialMap (k := k) (R := R) (A := A) n
        ((1 : A) ⊗ₜ[R] differentialVolumeForm bR)) = relativeDifferentialDet bR bA := by
  rw [affineCanonicalDifferentialMap_volumeForm, differentialVolumeCoordinate,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Basis.det_apply]
  rfl

/-- The full actual all-source-functions Jacobian ideal is the ideal of the
actual relative canonical coefficient for any genuine source and target bases;
no etale source-coordinate or assumed image hypothesis is required. -/
theorem affineRelativeJacobianIdeal_eq_span_of_differential_basis
    (bR : Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) :
    affineRelativeJacobianIdeal (R := R) bA = span {relativeDifferentialDet bR bA} := by
  apply le_antisymm (affineRelativeJacobianIdeal_le_span bR bA)
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = _)
  have hmem : relativeDifferentialDet bR bA ∈ LinearMap.range
      ((differentialVolumeEquiv bA).toLinearMap.comp
        (affineCanonicalDifferentialMap (k := k) (R := R) (A := A) n)) := by
    refine ⟨(1 : A) ⊗ₜ[R] differentialVolumeForm bR, ?_⟩
    exact differentialVolumeCoordinate_affineCanonicalDifferentialMap_volumeForm bR bA
  rwa [range_differentialVolumeCoordinate_comp_affineCanonicalDifferentialMap] at hmem

end EnvelopeProperty.Char0
