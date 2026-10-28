/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Charts
import EnvelopeProperty.Berkovich.ClosedImmersion

/-!
# Homogeneous closed loci on affine projective charts

Dehomogenizing a homogeneous ideal gives its genuine affine chart ideal. Its extension
through the chart-ratio map equals the original ideal in the selected-coordinate
localization. This algebraic statement holds over arbitrary commutative rings.

Over a trivially valued field, chart homeomorphisms identify the closed normalized
projective-model locus with actual quotient-ring analytifications. Homogeneity is
explicit; scheme identification and coherent sheaf gluing are separate constructions.
-/

open scoped NNReal Topology
open Topology

noncomputable section

namespace EnvelopeProperty.ProjBerk

attribute [local instance] MvPolynomial.gradedAlgebra

section Algebra

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The affine chart ideal obtained by dehomogenizing the homogeneous equations. -/
def coordinateChartIdeal (j : Fin (n + 1)) (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    Ideal (CoordinateRing R j) := Ideal.map (coordinateDehom j).toRingHom J

/-- A homogeneous ideal and its dehomogenized chart ideal agree after localization. -/
theorem coordinateChartIdeal_localization_eq (j : Fin (n + 1))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    Ideal.map (algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (MvPolynomial.X j))) J =
      Ideal.map (chartRatioHom j).toRingHom (coordinateChartIdeal j J) := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    change algebraMap (MvPolynomial (Fin (n + 1)) R)
      (Localization.Away (MvPolynomial.X j)) F ∈
      Ideal.map (chartRatioHom j).toRingHom (coordinateChartIdeal j J)
    rw [← MvPolynomial.sum_homogeneousComponent F, map_sum]
    refine Ideal.sum_mem _ fun d _ => ?_
    rw [← chartRatioHom_dehom_homogeneousComponent_mul_pow]
    apply Ideal.mul_mem_right
    exact Ideal.mem_map_of_mem (chartRatioHom j).toRingHom
      (Ideal.mem_map_of_mem (coordinateDehom j).toRingHom
        (MvPolynomial.homogeneousComponent_mem_of_mem hJ hF d))
  · rw [Ideal.map_le_iff_le_comap, coordinateChartIdeal, Ideal.map_le_iff_le_comap]
    intro F hF
    change chartRatioHom (R := R) j (coordinateDehom j F) ∈
      Ideal.map (algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (MvPolynomial.X j))) J
    rw [← MvPolynomial.sum_homogeneousComponent F, map_sum, map_sum]
    refine Ideal.sum_mem _ fun d _ => ?_
    have hmul : chartRatioHom j (coordinateDehom j (MvPolynomial.homogeneousComponent d F)) *
        (algebraMap (MvPolynomial (Fin (n + 1)) R)
          (Localization.Away (MvPolynomial.X j)) (MvPolynomial.X j)) ^ d ∈
        Ideal.map (algebraMap (MvPolynomial (Fin (n + 1)) R)
          (Localization.Away (MvPolynomial.X j))) J := by
      rw [chartRatioHom_dehom_homogeneousComponent_mul_pow]
      exact Ideal.mem_map_of_mem _ (MvPolynomial.homogeneousComponent_mem_of_mem hJ hF d)
    have hinv := Ideal.mul_mem_right
      ((IsLocalization.Away.invSelf (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) :
        Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) ^ d)
      (Ideal.map (algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (MvPolynomial.X j))) J)
      hmul
    simpa only [mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one] using hinv

end Algebra

section Analytic

variable {k : Type*} [Field k] {n : ℕ}

/-- The closed normalized projective-model locus cut out by an ideal of homogeneous
coordinates. Its definition does not impose homogeneity on the ideal. -/
def projectiveZeroLocus (J : Ideal (MvPolynomial (Fin (n + 1)) k)) : Set (ProjBerk k n) :=
  {v | J ≤ v.1.val.supp}

@[simp]
theorem mem_projectiveZeroLocus (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (v : ProjBerk k n) : v ∈ projectiveZeroLocus J ↔ J ≤ v.1.val.supp := Iff.rfl

/-- Vanishing on a coordinate-ring ideal is closed in the projective model. -/
theorem isClosed_projectiveZeroLocus (J : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    IsClosed (projectiveZeroLocus J) :=
  (Berk.isClosed_zeroLocus J).preimage continuous_val

/-- On a coordinate chart, vanishing of a homogeneous ideal is exactly vanishing
of its dehomogenized affine ideal. -/
theorem coordinateChartMap_mem_zeroLocus_iff (j : Fin (n + 1))
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (v : chartOpen (k := k) j) :
    coordinateChartMap j v ∈ Berk.zeroLocus (coordinateChartIdeal j J) ↔ v.1 ∈ projectiveZeroLocus J := by
  let z := Berk.awayLift (MvPolynomial.X j) v.1.1 v.2
  have hbase : Ideal.comap
      (algebraMap (MvPolynomial (Fin (n + 1)) k) (Localization.Away (MvPolynomial.X j)))
      z.val.supp = v.1.1.val.supp := by
    ext F
    simp only [Ideal.mem_comap, Valuation.mem_supp_iff]
    change (Berk.awayLift (MvPolynomial.X j) v.1.1 v.2).val
      (algebraMap (MvPolynomial (Fin (n + 1)) k) (Localization.Away (MvPolynomial.X j)) F) = 0 ↔
        v.1.1.val F = 0
    rw [Berk.awayLift_val_algebraMap (MvPolynomial.X j) v.1.1 v.2 F]
  have hchart : (coordinateChartMap j v).val.supp =
      Ideal.comap (chartRatioHom j).toRingHom z.val.supp :=
    Valuation.comap_supp z.val (chartRatioHom j).toRingHom
  change coordinateChartIdeal j J ≤ (coordinateChartMap j v).val.supp ↔ J ≤ v.1.1.val.supp
  rw [hchart, ← Ideal.map_le_iff_le_comap, ← coordinateChartIdeal_localization_eq j J hJ,
    Ideal.map_le_iff_le_comap, hbase]

/-- The closed part of a coordinate chart cut out by a projective-model ideal. -/
def closedChart (j : Fin (n + 1)) (J : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    Set (chartOpen (k := k) j) := {v | v.1 ∈ projectiveZeroLocus J}

/-- The homogeneous closed locus is closed within each coordinate chart. -/
theorem isClosed_closedChart (j : Fin (n + 1))
    (J : Ideal (MvPolynomial (Fin (n + 1)) k)) : IsClosed (closedChart j J) :=
  (isClosed_projectiveZeroLocus J).preimage continuous_subtype_val

/-- The affine chart homeomorphism restricts to the homogeneous closed locus. -/
def closedChartHomeomorph (j : Fin (n + 1))
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :
    closedChart j J ≃ₜ Berk.zeroLocus (k := k) (coordinateChartIdeal j J) :=
  (coordinateChartHomeomorph j).subtype fun v => (coordinateChartMap_mem_zeroLocus_iff j J hJ v).symm

@[simp]
theorem closedChartHomeomorph_apply_coe (j : Fin (n + 1))
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (v : closedChart j J) :
    (closedChartHomeomorph j J hJ v).1 = coordinateChartMap j v.1 := rfl

/-- The genuine quotient-ring analytification is the corresponding closed
coordinate chart of the normalized projective model. -/
def quotientChartHomeomorph (j : Fin (n + 1))
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :
    Berk k (CoordinateRing k j ⧸ coordinateChartIdeal j J) ≃ₜ closedChart j J :=
  (Berk.quotientHomeomorph (coordinateChartIdeal j J)).trans (closedChartHomeomorph j J hJ).symm

@[simp]
theorem coordinateChartMap_quotientChartHomeomorph (j : Fin (n + 1))
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (y : Berk k (CoordinateRing k j ⧸ coordinateChartIdeal j J)) :
    coordinateChartMap j (quotientChartHomeomorph j J hJ y).1 =
      Berk.quotientComap (coordinateChartIdeal j J) y := by
  change (closedChartHomeomorph j J hJ
    ((closedChartHomeomorph j J hJ).symm (Berk.quotientHomeomorph (coordinateChartIdeal j J) y))).1 = _
  rw [Homeomorph.apply_symm_apply]
  rfl

end Analytic

end EnvelopeProperty.ProjBerk
