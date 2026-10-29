/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.HomogeneousQuotient
import EnvelopeProperty.Projective.NativeClosed

/-!
# Original homogeneous ideal sheaves and actual native projective quotients

The genuine kernel ideal sheaf of the actual polynomial Proj quotient has
its entire coordinate ideal equal to the original dehomogenization image,
without radical replacement. The actual closed-projective native comparison
then identifies its prescribed-base points with whole normalized seminorms
vanishing on the original homogeneous ideal. Compactness and Hausdorffness
hold for every prescribed base seminorm, including unbounded values and empty
quotients. Coefficient rings are arbitrary; no field, completeness, infinitude,
Noetherianity or nonreduced exclusion is used. No coherent analytic sheaf
identification or recovery of irrelevant-supported original ideals is claimed.
-/

open scoped Classical NNReal Topology
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjBerk
variable {R : Type u} [CommRing R] {n : ℕ}
private local instance nativeQuotientChartAlgebra (j : Fin (n + 1)) :
    Algebra R (HomogeneousChartRing R j) := homogeneousChartAlgebra j

/-- The entire original coordinate dehomogenization image is the true homogeneous quotient away kernel in affine coordinates. -/
theorem homogeneousQuotient_coordinateKernel (J : HomogeneousIdeal (ProjectiveGrading R n))
    (j : Fin (n + 1)) :
    (RingHom.ker (Away.map (GradedQuotient.gradedMk (ProjectiveGrading R n) J.toIdeal)
      (MvPolynomial.X j))).comap (homogeneousChartRatioHom j).toRingHom =
        J.toIdeal.map (coordinateDehom j).toRingHom := by
  apply le_antisymm
  · intro a ha
    change Away.map (GradedQuotient.gradedMk (ProjectiveGrading R n) J.toIdeal) (X j)
      (homogeneousChartRatioHom j a) = 0 at ha
    obtain ⟨d, F, hF, hrep⟩ := Away.mk_surjective
      (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j) (homogeneousChartRatioHom j a)
    rw [← hrep] at ha
    obtain ⟨m, hm⟩ := (GradedQuotient.awayMap_mk_eq_zero_iff (ProjectiveGrading R n) J
      (MvPolynomial.isHomogeneous_X R j) d F hF).mp ha
    have he : coordinateDehom j F = a := by
      rw [← homogeneousChartDehom_mk j d F hF, hrep]
      exact AlgHom.congr_fun (homogeneousChartDehom_comp_ratioHom j) a
    rw [← he]
    have h := Ideal.mem_map_of_mem (coordinateDehom j).toRingHom hm
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow,
      coordinateDehom, MvPolynomial.aeval_X, coordinateDehomCoord_self, one_pow, one_mul] using h
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    change Away.map (GradedQuotient.gradedMk (ProjectiveGrading R n) J.toIdeal) (X j)
      (homogeneousChartRatioHom j (coordinateDehom j F)) = 0
    rw [← MvPolynomial.sum_homogeneousComponent F, map_sum, map_sum, map_sum]
    apply Finset.sum_eq_zero
    intro d _hd
    have hFd : homogeneousComponent d F ∈ J.toIdeal :=
      MvPolynomial.homogeneousComponent_mem_of_mem J.isHomogeneous hF d
    have h := (GradedQuotient.awayMap_mk_eq_zero_iff (ProjectiveGrading R n) J
      (MvPolynomial.isHomogeneous_X R j) d (homogeneousComponent d F)
      (by simpa using MvPolynomial.homogeneousComponent_mem d F)).mpr ⟨0, by simpa using hFd⟩
    have he : homogeneousChartRatioHom j (coordinateDehom j (homogeneousComponent d F)) =
        Away.mk (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j) d
          (homogeneousComponent d F) (by simpa using MvPolynomial.homogeneousComponent_mem d F) := by
      rw [← homogeneousChartDehom_mk j d (homogeneousComponent d F),
        ← AlgHom.comp_apply, homogeneousChartRatioHom_comp_dehom, AlgHom.id_apply]
    rw [he]
    exact h

end EnvelopeProperty.ProjBerk

namespace EnvelopeProperty.ProjBerk
variable {R : Type u} [CommRing R] {n : ℕ}
private local instance nativeQuotientSectionChartAlgebra (j : Fin (n + 1)) :
    Algebra R (HomogeneousChartRing R j) := homogeneousChartAlgebra j

set_option backward.isDefEq.respectTransparency false in
/-- The genuine projective quotient kernel sheaf on an actual coordinate open is exactly the original dehomogenized ideal on the whole coordinate ring. -/
theorem homogeneousQuotient_coordinateSectionIdeal (J : HomogeneousIdeal (ProjectiveGrading R n))
    (j : Fin (n + 1)) :
    ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).ideal
      ⟨nativeCoordinateOpen j,
        Proj.isAffineOpen_basicOpen (ProjectiveGrading R n) (X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < (1 : ℕ))⟩).comap (nativeCoordinateSectionsIso j).hom.hom =
            J.toIdeal.map (coordinateDehom j).toRingHom := by
  have he : (nativeCoordinateSectionsIso (R := R) j).hom =
      CommRingCat.ofHom (homogeneousChartRatioHom j).toRingHom ≫
        Proj.awayToSection (ProjectiveGrading R n) (X j) := by
    rw [nativeCoordinateSectionsIso, Iso.trans_hom, nativeHomogeneousChartSectionsIso_hom]
    rfl
  rw [he, CommRingCat.hom_comp, ← Ideal.comap_comap]
  erw [GradedQuotient.quotientIdealSheaf_awayToSection_comap (ProjectiveGrading R n) J
    (by decide : 0 < (1 : ℕ)) (MvPolynomial.isHomogeneous_X R j)]
  exact homogeneousQuotient_coordinateKernel J j

private local instance nativeQuotientClosedImmersion (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    IsClosedImmersion (show Proj (GradedQuotient.grading (ProjectiveGrading R n) J.toIdeal) ⟶
      NativeProjectiveScheme R n from GradedQuotient.quotientSchemeMap (ProjectiveGrading R n) J) :=
  GradedQuotient.instIsClosedImmersion_quotientSchemeMap (ProjectiveGrading R n) J

/-- The explicit original-ideal normalized vanishing locus is the genuine quotient scheme support locus. -/
theorem homogeneousQuotient_normalizedClosedLocus (v : Valuation R ℝ≥0)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    normalizedClosedLocus v (GradedQuotient.quotientSchemeMap (ProjectiveGrading R n) J) =
      {x : RelativeNormalizedProjectiveSpectrum v n | J.toIdeal ≤ x.1.1.val.supp} := by
  ext x
  change NormalizedProjectiveSpectrum.nativeSupport x.1 ∈
    Set.range (GradedQuotient.quotientSchemeMap (ProjectiveGrading R n) J) ↔ J.toIdeal ≤ x.1.1.val.supp
  rw [GradedQuotient.range_quotientSchemeMap]
  rfl

/-- Actual native points of the original homogeneous quotient are the entire normalized J-vanishing seminorms with the exact prescribed coefficients. -/
def nativeHomogeneousQuotientHomeomorph (v : Valuation R ℝ≥0)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    RelativeSchemeValuedPoint v
      (GradedQuotient.quotientSchemeMap (ProjectiveGrading R n) J ≫ nativeStructureMap) ≃ₜ
        {x : RelativeNormalizedProjectiveSpectrum v n | J.toIdeal ≤ x.1.1.val.supp} :=
  (nativeClosedProjectiveHomeomorph v (GradedQuotient.quotientSchemeMap (ProjectiveGrading R n) J)).trans
    (Homeomorph.setCongr (homogeneousQuotient_normalizedClosedLocus v J))

/-- The homogeneous quotient comparison preserves the entire original native inclusion point. -/
theorem nativeHomogeneousQuotientHomeomorph_apply (v : Valuation R ℝ≥0)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (x : RelativeSchemeValuedPoint v
      (GradedQuotient.quotientSchemeMap (ProjectiveGrading R n) J ≫ nativeStructureMap)) :
    RelativeNormalizedProjectiveSpectrum.nativeHomeomorph v (nativeHomogeneousQuotientHomeomorph v J x).1 =
      RelativeSchemeValuedPoint.map (GradedQuotient.quotientSchemeMap (ProjectiveGrading R n) J) rfl x :=
  nativeClosedProjectiveHomeomorph_apply v _ x

/-- The actual quotient inclusion's entire polynomial prime support is the resulting whole seminorm kernel. -/
theorem nativeHomogeneousQuotientHomeomorph_support (v : Valuation R ℝ≥0)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (x : RelativeSchemeValuedPoint v
      (GradedQuotient.quotientSchemeMap (ProjectiveGrading R n) J ≫ nativeStructureMap)) :
    (RelativeSchemeValuedPoint.map (GradedQuotient.quotientSchemeMap (ProjectiveGrading R n) J) rfl x).1.point.asHomogeneousIdeal.toIdeal =
      (nativeHomogeneousQuotientHomeomorph v J x).1.1.1.val.supp :=
  nativeClosedProjectiveHomeomorph_support_toIdeal v _ x

/-- The actual native projective homogeneous quotient space is compact for every prescribed coefficient seminorm. -/
theorem compactSpace_nativeHomogeneousQuotient (v : Valuation R ℝ≥0)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    CompactSpace (RelativeSchemeValuedPoint v
      (GradedQuotient.quotientSchemeMap (ProjectiveGrading R n) J ≫ nativeStructureMap)) :=
  compactSpace_nativeClosedProjective v _

/-- The actual native projective homogeneous quotient space is Hausdorff, including empty or nonreduced quotients. -/
theorem t2Space_nativeHomogeneousQuotient (v : Valuation R ℝ≥0)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    T2Space (RelativeSchemeValuedPoint v
      (GradedQuotient.quotientSchemeMap (ProjectiveGrading R n) J ≫ nativeStructureMap)) :=
  t2Space_nativeClosedProjective v _

end EnvelopeProperty.ProjBerk
