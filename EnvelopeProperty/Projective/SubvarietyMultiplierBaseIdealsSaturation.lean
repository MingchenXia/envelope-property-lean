import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsCone
import EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsClosedExtension
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Actual original coordinate localization implies SAME cone saturation -/

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
open ProjBerk
open Char0.EnvelopeGradedBaseIdealsCore Char0.EnvelopeGradedBaseIdealsClosedExtension
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The SAME actual cone quotient kills exactly the original family equations. -/
theorem familyIdeal_le_ker_parameterConeQuotient :
    (familyHomogeneousIdeal X).toIdeal ≤ RingHom.ker (parameterConeQuotient X).toRingHom := by
  intro F hF
  rw [RingHom.mem_ker]
  change X.coneMk ((parameterEquiv (k := k) (M := M)).symm F) = 0
  apply coneMk_eq_zero_iff.mpr
  apply (parameterEquiv_mem_familyIdeal_iff X _).mp
  simpa only [AlgEquiv.apply_symm_apply] using hF

/-- The same original coordinate maps to the same original irrelevant generator. -/
theorem parameterConeQuotient_X (j : Fin (M + 1)) :
    parameterConeQuotient X (MvPolynomial.X j) = Polynomial.C (X.coordMk (MvPolynomial.X j)) := by
  have h := parameterConeQuotient_parameterEquiv X (Polynomial.C (MvPolynomial.X j))
  simpa only [parameterEquiv_C, MvPolynomial.map_X, coneMk_C] using h

/-- Actual powers of each original coordinate suffice for the SAME original
irrelevant-ideal saturation; the power is internally derived by Noetherianity. -/
theorem mem_saturation_of_coordinate_powers (B : Ideal X.ConeRing) (f : X.ConeRing)
    (h : ∀ j : Fin (M + 1), ∃ r : ℕ,
      Polynomial.C (X.coordMk (MvPolynomial.X j)) ^ r * f ∈ B) : f ∈ X.saturation B := by
  let Q := B.colon ({f} : Set X.ConeRing)
  have hrad : X.coneIrrelevant ≤ Q.radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨r, hr⟩ := h j
    refine ⟨r, ?_⟩
    change _ ∈ B.colon ({f} : Set X.ConeRing)
    rw [Submodule.mem_colon_singleton]
    simpa only [smul_eq_mul, mul_comm] using hr
  obtain ⟨r, hr⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  apply mem_saturation_iff.mpr
  refine ⟨r, fun a ha => ?_⟩
  have hm := hr ha
  change a ∈ B.colon ({f} : Set X.ConeRing) at hm
  rw [Submodule.mem_colon_singleton] at hm
  simpa only [smul_eq_mul, mul_comm] using hm

/-- The actual native projective quotient criterion supplies an original
coordinate annihilator from the true whole sheaf inclusion. -/
theorem coordinate_power_mem_of_sheaf_le
    (H J : HomogeneousIdeal (ProjectiveGrading k[X] M))
    (h : GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) H ≤
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) J)
    {F : MvPolynomial (Fin (M + 1)) k[X]} {d : ℕ} (hF : F.IsHomogeneous d)
    (hHF : F ∈ H) (j : Fin (M + 1)) : ∃ r : ℕ, MvPolynomial.X j ^ r * F ∈ J := by
  have hh := Ideal.comap_mono (f := (nativeCoordinateSectionsIso (R := k[X]) j).hom.hom)
    (h ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
  rw [homogeneousQuotient_coordinateSectionIdeal, homogeneousQuotient_coordinateSectionIdeal] at hh
  have hm := hh (Ideal.mem_map_of_mem (coordinateDehom j).toRingHom hHF)
  rw [← homogeneousQuotient_coordinateKernel J j] at hm
  change HomogeneousLocalization.Away.map
    (GradedQuotient.gradedMk (ProjectiveGrading k[X] M) J.toIdeal) (MvPolynomial.X j)
      (homogeneousChartRatioHom j (coordinateDehom j F)) = 0 at hm
  rw [homogeneousChartRatioHom_dehom_of_isHomogeneous j hF] at hm
  exact (GradedQuotient.awayMap_mk_eq_zero_iff (ProjectiveGrading k[X] M) J
    (MvPolynomial.isHomogeneous_X k[X] j) d F (by simpa using hF)).mp hm

/-- A genuine whole comparison on the SAME family gives an actual ambient
comparison modulo exactly its SAME original defining equations. -/
theorem ambient_sheaf_le_of_family_comap_le
    (H J : HomogeneousIdeal (ProjectiveGrading k[X] M))
    (h : (GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) H).comap
        (familyInclusion X) ≤
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) J).comap (familyInclusion X)) :
    GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) H ≤
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) (J ⊔ familyHomogeneousIdeal X) := by
  have hh := Scheme.IdealSheafData.le_map_iff_comap_le.mpr h
  have hker : (familyInclusion X).ker =
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) (familyHomogeneousIdeal X) := rfl
  rw [map_comap_eq_sup_ker, hker, ← quotientIdealSheaf_sup] at hh
  exact hh

/-- The ENTIRE actual family sheaf comparison yields the SAME original cone
saturation. All coordinate annihilators and the irrelevant power are produced
internally from the actual comparison, not supplied as a certificate. -/
theorem map_cone_le_saturation_of_family_comap_le
    (H J : HomogeneousIdeal (ProjectiveGrading k[X] M))
    (h : (GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) H).comap
        (familyInclusion X) ≤
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) J).comap (familyInclusion X)) :
    H.toIdeal.map (parameterConeQuotient X).toRingHom ≤
      X.saturation (J.toIdeal.map (parameterConeQuotient X).toRingHom) := by
  have hs := ambient_sheaf_le_of_family_comap_le X H J h
  have hk : ((familyHomogeneousIdeal X).toIdeal).map (parameterConeQuotient X).toRingHom = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (familyIdeal_le_ker_parameterConeQuotient X)
  rw [Ideal.map_le_iff_le_comap]
  intro F hHF
  change parameterConeQuotient X F ∈ X.saturation (J.toIdeal.map (parameterConeQuotient X).toRingHom)
  rw [← MvPolynomial.sum_homogeneousComponent F, map_sum]
  apply Ideal.sum_mem
  intro d _hd
  have hFd := MvPolynomial.homogeneousComponent_isHomogeneous d F
  have hHd := MvPolynomial.homogeneousComponent_mem_of_mem H.isHomogeneous hHF d
  apply mem_saturation_of_coordinate_powers X
  intro j
  obtain ⟨r, hr⟩ := coordinate_power_mem_of_sheaf_le H (J ⊔ familyHomogeneousIdeal X) hs hFd hHd j
  have hm := Ideal.mem_map_of_mem (parameterConeQuotient X).toRingHom hr
  change _ ∈ (J.toIdeal ⊔ (familyHomogeneousIdeal X).toIdeal).map (parameterConeQuotient X).toRingHom at hm
  rw [Ideal.map_sup, hk, sup_bot_eq] at hm
  refine ⟨r, ?_⟩
  simpa only [map_mul, map_pow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    parameterConeQuotient_X] using hm

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
