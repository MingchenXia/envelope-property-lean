/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeModelIdeals

/-!
# Genuine coefficient opens and whole homogeneous ideal supports

The actual native projective structure map preserves coefficient prime
membership. Its genuine coefficient opens therefore avoid every original
homogeneous quotient ideal containing an actual power of that coefficient.
-/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual native projective structure map sends the original homogeneous
prime to its entire coefficient inverse image. -/
theorem nativeStructureMap_mem_coefficient_iff {R : Type u} [CommRing R] {n : ℕ}
    (p : NativeProjectiveScheme R n) (r : R) :
    r ∈ (nativeStructureMap p).asIdeal ↔ MvPolynomial.C r ∈ p.asHomogeneousIdeal := by
  simp only [nativeStructureMap, Scheme.Hom.comp_apply, Spec.map_apply,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change homogeneousCoefficientZero R n r ∈
    (AlgebraicGeometry.Proj.toSpecZero (ProjectiveGrading R n) p).asIdeal ↔ _
  simp only [AlgebraicGeometry.Proj.toSpecZero, Scheme.Hom.comp_apply, Spec.map_apply,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have hbasic : Scheme.forgetToLocallyRingedSpace.map
      (AlgebraicGeometry.Proj.basicOpenToSpec (ProjectiveGrading R n) 1) =
      ProjectiveSpectrum.Proj.toSpec (ProjectiveGrading R n) 1 := by
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [AlgebraicGeometry.Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
    simp only [Category.assoc, ← Spec.map_comp]
    rfl
  change HomogeneousLocalization.fromZeroRingHom (ProjectiveGrading R n)
      (Submonoid.powers 1) (homogeneousCoefficientZero R n r) ∈
    ((Scheme.forgetToLocallyRingedSpace.map
      (AlgebraicGeometry.Proj.basicOpenToSpec (ProjectiveGrading R n) 1)).base _).asIdeal ↔ _
  rw [hbasic]
  change HomogeneousLocalization.mk
      (⟨0, homogeneousCoefficientZero R n r, 1, one_mem _⟩ :
        HomogeneousLocalization.NumDenSameDeg (ProjectiveGrading R n) (Submonoid.powers 1)) ∈
    ((ProjectiveSpectrum.Proj.toSpec (ProjectiveGrading R n) 1).base _).asIdeal ↔ _
  convert ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply (ProjectiveGrading R n)
    (f := (1 : MvPolynomial (Fin (n + 1)) R))
    ⟨p, by
      change (1 : MvPolynomial (Fin (n + 1)) R) ∉ p.asHomogeneousIdeal.toIdeal
      exact (Ideal.ne_top_iff_one _).mp p.isPrime.ne_top⟩
    (⟨0, homogeneousCoefficientZero R n r, 1, one_mem _⟩ :
      HomogeneousLocalization.NumDenSameDeg (ProjectiveGrading R n) (Submonoid.powers 1)) using 1
  · apply Iff.of_eq
    apply congrArg (fun q : (AlgebraicGeometry.Proj.basicOpen (ProjectiveGrading R n)
        (1 : MvPolynomial (Fin (n + 1)) R)).toScheme =>
      HomogeneousLocalization.mk
        (⟨0, homogeneousCoefficientZero R n r, 1, one_mem _⟩ :
          HomogeneousLocalization.NumDenSameDeg (ProjectiveGrading R n) (Submonoid.powers 1)) ∈
        ((ProjectiveSpectrum.Proj.toSpec (ProjectiveGrading R n) 1).base q).asIdeal)
    apply Subtype.ext
    change ((AlgebraicGeometry.Proj.basicOpen (ProjectiveGrading R n)
      (1 : MvPolynomial (Fin (n + 1)) R)).ι)
        (((AlgebraicGeometry.Proj (ProjectiveGrading R n)).isoOfEq _).inv
          ((AlgebraicGeometry.Proj (ProjectiveGrading R n)).topIso.inv p)) = p
    rw [← Scheme.Hom.comp_apply, Scheme.isoOfEq_inv_ι]
    exact congrArg (fun f : AlgebraicGeometry.Proj (ProjectiveGrading R n) ⟶
        AlgebraicGeometry.Proj (ProjectiveGrading R n) => f p)
      (Scheme.toIso_inv_ι (AlgebraicGeometry.Proj (ProjectiveGrading R n)))
  · rfl

/-- The true coefficient principal open pulls back to the actual homogeneous
principal open of the original constant polynomial. -/
theorem nativeStructureMap_preimage_coefficient_basicOpen
    {R : Type u} [CommRing R] {n : ℕ} (r : R) :
    nativeStructureMap (R := R) (n := n) ⁻¹ᵁ PrimeSpectrum.basicOpen r =
      AlgebraicGeometry.Proj.basicOpen (ProjectiveGrading R n) (MvPolynomial.C r) := by
  ext p
  change (r ∉ (nativeStructureMap p).asIdeal) ↔
    (MvPolynomial.C r ∉ p.asHomogeneousIdeal)
  exact not_congr (nativeStructureMap_mem_coefficient_iff p r)

/-- A genuine coefficient-power generator confines the actual entire
homogeneous kernel ideal sheaf support to the coefficient zero locus. -/
theorem coefficientOpen_le_compl_support_of_power_mem
    {R : Type u} [CommRing R] {n : ℕ}
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (r : R) (A : ℕ)
    (hA : MvPolynomial.C (r ^ A) ∈ J.toIdeal) :
    nativeStructureMap (R := R) (n := n) ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤
      (nativeHomogeneousIdealSheaf J).support.compl := by
  intro p hp
  change p ∉ (nativeHomogeneousIdealSheaf J).support
  intro hmem
  have hJ : J.toIdeal ≤ p.asHomogeneousIdeal.toIdeal := by
    change p ∈ (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).support at hmem
    rwa [← SetLike.mem_coe, GradedQuotient.quotientIdealSheaf_support_eq_zeroLocus] at hmem
  have hpow : (MvPolynomial.C r) ^ A ∈ p.asHomogeneousIdeal.toIdeal := by
    simpa only [map_pow] using hJ hA
  have hr := p.isPrime.mem_of_pow_mem A hpow
  exact ((nativeStructureMap_mem_coefficient_iff p r).not.mp hp) hr

end EnvelopeProperty.ProjBerk
