/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeQuotient
import EnvelopeProperty.Berkovich.SchemeModelIdeals
import EnvelopeProperty.Berkovich.SchemeCenterAffine
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Genuine proper-center projective homogeneous ideal functions

The actual constant degree-zero coefficient isomorphism proves properness
of polynomial Proj over any commutative ring. For an explicitly bounded
prescribed model coefficient seminorm, normalization gives genuine bounded
coordinate charts containing the actual proper center. Whole homogeneous
decomposition, original ideal homogeneity and actual section-ring identities
then identify the intrinsic center-stalk model ideal norm/log with the entire
original homogeneous ideal norm/log. No finite generators, Noetherianity,
field, completeness, infinitude or reducedness hypothesis is required.

The coefficient bound concerns the chosen model ring; it does not assert
boundedness of a nontrivially valued field. The original ideal is retained,
without radical replacement. Analytic structure-sheaf comparison and the
old k[t] Gauss-variable-swap specialization remain separate constructions.
-/

open scoped Classical NNReal ENNReal Topology
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjBerk
variable {R : Type u} [CommRing R] {n : ℕ}

/-- Original constants are the entire actual degree-zero homogeneous component over every coefficient ring. -/
theorem homogeneousCoefficientZero_bijective : Function.Bijective (homogeneousCoefficientZero R n) := by
  constructor
  · intro r s h
    exact MvPolynomial.C_injective (Fin (n + 1)) R (congrArg Subtype.val h)
  · intro F
    refine ⟨MvPolynomial.coeff 0 (F : MvPolynomial (Fin (n + 1)) R), Subtype.ext ?_⟩
    exact (MvPolynomial.homogeneousComponent_zero _).symm.trans
      (MvPolynomial.homogeneousComponent_eq_self F.2)

/-- The actual coefficient ring is isomorphic to the whole genuine degree-zero component. -/
def homogeneousCoefficientZeroIso : CommRingCat.of R ≅ CommRingCat.of (ProjectiveGrading R n 0) :=
  (RingEquiv.ofBijective (homogeneousCoefficientZero R n) homogeneousCoefficientZero_bijective).toCommRingCatIso

private local instance nativePolynomialDegreeZeroTower :
    IsScalarTower R (ProjectiveGrading R n 0) (MvPolynomial (Fin (n + 1)) R) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := ProjectiveGrading R n 0)
    (A := MvPolynomial (Fin (n + 1)) R) fun _ => rfl

/-- The actual original polynomial projective base morphism is genuinely proper over every coefficient ring. -/
theorem nativeStructureMap_isProper : IsProper (nativeStructureMap (R := R) (n := n)) := by
  let : Algebra.FiniteType (ProjectiveGrading R n 0) (MvPolynomial (Fin (n + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (ProjectiveGrading R n 0) _
  change IsProper (Proj.toSpecZero (ProjectiveGrading R n) ≫
    Spec.map (homogeneousCoefficientZeroIso (R := R) (n := n)).hom)
  infer_instance

/-- The actual original homogeneous quotient kernel sheaf, viewed on the genuine polynomial projective coefficient model. -/
def nativeHomogeneousIdealSheaf (J : HomogeneousIdeal (ProjectiveGrading R n)) :
    (NativeProjectiveScheme R n).IdealSheafData := GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J

end EnvelopeProperty.ProjBerk

namespace EnvelopeProperty.Berkovich.Spectrum
variable {R σ : Type*} [CommRing R]

/-- True coefficient and variable bounds control EVERY polynomial of an arbitrary polynomial ring. -/
theorem isBounded_mvPolynomial_of_C_X (x : Spectrum (MvPolynomial σ R))
    (hC : ∀ r : R, x.val (MvPolynomial.C r) ≤ 1) (hX : ∀ i : σ, x.val (MvPolynomial.X i) ≤ 1) :
    IsBounded x := by
  intro F
  induction F using MvPolynomial.induction_on with
  | C r => exact hC r
  | add F G hF hG => exact (x.val.map_add F G).trans (max_le hF hG)
  | mul_X F i hF =>
    rw [map_mul]
    exact (mul_le_mul' hF (hX i)).trans (by simp)

end EnvelopeProperty.Berkovich.Spectrum

namespace EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
variable {R : Type u} [CommRing R] (v : Valuation R ℝ≥0) {n : ℕ}

/-- Bounded prescribed coefficients and actual normalized variables bound the entire original polynomial seminorm. -/
theorem isBounded_polynomial (hb : ∀ r, v r ≤ 1) (x : RelativeNormalizedProjectiveSpectrum v n) :
    Spectrum.IsBounded x.1.1 :=
  Spectrum.isBounded_mvPolynomial_of_C_X x.1.1
    (fun r => (x.2 r).le.trans (hb r)) (NormalizedProjectiveSpectrum.val_X_le_one x.1)

/-- A value-one coordinate and bounded original coefficients give actual boundedness on EVERY affine coordinate polynomial. -/
theorem isBounded_coordinateChart_of_val_X_eq_one (hb : ∀ r, v r ≤ 1)
    (x : RelativeNormalizedProjectiveSpectrum v n) (j : Fin (n + 1)) (hj : x.1.1.val (X j) = 1) :
    Spectrum.IsBounded (coordinateChartHomeomorph v j
      ⟨x, by change x.1.1.val (X j) ≠ 0; rw [hj]; exact one_ne_zero⟩).1 := by
  apply Spectrum.isBounded_mvPolynomial_of_C_X
  · intro r
    exact ((coordinateChartHomeomorph v j _).2 r).le.trans (hb r)
  · intro i
    rw [coordinateChartHomeomorph_val_X]
    change x.1.1.val (X i.1) / x.1.1.val (X j) ≤ 1
    rw [hj, div_one]
    exact NormalizedProjectiveSpectrum.val_X_le_one x.1 i.1

private local instance nativeModelPolynomialProper :
    IsProper (ProjBerk.nativeStructureMap (R := R) (n := n)) := ProjBerk.nativeStructureMap_isProper

/-- True whole affine section boundedness forces the actual proper center into a normalized value-one coordinate chart. -/
theorem center_nativeHomeomorph_mem_coordinateOpen (hb : ∀ r, v r ≤ 1)
    (x : RelativeNormalizedProjectiveSpectrum v n) (j : Fin (n + 1)) (hj : x.1.1.val (X j) = 1) :
    RelativeSchemeValuedPoint.center hb (nativeHomeomorph v x) ∈ ProjBerk.nativeCoordinateOpen j := by
  have hne : x.1.1.val (X j) ≠ 0 := by rw [hj]; exact one_ne_zero
  let z : chartOpen v j := ⟨x, hne⟩
  apply RelativeSchemeValuedPoint.center_mem_of_bounded_affine hb (nativeHomeomorph v x)
    ⟨ProjBerk.nativeCoordinateOpen j, ProjBerk.nativeCoordinateOpen_isAffine j⟩ hne
  intro s
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (ProjBerk.nativeCoordinateSectionsIso (R := R) j).hom).2 s
  rw [nativeHomeomorph_val_apply v j z a]
  exact isBounded_coordinateChart_of_val_X_eq_one v hb x j hj a

end EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum

namespace EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
variable {R : Type u} [CommRing R] (v : Valuation R ℝ≥0) {n : ℕ}

/-- The true whole homogeneous fraction has its original value in a normalized value-one chart. -/
theorem coordinateChart_val_dehom_of_isHomogeneous (x : RelativeNormalizedProjectiveSpectrum v n)
    (j : Fin (n + 1)) (hj : x.1.1.val (X j) = 1) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d) :
    (coordinateChartHomeomorph v j
      ⟨x, by change x.1.1.val (X j) ≠ 0; rw [hj]; exact one_ne_zero⟩).1.val
        (ProjBerk.coordinateDehom j F) = x.1.1.val F := by
  have hne : x.1.1.val (X j) ≠ 0 := by rw [hj]; exact one_ne_zero
  have h := congrArg (Spectrum.awayLift (X j) x.1.1 hne).val
    (ProjBerk.chartRatioHom_dehom_mul_pow j hF)
  simp only [map_mul, map_pow, Spectrum.awayLift_val_algebraMap, hj, one_pow, mul_one] at h
  exact h

/-- Genuine entire homogeneous recomposition bounds the dehomogenization of EVERY polynomial by its original graded norm. -/
theorem coordinateChart_val_dehom_le (x : RelativeNormalizedProjectiveSpectrum v n)
    (j : Fin (n + 1)) (hj : x.1.1.val (X j) = 1) (F : MvPolynomial (Fin (n + 1)) R) :
    (coordinateChartHomeomorph v j
      ⟨x, by change x.1.1.val (X j) ≠ 0; rw [hj]; exact one_ne_zero⟩).1.val
        (ProjBerk.coordinateDehom j F) ≤ x.1.1.val F := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent F, map_sum]
  apply Valuation.map_sum_le
  intro d _hd
  rw [coordinateChart_val_dehom_of_isHomogeneous v x j hj d _
    (MvPolynomial.homogeneousComponent_isHomogeneous _ _)]
  exact (Spectrum.isPolynomialGraded_iff x.1.1).mp x.1.2.1 F d

/-- Entire original homogeneous ideal norms agree with actual value-one affine coordinate ideal norms, without chosen finite generators. -/
theorem idealNorm_coordinateDehom (hb : ∀ r, v r ≤ 1)
    (J : HomogeneousIdeal (ProjBerk.ProjectiveGrading R n)) (x : RelativeNormalizedProjectiveSpectrum v n)
    (j : Fin (n + 1)) (hj : x.1.1.val (X j) = 1) :
    Spectrum.idealNorm (J.toIdeal.map (ProjBerk.coordinateDehom j).toRingHom)
      (coordinateChartHomeomorph v j
        ⟨x, by change x.1.1.val (X j) ≠ 0; rw [hj]; exact one_ne_zero⟩).1 =
      Spectrum.idealNorm J.toIdeal x.1.1 := by
  rw [Spectrum.idealNorm_map _ _ (isBounded_coordinateChart_of_val_X_eq_one v hb x j hj)]
  apply le_antisymm
  · apply (Spectrum.idealNorm_le_iff _ _ _).mpr
    intro F hF
    exact (ENNReal.coe_le_coe.mpr (coordinateChart_val_dehom_le v x j hj F)).trans
      (Spectrum.val_le_idealNorm _ _ hF)
  · apply (Spectrum.idealNorm_le_iff _ _ _).mpr
    intro F hF
    rw [NormalizedProjectiveSpectrum.isGraded x.1 F, ENNReal.coe_finset_sup]
    apply Finset.sup_le
    intro d _hd
    have hFd := MvPolynomial.homogeneousComponent_mem_of_mem J.isHomogeneous hF d
    have h := Spectrum.val_le_idealNorm J.toIdeal
      (Spectrum.comap (ProjBerk.coordinateDehom j).toRingHom
        (coordinateChartHomeomorph v j
          ⟨x, by change x.1.1.val (X j) ≠ 0; rw [hj]; exact one_ne_zero⟩).1) hFd
    erw [Spectrum.comap_val_apply,
      coordinateChart_val_dehom_of_isHomogeneous v x j hj d _
        (MvPolynomial.homogeneousComponent_isHomogeneous _ _)] at h
    exact h

end EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum

namespace EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
variable {R : Type u} [CommRing R] (v : Valuation R ℝ≥0) {n : ℕ}
private local instance nativeModelPolynomialProperFinal :
    IsProper (ProjBerk.nativeStructureMap (R := R) (n := n)) := ProjBerk.nativeStructureMap_isProper

/-- The intrinsic norm of the true projective quotient ideal sheaf at its actual proper center is the original whole homogeneous ideal norm. -/
theorem modelIdealNorm_quotient_eq_idealNorm (hb : ∀ r, v r ≤ 1)
    (J : HomogeneousIdeal (ProjBerk.ProjectiveGrading R n)) (x : RelativeNormalizedProjectiveSpectrum v n) :
    RelativeSchemeValuedPoint.modelIdealNorm (ProjBerk.nativeHomogeneousIdealSheaf J)
      hb (nativeHomeomorph v x) = Spectrum.idealNorm J.toIdeal x.1.1 := by
  obtain ⟨j, hj⟩ := NormalizedProjectiveSpectrum.exists_val_X_eq_one x.1
  have hne : x.1.1.val (X j) ≠ 0 := by rw [hj]; exact one_ne_zero
  let z : chartOpen v j := ⟨x, hne⟩
  let U : (ProjBerk.NativeProjectiveScheme R n).affineOpens :=
    ⟨ProjBerk.nativeCoordinateOpen j, ProjBerk.nativeCoordinateOpen_isAffine j⟩
  let I := ProjBerk.nativeHomogeneousIdealSheaf J
  have hc : RelativeSchemeValuedPoint.center hb (nativeHomeomorph v x) ∈ U.1 :=
    center_nativeHomeomorph_mem_coordinateOpen v hb x j hj
  let y := (RelativeSchemeValuedPoint.sectionSpectrum (nativeHomeomorph v x) U.1
    (RelativeSchemeValuedPoint.support_mem_of_center_mem hb (nativeHomeomorph v x) U.1 hc)).1
  have hy : Spectrum.IsBounded y :=
    RelativeSchemeValuedPoint.isBounded_sectionSpectrum_of_center_mem hb (nativeHomeomorph v x) U.1 hc
  let φ := (ProjBerk.nativeCoordinateSectionsIso (R := R) j).hom.hom
  have he : Spectrum.comap φ y = (coordinateChartHomeomorph v j z).1 := by
    apply Spectrum.ext_val
    intro a
    exact nativeHomeomorph_val_apply v j z a
  have hi : (I.ideal U).comap φ = J.toIdeal.map (ProjBerk.coordinateDehom j).toRingHom :=
    ProjBerk.homogeneousQuotient_coordinateSectionIdeal J j
  have hnorm := Spectrum.idealNorm_map φ ((I.ideal U).comap φ) hy
  erw [Ideal.map_comap_of_surjective φ
    (ConcreteCategory.bijective_of_isIso (ProjBerk.nativeCoordinateSectionsIso (R := R) j).hom).2,
    hi, he] at hnorm
  rw [RelativeSchemeValuedPoint.modelIdealNorm_eq_affine I hb (nativeHomeomorph v x) U hc]
  exact hnorm.trans (idealNorm_coordinateDehom v hb J x j hj)

/-- The genuine proper-center model logarithm is the original homogeneous ideal logarithm, including zero ideals and negative infinity. -/
theorem modelIdealLog_quotient_eq_idealLog (hb : ∀ r, v r ≤ 1)
    (J : HomogeneousIdeal (ProjBerk.ProjectiveGrading R n)) (x : RelativeNormalizedProjectiveSpectrum v n) :
    RelativeSchemeValuedPoint.modelIdealLog (ProjBerk.nativeHomogeneousIdealSheaf J)
      hb (nativeHomeomorph v x) = Spectrum.idealLog J.toIdeal x.1.1 :=
  congrArg ENNReal.log (modelIdealNorm_quotient_eq_idealNorm v hb J x)

end EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
