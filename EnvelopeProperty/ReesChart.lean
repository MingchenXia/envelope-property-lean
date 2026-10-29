import EnvelopeProperty.ReesPresentation
import EnvelopeProperty.GradedQuotient
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Actual degree-zero charts of the original homogeneous Rees quotient

The rings, grading and maps are the genuine original quotient and localization.
Domain and a nonzero selected generator are used only for its embedding into
that SAME original fraction field and the actual fraction-adjoin comparison.
-/

open scoped Polynomial
noncomputable section
namespace EnvelopeProperty.ReesPresentation
variable {A ι : Type*} [CommRing A] (g : ι → A)

private theorem evaluate_presentation (H : MvPolynomial ι A) :
    Polynomial.aeval (1 : A) (presentation g H) = MvPolynomial.aeval g H := by
  have h : (Polynomial.aeval (1 : A)).comp (presentation g) = MvPolynomial.aeval g := by
    ext i
    simp
  exact AlgHom.congr_fun h H

/-- The original quotient genuinely evaluates at the SAME entire generator family. -/
def quotientEvaluation : (MvPolynomial ι A ⧸ kernel g) →ₐ[A] A :=
  Ideal.Quotient.liftₐ (kernel g) (MvPolynomial.aeval g) fun H hH => by
    rw [← evaluate_presentation g H]
    rw [show presentation g H = 0 from hH, map_zero]

@[simp]
theorem quotientEvaluation_mk (H : MvPolynomial ι A) :
    quotientEvaluation g (Ideal.Quotient.mk (kernel g) H) = MvPolynomial.aeval g H := rfl

@[simp]
theorem quotientEvaluation_algebraMap (a : A) :
    quotientEvaluation g (algebraMap A (MvPolynomial ι A ⧸ kernel g) a) = a :=
  (quotientEvaluation g).commutes a

/-- Homogeneous evaluation scales on EVERY original polynomial and every actual coefficient algebra. -/
theorem aeval_mul_of_isHomogeneous {B : Type*} [CommRing B] [Algebra A B]
    {H : MvPolynomial ι A} {d : ℕ} (hH : H.IsHomogeneous d) (c : B) :
    MvPolynomial.aeval (fun i => algebraMap A B (g i) * c) H =
      algebraMap A B (MvPolynomial.aeval g H) * c ^ d := by
  have h : (Polynomial.aeval c).comp (presentation g) =
      MvPolynomial.aeval (fun i => algebraMap A B (g i) * c) := by
    ext i
    simp
  rw [← AlgHom.congr_fun h H, AlgHom.comp_apply, presentation_of_isHomogeneous g hH]
  simp

end EnvelopeProperty.ReesPresentation

namespace EnvelopeProperty.ReesChart
open ReesPresentation
variable {A ι : Type*} [CommRing A] (g : ι → A)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The SAME original kernel quotient, without any radical replacement. -/
abbrev Quotient := MvPolynomial ι A ⧸ kernel g

/-- The actual quotient component images of the genuine total-degree grading. -/
abbrev grading := GradedQuotient.grading (MvPolynomial.homogeneousSubmodule ι A) (kernel g)

instance quotientGradedRing : GradedRing (grading g) :=
  GradedQuotient.gradedRing _ _ (kernel_isHomogeneous g)

/-- The actual original quotient variable. -/
def generator (i : ι) : Quotient g := Ideal.Quotient.mk (kernel g) (MvPolynomial.X i)

theorem generator_mem (i : ι) : generator g i ∈ grading g 1 :=
  (GradedQuotient.gradedMk _ _).map_mem (MvPolynomial.isHomogeneous_X A i)

@[simp]
theorem quotientEvaluation_generator (i : ι) :
    quotientEvaluation g (generator g i) = g i := MvPolynomial.aeval_X _ _

/-- The GENUINE degree-zero homogeneous localization chart of the actual quotient. -/
abbrev Chart (j : ι) := HomogeneousLocalization.Away (grading g) (generator g j)

/-- The actual original degree-zero coordinate ratio, before any domain assumption. -/
def coordinateRatio (j i : ι) : Chart g j :=
  HomogeneousLocalization.Away.mk (grading g) (generator_mem g j) 1
    (generator g i) (by simpa only [one_smul] using generator_mem g i)

/-- The true original coefficient classes in the actual quotient degree zero. -/
def coefficientZero : A →+* grading g 0 where
  toFun a := ⟨Ideal.Quotient.mk (kernel g) (MvPolynomial.C a),
    (GradedQuotient.gradedMk _ _).map_mem (MvPolynomial.isHomogeneous_C ι a)⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

/-- Every actual original coefficient maps to its true constant fraction in the chart. -/
def coefficients (j : ι) : A →+* Chart g j :=
  (HomogeneousLocalization.fromZeroRingHom (grading g) (Submonoid.powers (generator g j))).comp
    (coefficientZero g)

@[instance_reducible]
def chartAlgebra (j : ι) : Algebra A (Chart g j) := (coefficients g j).toAlgebra

private local instance reesChartActualCoefficientAction (j : ι) : Algebra A (Chart g j) :=
  chartAlgebra g j

/-- The actual degree-zero inclusion retains the ENTIRE original coefficient action. -/
def chartVal (j : ι) : Chart g j →ₐ[A] Localization.Away (generator g j) where
  __ := algebraMap (Chart g j) (Localization.Away (generator g j))
  commutes' a := by
    change HomogeneousLocalization.val (coefficients g j a) = _
    change Localization.mk (Ideal.Quotient.mk (kernel g) (MvPolynomial.C a))
      (1 : Submonoid.powers (generator g j)) = _
    rw [IsScalarTower.algebraMap_apply A (Quotient g)]
    rfl

section Domain
variable [IsDomain A] (j : ι) (hj : g j ≠ 0)

include hj in
private theorem generatorImage_isUnit :
    IsUnit (((Algebra.ofId A (FractionRing A)).comp (quotientEvaluation g)) (generator g j)) := by
  change IsUnit (algebraMap A (FractionRing A) (quotientEvaluation g (generator g j)))
  rw [quotientEvaluation_generator]
  exact isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hj)

/-- The ACTUAL quotient evaluation extends through its genuine selected-coordinate localization. -/
def localizationEvaluation : Localization.Away (generator g j) →ₐ[A] FractionRing A :=
  IsLocalization.Away.liftAlgHom
    (f := (Algebra.ofId A (FractionRing A)).comp (quotientEvaluation g)) (generator g j)
    (generatorImage_isUnit g j hj)

@[simp]
theorem localizationEvaluation_algebraMap (a : Quotient g) :
    localizationEvaluation g j hj (algebraMap (Quotient g)
      (Localization.Away (generator g j)) a) =
      algebraMap A (FractionRing A) (quotientEvaluation g a) := by
  change IsLocalization.Away.lift (generator g j) (generatorImage_isUnit g j hj)
    (algebraMap (Quotient g) (Localization.Away (generator g j)) a) = _
  rw [IsLocalization.Away.lift_eq]
  rfl

/-- The actual WHOLE degree-zero chart map into the ORIGINAL fraction field. -/
def toFractionRing : Chart g j →ₐ[A] FractionRing A :=
  (localizationEvaluation g j hj).comp (chartVal g j)

/-- Every actual homogeneous fraction follows the entire original quotient evaluation. -/
theorem toFractionRing_mk (n : ℕ) (a : Quotient g) (ha : a ∈ grading g (n • (1 : ℕ))) :
    toFractionRing g j hj (HomogeneousLocalization.Away.mk (grading g) (generator_mem g j) n a ha) =
      algebraMap A (FractionRing A) (quotientEvaluation g a) /
        (algebraMap A (FractionRing A) (g j)) ^ n := by
  apply (eq_div_iff (pow_ne_zero n
    ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hj))).mpr
  let den : Submonoid.powers (generator g j) := ⟨generator g j ^ n, n, rfl⟩
  have h := congrArg (localizationEvaluation g j hj)
    (IsLocalization.mk'_spec (Localization.Away (generator g j)) a den)
  rw [map_mul] at h
  change localizationEvaluation g j hj
      (IsLocalization.mk' (Localization.Away (generator g j)) a den) *
    localizationEvaluation g j hj (algebraMap (Quotient g)
      (Localization.Away (generator g j)) (generator g j ^ n)) =
    localizationEvaluation g j hj (algebraMap (Quotient g)
      (Localization.Away (generator g j)) a) at h
  rw [localizationEvaluation_algebraMap, localizationEvaluation_algebraMap,
    map_pow, quotientEvaluation_generator, map_pow] at h
  change localizationEvaluation g j hj (Localization.mk a den) * _ = _
  rw [Localization.mk_eq_mk']
  exact h

/-- The actual chart map is injective on WHOLE homogeneous fractions. -/
theorem toFractionRing_injective : Function.Injective (toFractionRing g j hj) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading g) (generator_mem g j) z
  obtain ⟨H, hH⟩ := GradedQuotient.componentMap_surjective
    (MvPolynomial.homogeneousSubmodule ι A) (kernel g) (n • (1 : ℕ)) ⟨a, ha⟩
  have hHa : Ideal.Quotient.mk (kernel g) (H : MvPolynomial ι A) = a :=
    congrArg Subtype.val hH
  rw [toFractionRing_mk] at hz
  have hden : (algebraMap A (FractionRing A) (g j)) ^ n ≠ 0 :=
    pow_ne_zero n ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hj)
  have he : quotientEvaluation g a = 0 := by
    apply IsFractionRing.injective A (FractionRing A)
    simpa only [map_zero] using (div_eq_zero_iff.mp hz).resolve_right hden
  have hev : MvPolynomial.aeval g (H : MvPolynomial ι A) = 0 := by
    rw [← hHa, quotientEvaluation_mk] at he
    exact he
  have hk : (H : MvPolynomial ι A) ∈ kernel g := by
    change presentation g (H : MvPolynomial ι A) = 0
    rw [presentation_of_isHomogeneous g H.2, hev, map_zero, zero_mul]
  have ha0 : a = 0 := hHa.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hk)
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    ha0, Localization.mk_zero]

/-- The actual original fractions that generate the entire image chart. -/
def ratios (i : ι) : FractionRing A :=
  algebraMap A (FractionRing A) (g i) / algebraMap A (FractionRing A) (g j)

/-- Homogeneous scaling computes every original numerator at the ORIGINAL ratios. -/
theorem aeval_ratios {H : MvPolynomial ι A} {d : ℕ} (hH : H.IsHomogeneous d) :
    MvPolynomial.aeval (ratios g j) H =
      algebraMap A (FractionRing A) (MvPolynomial.aeval g H) /
        (algebraMap A (FractionRing A) (g j)) ^ d := by
  change MvPolynomial.aeval (fun i => algebraMap A (FractionRing A) (g i) /
    algebraMap A (FractionRing A) (g j)) H = _
  simpa only [div_eq_mul_inv, inv_pow] using
    aeval_mul_of_isHomogeneous g hH (algebraMap A (FractionRing A) (g j))⁻¹

/-- The original fraction-adjoin subalgebra, without a finite-family assumption. -/
def fractionAlgebra : Subalgebra A (FractionRing A) := Algebra.adjoin A (Set.range (ratios g j))

/-- EVERY chart element belongs to the actual original fraction-adjoin ring. -/
theorem range_toFractionRing_le_fractionAlgebra :
    (toFractionRing g j hj).range ≤ fractionAlgebra g j := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading g) (generator_mem g j) z
  obtain ⟨H, hH⟩ := GradedQuotient.componentMap_surjective
    (MvPolynomial.homogeneousSubmodule ι A) (kernel g) (n • (1 : ℕ)) ⟨a, ha⟩
  have hHa : Ideal.Quotient.mk (kernel g) (H : MvPolynomial ι A) = a :=
    congrArg Subtype.val hH
  change toFractionRing g j hj (HomogeneousLocalization.Away.mk (grading g)
    (generator_mem g j) n a ha) ∈ fractionAlgebra g j
  rw [toFractionRing_mk, ← hHa, quotientEvaluation_mk]
  have hdeg0 : (H : MvPolynomial ι A).IsHomogeneous (n • (1 : ℕ)) := H.2
  have hdeg : (H : MvPolynomial ι A).IsHomogeneous n := by
    simpa only [smul_eq_mul, mul_one] using hdeg0
  rw [← aeval_ratios g j hdeg]
  change MvPolynomial.aeval (ratios g j) (H : MvPolynomial ι A) ∈
    Algebra.adjoin A (Set.range (ratios g j))
  rw [← MvPolynomial.aeval_range]
  exact ⟨H, rfl⟩

/-- Each actual ratio is the value of the genuine degree-zero generator fraction. -/
theorem ratios_mem_range_toFractionRing (i : ι) :
    ratios g j i ∈ (toFractionRing g j hj).range := by
  refine ⟨coordinateRatio g j i, ?_⟩
  change toFractionRing g j hj (HomogeneousLocalization.Away.mk (grading g)
    (generator_mem g j) 1 (generator g i) _) = ratios g j i
  rw [toFractionRing_mk, quotientEvaluation_generator, pow_one]
  rfl

/-- Every genuine coordinate fraction has its ENTIRE actual original ratio value. -/
@[simp]
theorem toFractionRing_coordinateRatio (i : ι) :
    toFractionRing g j hj (coordinateRatio g j i) = ratios g j i := by
  change toFractionRing g j hj (HomogeneousLocalization.Away.mk (grading g)
    (generator_mem g j) 1 (generator g i) _) = _
  rw [toFractionRing_mk, quotientEvaluation_generator, pow_one]
  rfl

/-- The WHOLE original chart image equals the actual fraction-adjoin algebra. -/
theorem range_toFractionRing : (toFractionRing g j hj).range = fractionAlgebra g j := by
  apply le_antisymm (range_toFractionRing_le_fractionAlgebra g j hj)
  apply Algebra.adjoin_le
  rintro _ ⟨i, rfl⟩
  exact ratios_mem_range_toFractionRing g j hj i

/-- The GENUINE whole degree-zero Rees chart equivalence, preserving every original coefficient. -/
def fractionEquiv : Chart g j ≃ₐ[A] fractionAlgebra g j :=
  (AlgEquiv.ofInjective (toFractionRing g j hj) (toFractionRing_injective g j hj)).trans
    (Subalgebra.equivOfEq _ _ (range_toFractionRing g j hj))

/-- The chart equivalence has the SAME whole original fraction-field map. -/
@[simp]
theorem fractionEquiv_coe (z : Chart g j) :
    (fractionEquiv g j hj z : FractionRing A) = toFractionRing g j hj z := rfl

/-- Every original coefficient is retained by the actual algebra equivalence. -/
@[simp]
theorem fractionEquiv_algebraMap (a : A) :
    fractionEquiv g j hj (algebraMap A (Chart g j) a) =
      algebraMap A (fractionAlgebra g j) a := (fractionEquiv g j hj).commutes a

end Domain
end EnvelopeProperty.ReesChart
