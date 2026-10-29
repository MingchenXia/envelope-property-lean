import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsSaturation

/-! # SAME whole original ideal powers give actual cone saturation bounds -/

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
open ProjBerk
open Char0.EnvelopeGradedBaseIdealsCore
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- Genuine finite homogeneous powers, using only the actual native product. -/
def homogeneousPower (H : HomogeneousIdeal (ProjectiveGrading k[X] M)) :
    ℕ → HomogeneousIdeal (ProjectiveGrading k[X] M)
  | 0 => ⊤
  | l + 1 => homogeneousPower H l * H

/-- The homogeneous power retains the ENTIRE original ordinary ideal power. -/
theorem homogeneousPower_toIdeal (H : HomogeneousIdeal (ProjectiveGrading k[X] M)) (l : ℕ) :
    (homogeneousPower H l).toIdeal = H.toIdeal ^ l := by
  induction l with
  | zero => simp only [homogeneousPower, HomogeneousIdeal.toIdeal_top, pow_zero, Ideal.one_eq_top]
  | succ l ih =>
      change (homogeneousPower H l).toIdeal * H.toIdeal = H.toIdeal ^ (l + 1)
      rw [ih, pow_succ]

/-- Powers of the ORIGINAL homogeneous ideal retain the exact SAME whole
family ideal under actual sheafification and geometric pullback. -/
theorem quotientIdealSheaf_comap_pow
    (H : HomogeneousIdeal (ProjectiveGrading k[X] M)) (l : ℕ) :
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) (homogeneousPower H l)).comap
        (familyInclusion X) =
      ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) H).comap (familyInclusion X)) ^ l := by
  induction l with
  | zero =>
      simp only [homogeneousPower, pow_zero, Scheme.IdealSheafData.one_eq_top,
        quotientIdealSheaf_top, Scheme.IdealSheafData.comap_top]
  | succ l ih =>
      rw [homogeneousPower, quotientIdealSheaf_mul, Scheme.IdealSheafData.comap_mul, ih, pow_succ]

/-- For ANY actual whole original scheme ideal, its genuine power's cone
representative lies in the SAME original cone ideal power saturation.
No local comparison, coordinate power or saturation certificate is supplied. -/
theorem coneIdeal_pow_le_saturation (K : (familyScheme X).IdealSheafData) (l : ℕ) :
    coneIdeal X (K ^ l) ≤ X.saturation (coneIdeal X K ^ l) := by
  let H := homogeneousConeRepresentative X (K ^ l)
  let J := homogeneousPower (homogeneousConeRepresentative X K) l
  have hj : (GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) J).comap
      (familyInclusion X) = K ^ l := by
    exact (quotientIdealSheaf_comap_pow X (homogeneousConeRepresentative X K) l).trans
      (congrArg (fun I : (familyScheme X).IdealSheafData => I ^ l)
        (homogeneousConeRepresentative_comap X K))
  have hh : (GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M) H).comap
      (familyInclusion X) = K ^ l := homogeneousConeRepresentative_comap X (K ^ l)
  have h := map_cone_le_saturation_of_family_comap_le X H J (hh.le.trans hj.ge)
  have hmap : J.toIdeal.map (parameterConeQuotient X).toRingHom = coneIdeal X K ^ l := by
    change (homogeneousPower (homogeneousConeRepresentative X K) l).toIdeal.map
      (parameterConeQuotient X).toRingHom = coneIdeal X K ^ l
    rw [homogeneousPower_toIdeal, Ideal.map_pow]
    rfl
  rw [hmap] at h
  exact h

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
