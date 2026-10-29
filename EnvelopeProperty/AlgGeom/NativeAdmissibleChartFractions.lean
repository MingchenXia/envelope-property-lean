import EnvelopeProperty.AlgGeom.NativeAdmissibleCharts

/-! # Literal original quotient fractions in the genuine native chart -/
open scoped Classical
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open EnvelopeProperty.ProjBerk
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] nativeQuotientAwayAlgebra
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
private local instance qgr : GradedRing (GradedQuotient.grading (ProjectiveGrading k n) X.ideal) :=
  GradedQuotient.gradedRing _ X.ideal X.homogeneousIdeal.isHomogeneous
private def localMap (F : MvPolynomial (Fin (n+1)) k) :
    MvPolynomial (Fin (n+1)) k →ₐ[k] Localization.Away (Ideal.Quotient.mk X.ideal F) :=
  (IsScalarTower.toAlgHom k (MvPolynomial (Fin (n+1)) k ⧸ X.ideal) _).comp
    (Ideal.Quotient.mkₐ k X.ideal)
private def awayVal (F : MvPolynomial (Fin (n+1)) k) :
    X.nativeQuotientAway F →ₐ[k] Localization.Away (Ideal.Quotient.mk X.ideal F) where
  __ := algebraMap (X.nativeQuotientAway F) (Localization.Away (Ideal.Quotient.mk X.ideal F))
  commutes' c := by
    change Localization.mk (Ideal.Quotient.mk X.ideal (C c)) 1 = _
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin (n+1)) k ⧸ X.ideal)]
    rfl

private theorem equiv_val {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (a : QuotChartAlg X.ideal F d) :
    awayVal X F (X.quotChartNativeAwayEquiv hF hFI a) =
      quotChartLift X.ideal F d (localMap X F)
        (fun τ hτ => by
          change algebraMap (MvPolynomial (Fin (n+1)) k ⧸ X.ideal) _ (Ideal.Quotient.mk X.ideal τ) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr hτ,map_zero])
        (IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk X.ideal F)) a := by
  dsimp only [quotChartNativeAwayEquiv]
  erw [apply_quotChartEquiv]
  rfl

/-- The SAME original quotient-chart numerator retains its literal actual
homogeneous quotient localization fraction under the whole native comparison. -/
theorem quotChartNativeAwayEquiv_quotChartMk_mul
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (m : ℕ)
    (G : MvPolynomial (Fin (n+1)) k) :
    (X.quotChartNativeAwayEquiv hF hFI (quotChartMk X.ideal F d m G)).val *
      algebraMap (MvPolynomial (Fin (n+1)) k ⧸ X.ideal)
        (Localization.Away (Ideal.Quotient.mk X.ideal F)) (Ideal.Quotient.mk X.ideal F) ^ m =
      algebraMap (MvPolynomial (Fin (n+1)) k ⧸ X.ideal)
        (Localization.Away (Ideal.Quotient.mk X.ideal F))
          (Ideal.Quotient.mk X.ideal (homogeneousComponent (m*d) G)) := by
  change awayVal X F _ * localMap X F F ^ m = localMap X F _
  rw [equiv_val]
  exact quotChartLift_quotChartMk_mul_pow _ _ _ m G
/-- EVERY original homogeneous quotient-chart numerator is EXACTLY the
SAME genuine native homogeneous-away fraction, as a WHOLE ring element. -/
theorem quotChartNativeAwayEquiv_quotChartMk
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (m : ℕ)
    (G : MvPolynomial (Fin (n+1)) k) (hG : G.IsHomogeneous (m*d)) :
    X.quotChartNativeAwayEquiv hF hFI (quotChartMk X.ideal F d m G) =
      Away.mk (GradedQuotient.grading (ProjectiveGrading k n) X.ideal)
        (show Ideal.Quotient.mk X.ideal F ∈
          GradedQuotient.grading (ProjectiveGrading k n) X.ideal d from
          (GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal).map_mem hF)
        m (Ideal.Quotient.mk X.ideal G)
        (show Ideal.Quotient.mk X.ideal G ∈
          GradedQuotient.grading (ProjectiveGrading k n) X.ideal (m • d) from
          (GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal).map_mem
            (by simpa only [smul_eq_mul, ProjectiveGrading, MvPolynomial.mem_homogeneousSubmodule] using hG)) := by
  apply HomogeneousLocalization.val_injective
  apply ((IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (Ideal.Quotient.mk X.ideal F)) (Ideal.Quotient.mk X.ideal F)).pow m).mul_left_injective
  dsimp only
  erw [X.quotChartNativeAwayEquiv_quotChartMk_mul hF hFI m G,
    homogeneousComponent_eq_self hG, Away.val_mk, Localization.mk_eq_mk']
  symm
  change IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk X.ideal F))
      (Ideal.Quotient.mk X.ideal G)
      (⟨Ideal.Quotient.mk X.ideal F ^ m, ⟨m,rfl⟩⟩ :
        Submonoid.powers (Ideal.Quotient.mk X.ideal F)) *
      algebraMap (MvPolynomial (Fin (n+1)) k ⧸ X.ideal)
        (Localization.Away (Ideal.Quotient.mk X.ideal F)) (Ideal.Quotient.mk X.ideal F) ^ m =
      algebraMap (MvPolynomial (Fin (n+1)) k ⧸ X.ideal)
        (Localization.Away (Ideal.Quotient.mk X.ideal F)) (Ideal.Quotient.mk X.ideal G)
  simpa only [map_pow] using IsLocalization.mk'_spec
    (Localization.Away (Ideal.Quotient.mk X.ideal F)) (Ideal.Quotient.mk X.ideal G)
    (⟨Ideal.Quotient.mk X.ideal F ^ m, ⟨m,rfl⟩⟩ :
      Submonoid.powers (Ideal.Quotient.mk X.ideal F))
end EnvelopeProperty.ProjSubvariety
