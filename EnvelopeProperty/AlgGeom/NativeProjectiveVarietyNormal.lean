/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.NativeProjectiveVarietyComparison
import EnvelopeProperty.Projective.SubvarietyNormal
import EnvelopeProperty.Berkovich.SchemeNormalStalks

/-! # Normality of the SAME original native projective variety -/
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open EnvelopeProperty EnvelopeProperty.ProjBerk
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace EnvelopeProperty.ProjSubvariety
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
private local instance qgr : GradedRing (GradedQuotient.grading (ProjectiveGrading k n) X.ideal) :=
  GradedQuotient.gradedRing _ X.ideal X.homogeneousIdeal.isHomogeneous
/-- The actual homogeneous away ring of the SAME original homogeneous quotient. -/
abbrev nativeQuotientAway (σ : MvPolynomial (Fin (n+1)) k) :=
  Away (GradedQuotient.grading (ProjectiveGrading k n) X.ideal) (Ideal.Quotient.mk X.ideal σ)
private def quotientCoeffZero : k →+* GradedQuotient.grading (ProjectiveGrading k n) X.ideal 0 where
  toFun c := GradedQuotient.componentMap _ _ 0 ⟨C c, isHomogeneous_C _ c⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)
@[instance_reducible]
private def awayAlgebra (σ : MvPolynomial (Fin (n+1)) k) : Algebra k (X.nativeQuotientAway σ) :=
  ((fromZeroRingHom _ _).comp (quotientCoeffZero X)).toAlgebra
private local instance qa (σ : MvPolynomial (Fin (n+1)) k) : Algebra k (X.nativeQuotientAway σ) := awayAlgebra X σ
private def awayVal (σ : MvPolynomial (Fin (n+1)) k) :
    X.nativeQuotientAway σ →ₐ[k] Localization.Away (Ideal.Quotient.mk X.ideal σ) where
  __ := algebraMap (X.nativeQuotientAway σ) (Localization.Away (Ideal.Quotient.mk X.ideal σ))
  commutes' c := by
    change (fromZeroRingHom _ _ (quotientCoeffZero X c)).val = _
    change Localization.mk (Ideal.Quotient.mk X.ideal (C c)) 1 = _
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin (n+1)) k ⧸ X.ideal)]
    rfl
private theorem awayVal_apply (σ : MvPolynomial (Fin (n+1)) k) (a : X.nativeQuotientAway σ) :
    awayVal X σ a = a.val := rfl

private def quotientLocalizationMap (σ : MvPolynomial (Fin (n+1)) k) :
    MvPolynomial (Fin (n+1)) k →ₐ[k] Localization.Away (Ideal.Quotient.mk X.ideal σ) :=
  (IsScalarTower.toAlgHom k (MvPolynomial (Fin (n+1)) k ⧸ X.ideal) _).comp
    (Ideal.Quotient.mkₐ k X.ideal)

private theorem awayVal_mk_mul {σ : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hσ : σ.IsHomogeneous d) (m : ℕ) (τ : MvPolynomial (Fin (n+1)) k)
    (hτ : τ.IsHomogeneous (m * d)) :
    awayVal X σ (Away.mk _ ((GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal).map_mem hσ)
      m (Ideal.Quotient.mk X.ideal τ)
      ((GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal).map_mem (by simpa using hτ))) *
        quotientLocalizationMap X σ σ ^ m = quotientLocalizationMap X σ τ := by
  rw [awayVal_apply, Away.val_mk, Localization.mk_eq_mk']
  change IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk X.ideal σ))
      (Ideal.Quotient.mk X.ideal τ)
      (⟨Ideal.Quotient.mk X.ideal σ ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers (Ideal.Quotient.mk X.ideal σ)) *
    algebraMap (MvPolynomial (Fin (n+1)) k ⧸ X.ideal)
      (Localization.Away (Ideal.Quotient.mk X.ideal σ)) (Ideal.Quotient.mk X.ideal σ) ^ m =
    algebraMap (MvPolynomial (Fin (n+1)) k ⧸ X.ideal)
      (Localization.Away (Ideal.Quotient.mk X.ideal σ)) (Ideal.Quotient.mk X.ideal τ)
  simpa only [map_pow] using IsLocalization.mk'_spec
    (Localization.Away (Ideal.Quotient.mk X.ideal σ)) (Ideal.Quotient.mk X.ideal τ)
    (⟨Ideal.Quotient.mk X.ideal σ ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers (Ideal.Quotient.mk X.ideal σ))

/-- The WHOLE original quotient chart algebra is the ACTUAL native quotient away ring. -/
def quotChartNativeAwayEquiv {σ : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hσ : σ.IsHomogeneous d) (hσI : σ ∉ X.ideal) :
    QuotChartAlg X.ideal σ d ≃ₐ[k] X.nativeQuotientAway σ := by
  let S := MvPolynomial (Fin (n+1)) k ⧸ X.ideal
  let s : S := Ideal.Quotient.mk X.ideal σ
  have hs : s ≠ 0 := fun h => hσI (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hle : Submonoid.powers s ≤ nonZeroDivisors S := powers_le_nonZeroDivisors_of_noZeroDivisors hs
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) := IsLocalization.injective _ hle
  let φ := quotientLocalizationMap X σ
  have hφI : ∀ τ ∈ X.ideal, φ τ = 0 := fun τ hτ => by
    change algebraMap S _ (Ideal.Quotient.mk X.ideal τ) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hτ, map_zero]
  have hker : ∀ τ, φ τ = 0 → τ ∈ X.ideal := fun τ hτ => by
    change algebraMap S _ (Ideal.Quotient.mk X.ideal τ) = 0 at hτ
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ hinj).mp hτ)
  have hσu : IsUnit (φ σ) := IsLocalization.Away.algebraMap_isUnit s
  apply quotChartEquiv X.ideal σ d φ hφI hσu hσ (fun _ τ _ => hker τ) (awayVal X σ)
    (HomogeneousLocalization.val_injective _)
  ext z
  constructor
  · intro hz
    obtain ⟨m, τ, hτ, heq⟩ := (mem_range_quotChartLift φ hφI hσu hσ).mp hz
    refine ⟨Away.mk _ ((GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal).map_mem hσ)
      m (Ideal.Quotient.mk X.ideal τ)
      ((GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal).map_mem (by simpa using hτ)), ?_⟩
    apply (hσu.pow m).mul_left_injective
    exact (awayVal_mk_mul X hσ m τ hτ).trans heq.symm
  · rintro ⟨a, rfl⟩
    obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective _
      ((GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal).map_mem hσ) a
    obtain ⟨τ, hτ⟩ := GradedQuotient.componentMap_surjective (ProjectiveGrading k n) X.ideal
      (m • d) ⟨a, ha⟩
    have heq : Ideal.Quotient.mk X.ideal τ = a := congrArg Subtype.val hτ
    subst a
    apply (mem_range_quotChartLift φ hφI hσu hσ).mpr
    refine ⟨m, τ, by simpa only [ProjectiveGrading, MvPolynomial.mem_homogeneousSubmodule, smul_eq_mul] using τ.2, ?_⟩
    have h := awayVal_mk_mul X hσ m τ (by simpa only [ProjectiveGrading, MvPolynomial.mem_homogeneousSubmodule, smul_eq_mul] using τ.2)
    exact h

/-- The original projective-normality premise derives normality of the SAME actual native away ring. -/
theorem nativeQuotientAway_isIntegrallyClosed (hX : X.IsProjNormal)
    {σ : MvPolynomial (Fin (n+1)) k} {d : ℕ} (hσ : σ.IsHomogeneous d) (hσI : σ ∉ X.ideal) :
    IsIntegrallyClosed (X.nativeQuotientAway σ) := by
  let : IsIntegrallyClosed (QuotChartAlg X.ideal σ d) := X.isIntegrallyClosed_quotChartAlg hX hσ hσI
  exact IsIntegrallyClosed.of_equiv (R := QuotChartAlg X.ideal σ d)
    (X.quotChartNativeAwayEquiv hσ hσI).toRingEquiv
/-- EVERY stalk of the ACTUAL quotient Proj is normal, derived through its genuine original affine cover. -/
theorem nativeScheme_stalk_isIntegrallyClosed (hX : X.IsProjNormal) (x : X.nativeScheme) :
    IsIntegrallyClosed (X.nativeScheme.presheaf.stalk x) := by
  let 𝒬 := GradedQuotient.grading (ProjectiveGrading k n) X.ideal
  obtain ⟨i, q, hq⟩ := (Proj.affineOpenCover 𝒬).openCover.exists_eq x
  obtain ⟨σ, hσ⟩ := GradedQuotient.componentMap_surjective (ProjectiveGrading k n) X.ideal
    (i.1 : ℕ) i.2
  have heq : Ideal.Quotient.mk X.ideal σ = i.2 := congrArg Subtype.val hσ
  have hm : (Proj.affineOpenCover 𝒬).f i q ∈ Proj.basicOpen 𝒬 (i.2 : _) := by
    have hm' : (Proj.affineOpenCover 𝒬).f i q ∈ ((Proj.affineOpenCover 𝒬).f i).opensRange := ⟨q, rfl⟩
    simpa only [Proj.affineOpenCover_f, Proj.opensRange_awayι] using hm'
  have hσI : (σ : MvPolynomial (Fin (n+1)) k) ∉ X.ideal := by
    intro hs
    have hz : (i.2 : MvPolynomial (Fin (n+1)) k ⧸ X.ideal) = 0 :=
      heq.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hs)
    rw [hz, Proj.basicOpen_zero] at hm
    exact hm
  have hσhom : (σ : MvPolynomial (Fin (n+1)) k).IsHomogeneous (i.1 : ℕ) := σ.2
  let e := X.quotChartNativeAwayEquiv hσhom hσI
  let : IsDomain (QuotChartAlg X.ideal σ (i.1 : ℕ)) := isDomain_quotChartAlg hσI
  have : IsDomain (X.nativeQuotientAway σ) := e.toRingEquiv.symm.toMulEquiv.isDomain _
  have : IsIntegrallyClosed (X.nativeQuotientAway σ) :=
    X.nativeQuotientAway_isIntegrallyClosed hX hσhom hσI
  have : IsDomain (Away 𝒬 (i.2 : MvPolynomial (Fin (n+1)) k ⧸ X.ideal)) := heq ▸ inferInstance
  have : IsIntegrallyClosed (Away 𝒬 (i.2 : MvPolynomial (Fin (n+1)) k ⧸ X.ideal)) := heq ▸ inferInstance
  have : IsDomain ((Proj.affineOpenCover 𝒬).X i) :=
    inferInstanceAs (IsDomain (Away 𝒬 (i.2 : MvPolynomial (Fin (n+1)) k ⧸ X.ideal)))
  have : IsIntegrallyClosed ((Proj.affineOpenCover 𝒬).X i) :=
    inferInstanceAs (IsIntegrallyClosed (Away 𝒬 (i.2 : MvPolynomial (Fin (n+1)) k ⧸ X.ideal)))
  have : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  rw [← hq]
  have : IsIntegrallyClosed ((Spec ((Proj.affineOpenCover 𝒬).X i)).presheaf.stalk q) :=
    IsIntegrallyClosed.of_equiv
      (Spec.stalkIso ((Proj.affineOpenCover 𝒬).X i) q).commRingCatIsoToRingEquiv.symm
  exact IsIntegrallyClosed.of_equiv
    (asIso (((Proj.affineOpenCover 𝒬).f i).stalkMap q)).commRingCatIsoToRingEquiv.symm

/-- The original projectively-normal homogeneous quotient derives integral
closedness of EVERY stalk of the SAME existing original closed-subscheme variety. -/
theorem originalNativeScheme_stalk_isIntegrallyClosed (hX : X.IsProjNormal) (x : X.NativeScheme) :
    IsIntegrallyClosed (X.NativeScheme.presheaf.stalk x) := by
  have : IsIntegrallyClosed (X.nativeScheme.presheaf.stalk (X.quotientNativeIso.inv x)) :=
    X.nativeScheme_stalk_isIntegrallyClosed hX _
  exact IsIntegrallyClosed.of_equiv
    (asIso (X.quotientNativeIso.inv.stalkMap x)).commRingCatIsoToRingEquiv

/-- The actual existing original variety is geometrically unibranch,
with the standard structural class derived from its actual original normal stalks. -/
theorem originalNativeScheme_isGeometricallyUnibranch (hX : X.IsProjNormal) :
    EnvelopeProperty.IsGeometricallyUnibranchScheme X.NativeScheme := by
  let : IsIntegral X.NativeScheme := X.originalNativeScheme_isIntegral
  exact EnvelopeProperty.IsGeometricallyUnibranchScheme.of_normal_stalks X.NativeScheme
    (fun _ => inferInstance) (X.originalNativeScheme_stalk_isIntegrallyClosed hX)

end EnvelopeProperty.ProjSubvariety
