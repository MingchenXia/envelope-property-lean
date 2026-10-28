import EnvelopeProperty.AlgGeom.NativeAdmissibleConvexity
import EnvelopeProperty.Berkovich.SchemeConvexPLAlgebra
import EnvelopeProperty.Local.PLNormalizedOriginalProjection
import EnvelopeProperty.Local.PrescribedClassFullModelMetric

/-! # Actual intrinsic convexity of the original prescribed-class model metric -/
open scoped Classical Polynomial NNReal
open CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich.RelativeSchemeValuedPoint
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The actual original homogeneous form-open on the whole normalized-model
point space, pulled back by the literal original scheme projection. -/
def normalizedSimultaneousAdmissibleAnalyticLocus (F : MvPolynomial (Fin (n+1)) k) :
    Set (RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin)) :=
  RelativeSchemeValuedPoint.mapOverBase Polynomial.C
    (fun c => Spectrum.gauss_val_C (Spectrum.ofValuation (1 : Valuation k ℝ≥0)) gaussRadius c)
    (X.normalizedSimultaneousOriginalProjection I J hfin)
    (X.normalizedSimultaneousOriginalProjection_over_base I J hfin) ⁻¹'
      X.nativeAdmissibleAnalyticLocus F

/-- The genuine original model form-open is exactly nonvanishing of the SAME
original form on the actual original analytic restriction, at EVERY model point. -/
theorem mem_normalizedSimultaneousAdmissibleAnalyticLocus
    (F : MvPolynomial (Fin (n+1)) k)
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin)) :
    y ∈ X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin F ↔
      (X.normalizedSimultaneousBaseRestrictionAt I J hfin y).1.1.val F ≠ 0 := by
  change (RelativeSchemeValuedPoint.mapOverBase Polynomial.C
    (fun c => Spectrum.gauss_val_C (Spectrum.ofValuation (1 : Valuation k ℝ≥0)) gaussRadius c)
    (X.normalizedSimultaneousOriginalProjection I J hfin)
    (X.normalizedSimultaneousOriginalProjection_over_base I J hfin) y).1.point ∈ X.nativeAdmissibleOpen F ↔ _
  rw [← X.nativeAnalyticHomeomorph_normalizedSimultaneousBaseRestrictionAt I J hfin y]
  exact X.nativeAnalyticHomeomorph_mem_nativeAdmissibleOpen _ F

private theorem actualAdmissibleWeight_isConvexPLOn
    {a : ℚ} {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) (hda : (d : ℚ) = r*a)
    (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) :
    RelativeSchemeValuedPoint.IsConvexPLOn
      (X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin F)
      (fun y =>
        let w := X.normalizedSimultaneousBaseRestrictionAt I J hfin y
        ((φ w - (r : ℝ)⁻¹ * Real.log (w.1.1.val F : ℝ) : ℝ) : EReal)) := by
  have hc := hconv.nativeAdmissibleWeight_comp_mapOverBase X r d hr hd hda F hF hFI
    (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) Polynomial.C
    (fun c => Spectrum.gauss_val_C (Spectrum.ofValuation (1 : Valuation k ℝ≥0)) gaussRadius c)
    (X.normalizedSimultaneousOriginalProjection I J hfin)
    (X.normalizedSimultaneousOriginalProjection_over_base I J hfin)
  apply hc.congr
  intro y _
  rw [← X.nativeAnalyticHomeomorph_normalizedSimultaneousBaseRestrictionAt I J hfin y]
  simp only [nativeAdmissibleWeight,Homeomorph.symm_apply_apply]

private theorem actualPolarizedWeight_isConvexPLOn
    {a : ℚ} {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) (hda : (d : ℚ) = r*a) (C : ℤ)
    (hfinAll : ∀ z : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        X.nativeProductStructure,
      modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥)
    (heq : ∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
      (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
        X.normalizedSimultaneousRatioWeightAt I J hfin y
          (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 + ((C : ℝ) : EReal))
    (j : Fin (n+1)) (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) :
    RelativeSchemeValuedPoint.IsConvexPLOn
      (X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin F)
      (fun y => X.normalizedSimultaneousPolynomialRatioWeightAt I J hfin y
        (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 j d F hF) := by
  have hc := (actualAdmissibleWeight_isConvexPLOn X I J hfin hconv r d hr hd hda F hF hFI).smul
    (show 0 ≤ (r : ℚ) from Nat.cast_nonneg r)
  have ht := hc.add_const (-(C : ℚ))
  apply ht.congr
  intro y hy
  have hn := (X.mem_normalizedSimultaneousAdmissibleAnalyticLocus I J hfin F y).mp hy
  have hw : (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) - (C : ℝ) : ℝ) : EReal) =
      X.normalizedSimultaneousRatioWeightAt I J hfin y
        (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 := by
    have h := congrArg (fun t : EReal => t - ((C : ℝ) : EReal)) (heq y)
    simpa only [EReal.add_sub_cancel_right,← EReal.coe_sub] using h
  rw [X.normalizedSimultaneousPolynomialRatioWeightAt_eq,← hw,ProjBerk.logAbs_eq_coe_log hn]
  simp only [Rat.cast_natCast,Rat.cast_neg,Rat.cast_intCast,← EReal.coe_mul,← EReal.coe_sub,
    ← EReal.coe_add]
  apply congrArg ((↑) : ℝ → EReal)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  ring

/-- ORIGINAL local O(a)-convexity constructs a genuine normal-model metric in
EXACT original class d=r*a whose TRUE polarized section weights are intrinsically
convex in ACTUAL regular units at ALL actual model points of every original
admissible form-open. No nefness or slope/degree certificate is supplied. -/
theorem IsLocallyConvexAll.exists_prescribedClass_intrinsicConvex_normalizedRatioMetric
    (hX : X.IsProjNormal) {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ}
    (hconv : X.IsLocallyConvexAll a φ) :
    ∃ (r d : ℕ) (_hr : 0 < r) (_hd : 0 < d), (d : ℚ) = r*a ∧
      ∃ (C : ℤ) (I J : X.NativeProductModel.IdealSheafData)
        (hfinAll : ∀ z : RelativeSchemeValuedPoint
            (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
          modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
          modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥),
        let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
        (∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
            (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
          (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
            X.normalizedSimultaneousRatioWeightAt I J hfin y
              (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 + ((C : ℝ) : EReal)) ∧
        ∀ (j : Fin (n+1)) (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d),
          F ∉ X.ideal → RelativeSchemeValuedPoint.IsConvexPLOn
            (X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin F)
            (fun y => X.normalizedSimultaneousPolynomialRatioWeightAt I J hfin y
              (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 j d F hF) := by
  obtain ⟨r,d,hr,hd,hda,C,I,J,hfinAll,heq,_hweights,_hGauss⟩ :=
    hconv.exists_prescribedClass_full_normalizedRatioMetric X hX ha
  refine ⟨r,d,hr,hd,hda,C,I,J,hfinAll,heq,?_⟩
  intro j F hF hFI
  exact actualPolarizedWeight_isConvexPLOn X I J _ hconv r d hr hd hda C hfinAll heq j F hF hFI

end EnvelopeProperty.ProjSubvariety
