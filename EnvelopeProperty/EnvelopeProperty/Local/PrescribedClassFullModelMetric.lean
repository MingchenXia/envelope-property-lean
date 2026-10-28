import EnvelopeProperty.Local.PLFullNormalizedMetricModels
import EnvelopeProperty.Local.PLNormalizedFullPointPolarizedMetric
import EnvelopeProperty.Local.PrescribedClassModelMetric

/-! # The ORIGINAL prescribed rational class on the WHOLE actual normal metric -/
open scoped Classical Polynomial NNReal ENNReal
open CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich.RelativeSchemeValuedPoint
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The entire projected original product point at a genuine normalized Gauss
lift is the SAME original product Gauss point, not merely its support. -/
theorem normalizedSimultaneousProductPointAt_gauss (hX : X.IsProjNormal) (w : X.an) :
    X.normalizedSimultaneousProductPointAt I J hfin
      (X.normalizedSimultaneousGaussPoint I J hfin hX w) = X.nativeProductGaussPoint w := by
  unfold normalizedSimultaneousProductPointAt
  rw [X.map_normalizedSimultaneousGaussPoint, X.map_simultaneousIdealBlowupGaussPoint]

/-- Actual whole original analytic restriction recovers the SAME original point. -/
theorem normalizedSimultaneousBaseRestrictionAt_gauss (hX : X.IsProjNormal) (w : X.an) :
    X.normalizedSimultaneousBaseRestrictionAt I J hfin
      (X.normalizedSimultaneousGaussPoint I J hfin hX w) = w := by
  unfold normalizedSimultaneousBaseRestrictionAt
  rw [X.normalizedSimultaneousProductPointAt_gauss, X.nativeProductBaseRestriction_gauss]

private theorem actualWeight_isConvexPLOn (hX : X.IsProjNormal)
    {a : ℚ} {φ : X.an → ℝ} (hφ : X.IsLocallyConvexAll a φ)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) (hda : (d : ℚ) = r*a)
    (C : ℤ)
    (hfinAll : ∀ z : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
      modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥)
    (heq : ∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
      (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
        X.normalizedSimultaneousRatioWeightAt I J hfin y
          (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 + ((C : ℝ) : EReal))
    (j : Fin (M+1)) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d)
    (hFI : F ∉ X.ideal) :
    IsConvexPLOn Set.univ (fun z =>
      let y := X.normalizedSimultaneousGaussPoint I J hfin hX (X.chartInv F d hF hd z)
      X.normalizedSimultaneousPolynomialRatioWeightAt I J hfin y
        (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 j d F hF +
          ((C : ℝ) : EReal)) := by
  have hconv := (hφ r d F hF hd hr hda hFI).smul (show 0 ≤ (r : ℚ) from Nat.cast_nonneg r)
  have hconv' : IsConvexPLOn Set.univ (fun z => ((r : ℝ) : EReal) *
      X.admChartFun r φ F d hF hd z) := by simpa only [Rat.cast_natCast] using hconv
  convert hconv' using 1
  funext z
  let w := X.chartInv F d hF hd z
  let y := X.normalizedSimultaneousGaussPoint I J hfin hX w
  have hres : X.normalizedSimultaneousBaseRestrictionAt I J hfin y = w :=
    X.normalizedSimultaneousBaseRestrictionAt_gauss I J hfin hX w
  have hn : w.1.1.val F ≠ 0 := X.chartInv_val_ne_zero hF hd z
  have hw : (((r : ℝ)*φ w - (C : ℝ) : ℝ) : EReal) =
      X.normalizedSimultaneousRatioWeightAt I J hfin y
        (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 := by
    have h := congrArg (fun t : EReal => t - ((C : ℝ) : EReal)) (heq y)
    rw [hres] at h
    simpa only [EReal.add_sub_cancel_right, ← EReal.coe_sub] using h
  change X.normalizedSimultaneousPolynomialRatioWeightAt I J hfin y _ j d F hF + _ = _
  rw [X.normalizedSimultaneousPolynomialRatioWeightAt_eq, hres, ← hw,
    ProjBerk.logAbs_eq_coe_log hn]
  simp only [admChartFun, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_add]
  apply congrArg ((↑) : ℝ → EReal)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  ring

/-- ORIGINAL local O(a)-convexity produces a TRUE whole normal model metric
in the EXACT original class d=r*a. Its genuine canonical section weights
hold at ALL actual model points; the SAME original admissible chart weights
are convex PL. No nef/curve-degree/positivity hypothesis is added. -/
theorem IsLocallyConvexAll.exists_prescribedClass_full_normalizedRatioMetric
    (hX : X.IsProjNormal) {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ}
    (hφ : X.IsLocallyConvexAll a φ) :
    ∃ (r d : ℕ) (_hr : 0 < r) (hd : 0 < d), (d : ℚ) = r*a ∧
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
        (∀ (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
            (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
            (j : Fin (M+1)) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d),
          X.normalizedSimultaneousPolynomialRatioWeightAt I J hfin y
            (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 j d F hF =
          (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) - (C : ℝ) : ℝ) : EReal) -
            ProjBerk.logAbs F (X.normalizedSimultaneousBaseRestrictionAt I J hfin y).1) ∧
        ∀ (j : Fin (M+1)) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d),
          F ∉ X.ideal → IsConvexPLOn Set.univ (fun z =>
            let y := X.normalizedSimultaneousGaussPoint I J hfin hX (X.chartInv F d hF hd z)
            X.normalizedSimultaneousPolynomialRatioWeightAt I J hfin y
              (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 j d F hF +
                ((C : ℝ) : EReal)) := by
  have hPL : X.IsPL φ := (hφ.isLocallyConvex ha).isPL
  have hscaled : X.IsPL (fun w => (a.den : ℝ)*φ w) := by
    simpa only [Rat.cast_natCast] using hPL.smul (a.den : ℚ)
  obtain ⟨s,hs,C,I,J,hfinAll,heq⟩ := hscaled.exists_full_normalizedRatioMetric_models X
  let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
  let r := s*a.den
  let d := s*a.num.toNat
  have hnum : 0 < a.num.toNat := by have h := Rat.num_pos.mpr ha; omega
  have hr : 0 < r := Nat.mul_pos hs a.den_pos
  have hd : 0 < d := Nat.mul_pos hs hnum
  have hda : (d : ℚ) = r*a := by
    have hp : (a.num.toNat : ℚ) = a.den*a := by
      rw [mul_comm, Rat.mul_den_eq_num]
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr ha).le
    dsimp only [r,d]
    rw [Nat.cast_mul, Nat.cast_mul, hp, mul_assoc]
  have heq' (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin)) :
      (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
        X.normalizedSimultaneousRatioWeightAt I J hfin y
          (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 + ((C : ℝ) : EReal) := by
    simpa only [r, Nat.cast_mul, mul_assoc] using heq y
  refine ⟨r,d,hr,hd,hda,C,I,J,hfinAll,?_⟩
  intro hfin'
  refine ⟨heq',?_,?_⟩
  · intro y j F hF
    rw [X.normalizedSimultaneousPolynomialRatioWeightAt_eq]
    congr 1
    have h := congrArg (fun t : EReal => t - ((C : ℝ) : EReal)) (heq' y)
    symm
    simpa only [EReal.add_sub_cancel_right, ← EReal.coe_sub] using h
  intro j F hF hFI
  exact actualWeight_isConvexPLOn X I J hfin hX hφ r d hr hd hda C hfinAll heq' j F hF hFI
end EnvelopeProperty.ProjSubvariety
