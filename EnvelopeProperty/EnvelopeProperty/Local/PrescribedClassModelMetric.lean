import EnvelopeProperty.Local.PLIdealNormalizedPolarizedMetric
import EnvelopeProperty.Local.PLGerms
import EnvelopeProperty.Local.PositivityReductionCharts

/-! # Original local convexity on a TRUE model metric in the prescribed rational class -/
open scoped Classical Polynomial NNReal ENNReal
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

private theorem actualWeight_isConvexPLOn (hX : X.IsProjNormal)
    {a : ℚ} {φ : X.an → ℝ} (hφ : X.IsLocallyConvexAll a φ)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) (hda : (d : ℚ) = r*a)
    (C : ℤ) (I J : X.NativeProductModel.IdealSheafData)
    (hfin : ∀ w : X.an,
      modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
    (heq : ∀ w : X.an, (((r : ℝ)*φ w : ℝ) : EReal) =
      X.normalizedSimultaneousRatioWeight I J hfin hX w + ((C : ℝ) : EReal))
    (j : Fin (M+1)) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d)
    (hFI : F ∉ X.ideal) :
    IsConvexPLOn Set.univ (fun y =>
      X.normalizedSimultaneousPolynomialRatioWeight I J hfin hX j d F hF
        (X.chartInv F d hF hd y) + ((C : ℝ) : EReal)) := by
  have hconv := (hφ r d F hF hd hr hda hFI).smul (show 0 ≤ (r : ℚ) from Nat.cast_nonneg r)
  have hconv' : IsConvexPLOn Set.univ (fun y => ((r : ℝ) : EReal) *
      X.admChartFun r φ F d hF hd y) := by simpa only [Rat.cast_natCast] using hconv
  convert hconv' using 1
  funext y
  let x := X.chartInv F d hF hd y
  have hn : x.1.1.val F ≠ 0 := X.chartInv_val_ne_zero hF hd y
  have hw : (((r : ℝ)*φ x - (C : ℝ) : ℝ) : EReal) =
      X.normalizedSimultaneousRatioWeight I J hfin hX x := by
    have h := congrArg (fun z : EReal => z - ((C : ℝ) : EReal)) (heq x)
    simpa only [EReal.add_sub_cancel_right, ← EReal.coe_sub] using h
  rw [X.normalizedSimultaneousPolynomialRatioWeight_eq I J hfin hX j d F hF,
    ← hw, ProjBerk.logAbs_eq_coe_log hn]
  simp only [admChartFun, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_add]
  apply congrArg ((↑) : ℝ → EReal)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  ring

/-- ORIGINAL local O(a)-convexity alone derives a TRUE actual normal ratio
model with integer polarization degree d=r*a, and every SAME original
homogeneous local-section weight is convex PL on its actual ORIGINAL chart.
This identifies the prescribed-class metric; no nefness is asserted or assumed. -/
theorem IsLocallyConvexAll.exists_prescribedClass_normalizedRatioMetric
    (hX : X.IsProjNormal) {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ}
    (hφ : X.IsLocallyConvexAll a φ) :
    ∃ (r d : ℕ) (_hr : 0 < r) (hd : 0 < d), (d : ℚ) = r*a ∧
      ∃ (C : ℤ) (I J : X.NativeProductModel.IdealSheafData)
        (hfin : ∀ w : X.an,
          modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
          modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥),
        (∀ w : X.an, (((r : ℝ)*φ w : ℝ) : EReal) =
          X.normalizedSimultaneousRatioWeight I J hfin hX w + ((C : ℝ) : EReal)) ∧
        ∀ (j : Fin (M+1)) (F : MvPolynomial (Fin (M+1)) k) (hF : F.IsHomogeneous d),
          F ∉ X.ideal → IsConvexPLOn Set.univ (fun y =>
            X.normalizedSimultaneousPolynomialRatioWeight I J hfin hX j d F hF
              (X.chartInv F d hF hd y) + ((C : ℝ) : EReal)) := by
  have hPL : X.IsPL φ := (hφ.isLocallyConvex ha).isPL
  have hscaled : X.IsPL (fun w => (a.den : ℝ)*φ w) := by
    simpa only [Rat.cast_natCast] using hPL.smul (a.den : ℚ)
  obtain ⟨s, hs, C, I, J, hfin, heq⟩ :=
    hscaled.exists_normalizedSimultaneousRatioMetric_models X hX
  let r := s*a.den
  let d := s*a.num.toNat
  have hnum : 0 < a.num.toNat := by have h := Rat.num_pos.mpr ha; omega
  have hr : 0 < r := Nat.mul_pos hs a.den_pos
  have hd : 0 < d := Nat.mul_pos hs hnum
  have hda : (d : ℚ) = r*a := by
    have hp : (a.num.toNat : ℚ) = a.den*a := by
      rw [mul_comm, Rat.mul_den_eq_num]
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr ha).le
    dsimp only [r, d]
    rw [Nat.cast_mul, Nat.cast_mul, hp, mul_assoc]
  have heq' (w : X.an) : (((r : ℝ)*φ w : ℝ) : EReal) =
      X.normalizedSimultaneousRatioWeight I J hfin hX w + ((C : ℝ) : EReal) := by
    simpa only [r, Nat.cast_mul, mul_assoc] using heq w
  refine ⟨r, d, hr, hd, hda, C, I, J, hfin, heq', ?_⟩
  intro j F hF hFI
  exact actualWeight_isConvexPLOn X hX hφ r d hr hd hda C I J hfin heq' j F hF hFI

end EnvelopeProperty.ProjSubvariety
