import EnvelopeProperty.AlgGeom.NativeAdmissibleChartAnalytic
import EnvelopeProperty.Berkovich.SchemeAffinePaperConvexity
import EnvelopeProperty.Local.PositivityImport

/-! # Original admissible convexity on actual native quotient charts -/
open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Classical
open EnvelopeProperty.ProjBerk EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)

/-- The true original analytic point obtained from an actual native quotient-chart
point by the literal original scheme chart map. -/
def nativeAdmissibleAnalyticProjection
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0)
      (Spec.map (CommRingCat.ofHom (R := k) (S := QuotChartAlg X.ideal F d) (algebraMap k (QuotChartAlg X.ideal F d))))) : X.an :=
  X.nativeAnalyticHomeomorph.symm (RelativeSchemeValuedPoint.map
    (X.nativeAdmissibleChartMap hF hFI hd) (X.nativeAdmissibleChartMap_over_base hF hFI hd) y)

/-- This actual original scheme projection is exactly the original chart inverse
of the SAME original affine seminorm point. -/
theorem nativeAdmissibleAnalyticProjection_eq_chartInv
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0)
      (Spec.map (CommRingCat.ofHom (R := k) (S := QuotChartAlg X.ideal F d) (algebraMap k (QuotChartAlg X.ideal F d))))) :
    X.nativeAdmissibleAnalyticProjection hF hFI hd y =
      X.chartInv F d hF hd (RelativeSchemeValuedPoint.affineBerkHomeomorph y) := by
  apply X.nativeAnalyticHomeomorph.injective
  rw [nativeAdmissibleAnalyticProjection,Homeomorph.apply_symm_apply]
  apply Subtype.ext
  change SchemeValuedPoint.map (X.nativeAdmissibleChartMap hF hFI hd) y.1 = _
  rw [X.nativeAnalyticHomeomorph_chartInv hF hFI hd]
  apply congrArg (SchemeValuedPoint.map (X.nativeAdmissibleChartMap hF hFI hd))
  have hc := congrArg Subtype.val
    (RelativeSchemeValuedPoint.affineBerkHomeomorph.symm_apply_apply y)
  exact hc.symm

/-- The ORIGINAL admissible section weight on the actual native quotient chart,
using its true whole projected point and the SAME original homogeneous form. -/
def nativeAdmissibleChartWeight (m : ℕ) (φ : X.an → ℝ)
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0)
      (Spec.map (CommRingCat.ofHom (R := k) (S := QuotChartAlg X.ideal F d) (algebraMap k (QuotChartAlg X.ideal F d))))) : EReal :=
  let w := X.nativeAdmissibleAnalyticProjection hF hFI hd y
  ((φ w - (m : ℝ)⁻¹ * Real.log ((w : ProjBerk k n).1.val F : ℝ) : ℝ) : EReal)

/-- Genuine intrinsic regular-unit convexity of the SAME original section weight
follows from the original admissible coefficient-chart convexity. -/
theorem nativeAdmissibleChartWeight_isConvexPLOn
    (m : ℕ) (φ : X.an → ℝ)
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d)
    (hconv : EnvelopeProperty.IsConvexPLOn Set.univ (X.admChartFun m φ F d hF hd)) :
    RelativeSchemeValuedPoint.IsConvexPLOn Set.univ
      (X.nativeAdmissibleChartWeight m φ hF hFI hd) := by
  have hc := RelativeSchemeValuedPoint.IsConvexPLOn.of_paperAffine hconv
  have heq : X.nativeAdmissibleChartWeight m φ hF hFI hd =
      fun y => X.admChartFun m φ F d hF hd
        (RelativeSchemeValuedPoint.affineBerkHomeomorph y) := by
    funext y
    dsimp only [nativeAdmissibleChartWeight,admChartFun]
    rw [X.nativeAdmissibleAnalyticProjection_eq_chartInv hF hFI hd]
  rw [heq]
  simpa only [Set.preimage_univ] using hc

/-- ORIGINAL local convexity supplies actual native regular-unit presentations for
EVERY original admissible pair, retaining its exact prescribed rational class. -/
theorem IsLocallyConvexAll.nativeAdmissibleChartWeight_isConvexPLOn
    {a : ℚ} {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ)
    (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hda : (d : ℚ) = m*a)
    (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) :
    RelativeSchemeValuedPoint.IsConvexPLOn Set.univ
      (X.nativeAdmissibleChartWeight m φ hF hFI hd) :=
  X.nativeAdmissibleChartWeight_isConvexPLOn m φ hF hFI hd (hconv m d F hF hd hm hda hFI)

end EnvelopeProperty.ProjSubvariety
