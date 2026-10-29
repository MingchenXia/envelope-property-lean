import EnvelopeProperty.AlgGeom.NativeAdmissibleChartConvexity
import EnvelopeProperty.Berkovich.SchemeOpenLocalPSH

/-! # Original admissible convexity on the original whole native scheme -/
open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Classical
open EnvelopeProperty.ProjBerk EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
attribute [local instance] nativeAdmissibleChartMap_isOpenImmersion MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)

/-- The true original native form-nonvanishing analytic locus. -/
def nativeAdmissibleAnalyticLocus (F : MvPolynomial (Fin (n+1)) k) :
    Set (RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) X.nativeStructure) :=
  {y | y.1.point ∈ X.nativeAdmissibleOpen F}

/-- The actual original native form-open is exactly original homogeneous
nonvanishing for EVERY original analytic point. -/
theorem nativeAnalyticHomeomorph_mem_nativeAdmissibleOpen
    (w : X.an) (F : MvPolynomial (Fin (n+1)) k) :
    (X.nativeAnalyticHomeomorph w).1.point ∈ X.nativeAdmissibleOpen F ↔ w.1.1.val F ≠ 0 := by
  change (RelativeSchemeValuedPoint.map X.nativeInclusion rfl
    (X.nativeAnalyticHomeomorph w)).1.point ∈ Proj.basicOpen (ProjectiveGrading k n) F ↔ _
  rw [X.nativeAnalyticHomeomorph_inclusion]
  rfl

/-- The original admissible weight on the actual original whole native scheme. -/
def nativeAdmissibleWeight (m : ℕ) (φ : X.an → ℝ)
    (F : MvPolynomial (Fin (n+1)) k)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) X.nativeStructure) : EReal :=
  let w := X.nativeAnalyticHomeomorph.symm y
  ((φ w - (m : ℝ)⁻¹ * Real.log ((w : ProjBerk k n).1.val F : ℝ) : ℝ) : EReal)

/-- The actual chart map identifies the whole original admissible native locus
with its genuine open-immersion image. -/
theorem nativeAdmissibleAnalyticLocus_eq_range
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d) :
    X.nativeAdmissibleAnalyticLocus F = Set.range
      (RelativeSchemeValuedPoint.map (v := (1 : _root_.Valuation k ℝ≥0))
        (X.nativeAdmissibleChartMap hF hFI hd) (X.nativeAdmissibleChartMap_over_base hF hFI hd)) := by
  rw [RelativeSchemeValuedPoint.range_map_of_isOpenImmersion,
    X.nativeAdmissibleChartMap_opensRange hF hFI hd]
  rfl

/-- True original admissible coefficient convexity descends to genuine actual
regular-unit convexity on the SAME original native form-nonvanishing locus. -/
theorem nativeAdmissibleWeight_isConvexPLOn
    (m : ℕ) (φ : X.an → ℝ)
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d)
    (hconv : EnvelopeProperty.IsConvexPLOn Set.univ (X.admChartFun m φ F d hF hd)) :
    RelativeSchemeValuedPoint.IsConvexPLOn (X.nativeAdmissibleAnalyticLocus F)
      (X.nativeAdmissibleWeight m φ F) := by
  apply RelativeSchemeValuedPoint.IsConvexPLOn.of_comp_openImmersion
    (X.nativeAdmissibleChartMap hF hFI hd) (X.nativeAdmissibleChartMap_over_base hF hFI hd)
  · rw [X.nativeAdmissibleAnalyticLocus_eq_range hF hFI hd]
  · have hc := X.nativeAdmissibleChartWeight_isConvexPLOn m φ hF hFI hd hconv
    have hpre : RelativeSchemeValuedPoint.map (v := (1 : _root_.Valuation k ℝ≥0))
        (X.nativeAdmissibleChartMap hF hFI hd) (X.nativeAdmissibleChartMap_over_base hF hFI hd) ⁻¹'
          X.nativeAdmissibleAnalyticLocus F = Set.univ := by
      rw [X.nativeAdmissibleAnalyticLocus_eq_range hF hFI hd]
      ext z
      exact iff_true_intro ⟨z,rfl⟩
    rw [hpre]
    exact hc

/-- ORIGINAL local O(a)-convexity yields genuine intrinsic convexity on EVERY
actual original admissible native open in the exact original class d=m*a. -/
theorem IsLocallyConvexAll.nativeAdmissibleWeight_isConvexPLOn
    {a : ℚ} {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ)
    (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hda : (d : ℚ) = m*a)
    (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) :
    RelativeSchemeValuedPoint.IsConvexPLOn (X.nativeAdmissibleAnalyticLocus F)
      (X.nativeAdmissibleWeight m φ F) :=
  X.nativeAdmissibleWeight_isConvexPLOn m φ hF hFI hd (hconv m d F hF hd hm hda hFI)

/-- Every actual scheme map over compatible coefficient valuations pulls back
the ORIGINAL prescribed-class convexity through its whole literal native map. -/
theorem IsLocallyConvexAll.nativeAdmissibleWeight_comp_mapOverBase
    {a : ℚ} {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ)
    (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hda : (d : ℚ) = m*a)
    (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal)
    {S : Type u} [CommRing S] (w : _root_.Valuation S ℝ≥0)
    (ψ : k →+* S) (hψ : ∀ c, w (ψ c) = (1 : _root_.Valuation k ℝ≥0) c)
    {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of S)}
    (g : Y ⟶ X.NativeScheme)
    (hg : g ≫ X.nativeStructure = fY ≫ Spec.map (CommRingCat.ofHom ψ)) :
    RelativeSchemeValuedPoint.IsConvexPLOn
      (RelativeSchemeValuedPoint.mapOverBase ψ hψ g hg ⁻¹' X.nativeAdmissibleAnalyticLocus F)
      (fun y => X.nativeAdmissibleWeight m φ F (RelativeSchemeValuedPoint.mapOverBase ψ hψ g hg y)) :=
  (hconv.nativeAdmissibleWeight_isConvexPLOn X m d hm hd hda F hF hFI).comp_mapOverBase ψ hψ g hg

end EnvelopeProperty.ProjSubvariety
