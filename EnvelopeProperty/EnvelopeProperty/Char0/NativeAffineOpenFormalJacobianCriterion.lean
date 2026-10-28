import EnvelopeProperty.Char0.NativeFormalHolomorphicIdealCriterion
import EnvelopeProperty.Char0.NativeAffineOpenJacobianMembership
import EnvelopeProperty.Char0.NativeAffineOpenGermComposition

/-! # Actual formal determinant membership as a whole original global Jacobian test -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeAffineOpenFormalJacobianCriterion

open CategoryTheory AlgebraicGeometry BingWangEntropy SGPT.Okounkov
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open NativeEtaleCoordinates NativeAffineOpenJacobian NativePreferredJacobian
open NativeAffineOpenJacobianMembership NativeAffineOpenGermComposition
open scoped Topology Manifold ContDiff

variable {R : Type} [CommRing R] [Algebra ℂ R] {Y : Scheme}
    (π : Y ⟶ Spec (.of R)) (n : ℕ) (U : Y.affineOpens)
    (v : Fin n → Γ(Y,U.1))
    (hv : Etale (toAffineSpace (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) U.1 v))
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    [IsSeparated (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    [QuasiCompact (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]

local instance baseAffine : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
  isAffineHom_of_isAffine _
local instance restrictedAffine : IsAffineHom
    ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
  isAffineHom_of_isAffine _
private instance restrictedSmooth : SmoothOfRelativeDimension n
    ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) := by
  rw [Category.assoc]
  exact (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp
    (f := U.2.fromSpec) (n := 0) (m := n)
      (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))

local instance baseTopology : TopologicalSpace (SchemeComplexPoint
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticPointTopology _
local instance globalTopology : TopologicalSpace (SchemeComplexPoint
    (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticPointTopology _
local instance restrictedTopology : TopologicalSpace (SchemeComplexPoint
    ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :=
  schemeAnalyticPointTopology _
local instance baseCharts
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))] :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticTNChartedSpace _ n
local instance globalCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint
    (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticTNChartedSpace _ n
local instance restrictedCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint
    ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :=
  schemeAnalyticTNChartedSpace _ n
local instance baseManifold
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))] :
    IsComplexManifold n (SchemeComplexPoint
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticTN_isComplexManifold _ n
local instance globalManifold : IsComplexManifold n (SchemeComplexPoint
    (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := schemeAnalyticTN_isComplexManifold _ n
local instance restrictedManifold : IsComplexManifold n (SchemeComplexPoint
    ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :=
  schemeAnalyticTN_isComplexManifold _ n

/-- ANY original ideal and ANY whole native base germ have the SAME literal formal
determinant test and actual global Jacobian test on an original affine open. -/
theorem formalPullback_taylor_mul_det_mem_iff
    (q : SchemeComplexPoint
      ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
    (K : Ideal Γ(Y,U.1)) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    ∀ (x : SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
      (g : NativeHolGerm n (SchemeComplexPoint
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) x)
      (hq : schemeComplexPointMap
        ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) (U.2.fromSpec ≫ π) rfl q = x),
    schemeMorphismFormalPullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
      (U.2.fromSpec ≫ π) n n q (NativeHolGerm.taylor x g) *
        schemeAffineNativeFormal
          ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q
          (affineOpenDet π n U v hv z hz) ∈
      K.map (schemeAffineNativeFormal
        ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q) ↔
    affineOpenGermPullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec n q
      (NativeHolGerm.chartEquiv
        (affineOpenPointMap (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec q)
        (schemeMorphismNativeGermPullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π n n
          (affineOpenPointMap (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec q)
          (((basePoint_comp (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec q).trans hq).symm ▸ g)) *
        preferredJacobian (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π n
          (affineOpenPointMap (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec q)) ∈
      K.map (coefficientGerm
        ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q) := by
  let := smoothOfRelativeDimension_of_etale_coordinates z hz
  intro x g hq
  cases hq
  have hF := NativeFormalHolomorphicIdealCriterion.formalPullback_taylor_mul_mem_iff
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) (U.2.fromSpec ≫ π) n n q K
    (affineOpenDet π n U v hv z hz) g
  have hC := centeredNativePullback_comp
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec n n q g
  rw [← hC] at hF
  exact hF.trans (openPullback_mul_det_mem_iff π n U v hv z hz q
    (K.map (coefficientGerm
      ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q)) _)

end EnvelopeProperty.Char0.NativeAffineOpenFormalJacobianCriterion
