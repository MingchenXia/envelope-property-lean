import EnvelopeProperty.Char0.NativeOriginalFiberGermCriterion
import EnvelopeProperty.Char0.NativeAffineOpenGlobalRoundedKernel

/-! # The SAME original rounded quotient at its actual original formal fibre lift -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeOriginalRoundedFiberCriterion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ComplexSchemes HolomorphicGerms
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open RoundedCanonicalModule NativeAffineOpenJacobianMembership

variable {R : Type} [CommRing R] [Algebra ℂ R] {Y : Scheme}
    (π : Y ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    [IsSeparated (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    [QuasiCompact (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    (U : Y.affineOpens) (v : Fin n → Γ(Y,U.1))
    (hv : Etale (toAffineSpace (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) U.1 v))
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)

private instance restrictedSmooth : SmoothOfRelativeDimension n
    ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) := by
  rw [Category.assoc]
  exact (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp
    (f := U.2.fromSpec) (n := 0) (m := n)
      (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))

local instance baseAffine : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
  isAffineHom_of_isAffine _
local instance restrictedAffine : IsAffineHom
    ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
  isAffineHom_of_isAffine _
local instance baseTopology : TopologicalSpace
    (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :=
  schemeAnalyticPointTopology _
local instance baseCharts
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))] :
    ChartedSpace (ComplexModel n)
    (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :=
  schemeAnalyticComplexChartedSpace _ n
local instance baseManifold
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))] :
    IsComplexManifold n
    (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :=
  schemeAnalyticComplex_isComplexManifold _ n

omit [IsSeparated (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
  [QuasiCompact (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))] in
private theorem sectionPointLiftGerm_taylor_eq_zero_iff
    (N : Y.Modules) [((Scheme.Modules.pullback U.2.fromSpec).obj N).IsQuasicoherent]
    (σ : Γ(N, ⊤)) (I : Ideal Γ(Y,U.1)) (j : Γ(Y,U.1))
    (hK : FlatSectionKernel.sectionKernel (R := Γ(Y,U.1)) (𝟙 (Spec Γ(Y,U.1)))
      ((Scheme.Modules.pullback U.2.fromSpec).obj N)
        (Scheme.Modules.affinePullbackUnitTop U.2.fromSpec N σ) = I.colon {j}) :
    letI : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
      smoothOfRelativeDimension_of_etale_coordinates z hz
    ∀ (x : SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
      (p : SchemeComplexPoint (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
      (hp : schemeComplexPointMap (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π rfl p = x)
      (q : SchemeComplexPoint
        ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
      (_hq : q.val ≫ U.2.fromSpec = p.val)
      (g : NativeHolGerm n
        (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) x),
    let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
    let s := NativeHolGerm.taylor x g
    let NS := (Scheme.Modules.pullback (pullback.fst π
      (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x))))).obj N
    NS.presheaf.germ ⊤
      (NativeFormalClosedFibrePoints.pointLift f n x π p hp (IsLocalRing.closedPoint ℂ)) trivial
      ((ProperBirationalSections.coefficientMap
        (pullback.snd π (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x)))) s) •
        Scheme.Modules.affinePullbackUnitTop (pullback.fst π
          (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x)))) N σ) = 0 ↔
      schemeMorphismFormalPullback f (U.2.fromSpec ≫ π) n n q s *
        schemeAffineNativeFormal ((U.2.fromSpec ≫ π) ≫ f) n q j ∈
          I.map (schemeAffineNativeFormal ((U.2.fromSpec ≫ π) ≫ f) n q) := by
  let : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
    smoothOfRelativeDimension_of_etale_coordinates z hz
  intro x p hp q hq g
  exact NativeOriginalFiberGermCriterion.pointLiftGerm_eq_zero_iff_nativeIdeal
    (R := R) (B := Γ(Y,U.1)) (Y := Y)
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π U.2.fromSpec n n
    N σ I j hK x p hp q hq (NativeHolGerm.taylor x g)

omit [IsSeparated (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
  [QuasiCompact (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))] in
/-- The SAME actual original rounded quotient differential section at its canonical
original formal fibre lift is tested by the WHOLE original rounded affine ideal.
The actual chart kernel is derived internally, and the only point data are natural. -/
theorem pointLiftGerm_taylor_eq_zero_iff_originalRoundedIdeal
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (r : ℚ) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
    letI : SmoothOfRelativeDimension n f :=
      smoothOfRelativeDimension_of_etale_coordinates z hz
    let Q := quotient (k := ℂ) f π n J hJ r
    let σ : Γ(Q, ⊤) :=
      (quotientDifferentialSection (k := ℂ) f π n J hJ r).val.app (.op ⊤) (1 : Γ(Y, ⊤))
    ∀
    (x : SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
    (p : SchemeComplexPoint (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
    (hp : schemeComplexPointMap (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π rfl p = x)
    (q : SchemeComplexPoint
      ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
    (_hq : q.val ≫ U.2.fromSpec = p.val)
    (g : NativeHolGerm n
      (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) x),
    let s := NativeHolGerm.taylor x g
    let QS := (Scheme.Modules.pullback (pullback.fst π
      (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x))))).obj Q
    QS.presheaf.germ ⊤
      (NativeFormalClosedFibrePoints.pointLift f n x π p hp (IsLocalRing.closedPoint ℂ)) trivial
      ((ProperBirationalSections.coefficientMap
        (pullback.snd π (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x)))) s) •
        Scheme.Modules.affinePullbackUnitTop (pullback.fst π
          (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x)))) Q σ) = 0 ↔
      schemeMorphismFormalPullback f (U.2.fromSpec ≫ π) n n q s *
        schemeAffineNativeFormal ((U.2.fromSpec ≫ π) ≫ f) n q
          (affineOpenDet π n U v hv z hz) ∈
        ((RoundedSncIdealSheaf.rounded J hJ r).ideal U).map
          (schemeAffineNativeFormal ((U.2.fromSpec ≫ π) ≫ f) n q) := by
  intro f
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  intro Q σ
  let : Q.IsQuasicoherent := quotient_isQuasicoherent (k := ℂ) f π n J hJ r
  let : ((Scheme.Modules.pullback U.2.fromSpec).obj Q).IsQuasicoherent := inferInstance
  let I := (RoundedSncIdealSheaf.rounded J hJ r).ideal U
  let j := affineOpenDet π n U v hv z hz
  have hK :=
    NativeAffineOpenGlobalRoundedKernel.affineOpenGlobalQuotient_sectionKernel_eq_det_colon
      (R := R) (Y := Y) π n U v hv z hz J hJ r
  exact sectionPointLiftGerm_taylor_eq_zero_iff
    (R := R) (Y := Y) π n U z hz Q σ I j hK

end EnvelopeProperty.Char0.NativeOriginalRoundedFiberCriterion
