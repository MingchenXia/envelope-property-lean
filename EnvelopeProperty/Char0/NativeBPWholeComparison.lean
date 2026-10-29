import EnvelopeProperty.Char0.NativeBPAffineRoundedCriterion
import EnvelopeProperty.Char0.NativeAffineIdealTaylorReflection
import EnvelopeProperty.Char0.NativeFormalHolomorphicIdealCriterion
import EnvelopeProperty.Char0.NativeOriginalFiberGermCriterion
import EnvelopeProperty.Char0.RoundedCanonicalKernelBaseChange
import EnvelopeProperty.Char0.NativeAffineOpenJacobianMembership
import EnvelopeProperty.Char0.NativeAffineOpenFormalJacobianCriterion
import EnvelopeProperty.Char0.NativeOriginalRoundedFiberCriterion

/-! # The whole original BP quotient kernel and every native holomorphic germ -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeBPWholeComparison

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexSchemes HolomorphicGerms
open ComplexGeometry ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open NativeBPMultiplierGermTransform NativeMultiplierGermTransform NativeEtaleCoordinates
open NativeFormalHolomorphicIdealCriterion NativeAffineIdealTaylorReflection
open FlatSectionKernel RoundedCanonicalModule
open scoped Topology

local instance nativeTopology {Y : Scheme} (f : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance nativeCharts {Y : Scheme} (f : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance nativeManifold {Y : Scheme} (f : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticComplex_isComplexManifold f n

private theorem pointGerm_eq_zero_iff_globalJacobian
    {A : Type} [CommRing A] [Algebra ℂ A] {Y : Scheme}
    (π : Y ⟶ Spec (.of A)) (n : ℕ)
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))]
    [IsSeparated (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))]
    [QuasiCompact (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))]
    (U : Y.affineOpens) (v : Fin n → Γ(Y,U.1))
    (hv : Etale (toAffineSpace (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) U.1 v))
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (r : ℚ) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ A))
    letI : SmoothOfRelativeDimension n f :=
      smoothOfRelativeDimension_of_etale_coordinates z hz
    let Q := quotient (k := ℂ) f π n J hJ r
    let σ : Γ(Q, ⊤) :=
      (quotientDifferentialSection (k := ℂ) f π n J hJ r).val.app (.op ⊤) (1 : Γ(Y, ⊤))
    ∀ (x : SchemeComplexPoint f)
      (p : SchemeComplexPoint (π ≫ f))
      (hp : schemeComplexPointMap (π ≫ f) f π rfl p = x)
      (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ f))
      (_hq : q.val ≫ U.2.fromSpec = p.val)
      (g : NativeHolGerm n (SchemeComplexPoint f) x),
    let s := NativeHolGerm.taylor x g
    let QS := (Scheme.Modules.pullback (pullback.fst π
      (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x))))).obj Q
    QS.presheaf.germ ⊤
      (NativeFormalClosedFibrePoints.pointLift f n x π p hp (IsLocalRing.closedPoint ℂ)) trivial
      ((ProperBirationalSections.coefficientMap
        (pullback.snd π (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x)))) s) •
        Scheme.Modules.affinePullbackUnitTop (pullback.fst π
          (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x)))) Q σ) = 0 ↔
    NativeAffineOpenJacobian.affineOpenGermPullback f π U.2.fromSpec n q
      (NativeHolGerm.chartEquiv p
        (schemeMorphismNativeGermPullback f π n n p
          (fiberGerm (π := schemeComplexPointMap (π ≫ f) f π rfl) g p hp)) *
        NativePreferredJacobian.preferredJacobian f π n p) ∈
      ((RoundedSncIdealSheaf.rounded J hJ r).ideal U).map
        (NativeEtaleCoordinates.coefficientGerm ((U.2.fromSpec ≫ π) ≫ f) n q) := by
  intro f
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  intro Q σ x p hp q hq g
  have hpoint : NativeAffineOpenJacobian.affineOpenPointMap f π U.2.fromSpec q = p :=
    Subtype.ext hq
  have hbase : schemeComplexPointMap ((U.2.fromSpec ≫ π) ≫ f) f
      (U.2.fromSpec ≫ π) rfl q = x := by
    apply Subtype.ext
    change q.val ≫ (U.2.fromSpec ≫ π) = x.val
    rw [← Category.assoc, hq]
    exact congrArg Subtype.val hp
  subst p
  have hQ := NativeOriginalRoundedFiberCriterion.pointLiftGerm_taylor_eq_zero_iff_originalRoundedIdeal
    π n U v hv z hz J hJ r x _ hp q rfl g
  have hlocal := NativeAffineOpenFormalJacobianCriterion.formalPullback_taylor_mul_det_mem_iff
    π n U v hv z hz q ((RoundedSncIdealSheaf.rounded J hJ r).ideal U) x g hbase
  exact hQ.trans hlocal

private theorem native_mem_kernel_iff_originalFiber
    {A : Type} [CommRing A] [Algebra ℂ A] {Y : Scheme}
    (π : Y ⟶ Spec (.of A)) [IsProper π] (n : ℕ)
    [hSourceSmooth : SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))]
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (r : ℚ) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ A))
    letI : SmoothOfRelativeDimension n f :=
      smoothOfRelativeDimension_of_etale_coordinates z hz
    let Q := quotient (k := ℂ) f π n J hJ r
    let σ : Γ(Q, ⊤) :=
      (quotientDifferentialSection (k := ℂ) f π n J hJ r).val.app (.op ⊤) (1 : Γ(Y, ⊤))
    ∀ (x : SchemeComplexPoint f) (g : NativeHolGerm n (SchemeComplexPoint f) x),
    g ∈ (specPushedQuotientKernel (.of A) π z hz J hJ r).map
      (NativeAffineIdealWeight.nativeMap f n x) ↔
    ∀ (p : SchemeComplexPoint (π ≫ f))
      (hp : schemeComplexPointMap (π ≫ f) f π rfl p = x),
    let s := NativeHolGerm.taylor x g
    let QS := (Scheme.Modules.pullback (pullback.fst π
      (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x))))).obj Q
    QS.presheaf.germ ⊤
      (NativeFormalClosedFibrePoints.pointLift f n x π p hp (IsLocalRing.closedPoint ℂ)) trivial
      ((ProperBirationalSections.coefficientMap
        (pullback.snd π (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x)))) s) •
        Scheme.Modules.affinePullbackUnitTop (pullback.fst π
          (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x)))) Q σ) = 0 := by
  intro f
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  intro Q σ x g
  let : SmoothOfRelativeDimension n (π ≫ f) := hSourceSmooth
  let : Q.IsQuasicoherent := quotient_isQuasicoherent f π n J hJ r
  rw [mem_map_nativeMap_iff_taylor f n x]
  rw [specPushedQuotientKernel_eq_sectionKernel]
  exact NativeFormalClosedFibrePoints.mem_map_sectionKernel_iff_originalFiber
    f n x π Q σ (NativeHolGerm.taylor x g)

variable {R : Type} [CommRing R] [IsDomain R] [Algebra ℂ R]

private instance baseAffine :
    IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) := isAffineHom_of_isAffine _

private instance bpSmooth (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    (I : Ideal R) (hI : I ≠ ⊥) : SmoothOfRelativeDimension n
      ((Hironaka.Sequence.BP (affinePrincipalizationTriple
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).composite ≫
          Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
  affinePrincipalization_smoothOfRelativeDimension _ n I hI

private instance bpProper (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    (I : Ideal R) (hI : I ≠ ⊥) : IsProper
      (Hironaka.Sequence.BP (affinePrincipalizationTriple
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).composite := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsLocallyNoetherian (Spec (.of R)) := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian (affinePrincipalizationTriple f n I hI).X.left := by
    change IsLocallyNoetherian (Spec (.of R))
    infer_instance
  exact (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).isProper_composite

private instance bpSeparated (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    (I : Ideal R) (hI : I ≠ ⊥) : IsSeparated
      ((Hironaka.Sequence.BP (affinePrincipalizationTriple
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).composite ≫
          Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) := by
  exact IsSeparated.stableUnderComposition.comp_mem _ _ inferInstance inferInstance

private instance bpQuasiCompact (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    (I : Ideal R) (hI : I ≠ ⊥) : QuasiCompact
      ((Hironaka.Sequence.BP (affinePrincipalizationTriple
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).composite ≫
          Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) := by
  exact @quasiCompact_comp _ _ _ _ _ inferInstance inferInstance

/-- Every arbitrary native holomorphic germ has the original whole BP quotient-kernel
criterion; the source is the SAME original principalization and quotient throughout. -/
theorem nativeMultiplierIdeal_eq_originalBP_kernel (n : ℕ) (z : Fin n → R)
    (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (I : Ideal R) (hI : I ≠ ⊥) {s : ℕ} (a : Fin s → R)
    (ha : Ideal.span (Set.range a) = I) (r : ℚ) (hr : (0 : ℝ) < r) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
    let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
    let J := (specIdealSheaf I).comap S.composite
    let hJ := affinePrincipalization_isIdealOfSncDivisor f n I hI
    ∀ x : SchemeComplexPoint f,
      nativeMultiplierIdeal (NativeAffineIdealWeight.weight_quasiPSH f n a)
          (2*(r : ℝ)) (by positivity) x =
        (specPushedQuotientKernel (.of R) S.composite z hz J hJ r).map
          (NativeAffineIdealWeight.nativeMap f n x) := by
  let := smoothOfRelativeDimension_of_etale_coordinates z hz
  intro f S J hJ x
  let π := S.composite
  apply Ideal.ext
  intro g
  have hana := NativeBPMultiplierGermTransform.native_mem_iff f n I hI a ha hr x g
  have hformal := native_mem_kernel_iff_originalFiber π n z hz J hJ r x g
  refine hana.trans (?_ : _ ↔ _)
  refine (forall_congr' fun p => forall_congr' fun hp => ?_).trans hformal.symm
  obtain ⟨U, v, hv, q, ht, hqp, hchart⟩ :=
    NativeBPAffineRoundedCriterion.exists_original_rounded_analytic_chart n I hI a ha p
  have htest := pointGerm_eq_zero_iff_globalJacobian
    π n U v hv z hz J hJ r x p hp q hqp g
  have hglobal := hchart r hr (weightedPullback f n I hI p
    (fiberGerm (π := pointMap f n I hI) g p hp))
  rw [weightedPullback_eq_preferred] at hglobal
  exact hglobal.trans htest.symm

end EnvelopeProperty.Char0.NativeBPWholeComparison
