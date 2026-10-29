import EnvelopeProperty.Char0.NativeBPRoundedMultiplierCriterion
import EnvelopeProperty.Char0.NativeAffineOpenMultiplierCovariance

/-! # The SAME original global BP germ on its actual original rounded affine chart -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeBPAffineRoundedCriterion

open CategoryTheory AlgebraicGeometry ComplexSchemes HolomorphicGerms Filter MeasureTheory
open ComplexGeometry ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open NativeBPMultiplierGermTransform NativeMultiplierGermTransform NativeSNCOriginalGenerators
open NativeAffineOpenJacobian NativeAffineOpenMultiplierCovariance NativeEtaleCoordinates
open NativeBPRoundedMultiplierCriterion WeightedHolomorphicGermIdealIntegralClosure
open HolomorphicGerms.NativeOpenJacobian
open scoped Topology Manifold ContDiff ENNReal

variable {R : Type} [CommRing R] [IsDomain R]
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (I : Ideal R) (hI : I ≠ ⊥)

local instance baseStructuralAffine : IsAffineHom f := isAffineHom_of_isAffine f

private instance bpSmooth : SmoothOfRelativeDimension n
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) :=
  affinePrincipalization_smoothOfRelativeDimension f n I hI

private instance bpProper : IsProper
    (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsLocallyNoetherian (Spec (.of R)) := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian (affinePrincipalizationTriple f n I hI).X.left := by
    change IsLocallyNoetherian (Spec (.of R))
    infer_instance
  exact (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).isProper_composite

private instance bpSeparated : IsSeparated
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) := by
  let π := (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite
  exact IsSeparated.stableUnderComposition.comp_mem π f inferInstance inferInstance

private instance bpQuasiCompact : QuasiCompact
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) := by
  let π := (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite
  let : IsAffineHom f := isAffineHom_of_isAffine f
  exact @quasiCompact_comp _ _ _ π f inferInstance inferInstance

private instance restrictedSmooth {Y : Scheme} (π : Y ⟶ Spec (.of R))
    [SmoothOfRelativeDimension n (π ≫ f)] (U : Y.affineOpens) :
    SmoothOfRelativeDimension n ((U.2.fromSpec ≫ π) ≫ f) := by
  rw [Category.assoc]
  exact (Nat.zero_add n) ▸
    (smoothOfRelativeDimension_comp (f := U.2.fromSpec) (n := 0) (m := n) (π ≫ f))

local instance restrictedAffine {Y : Scheme} (π : Y ⟶ Spec (.of R)) (U : Y.affineOpens) :
    IsAffineHom ((U.2.fromSpec ≫ π) ≫ f) := isAffineHom_of_isAffine _

private instance restrictedQC {Y : Scheme} (π : Y ⟶ Spec (.of R)) (U : Y.affineOpens) :
    QuasiCompact ((U.2.fromSpec ≫ π) ≫ f) := by
  let : IsAffineHom ((U.2.fromSpec ≫ π) ≫ f) := isAffineHom_of_isAffine _
  exact quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU => (hU.preimage _).isCompact

private instance restrictedSeparated {Y : Scheme} (π : Y ⟶ Spec (.of R)) (U : Y.affineOpens) :
    IsSeparated ((U.2.fromSpec ≫ π) ≫ f) := by
  let : IsAffineHom ((U.2.fromSpec ≫ π) ≫ f) := isAffineHom_of_isAffine _
  infer_instance

local instance nativeTopology {Y : Scheme} (g : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance nativeCharts {Y : Scheme} (g : Y ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension n g] : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticComplexChartedSpace g n
local instance nativeManifold {Y : Scheme} (g : Y ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticComplex_isComplexManifold g n

/-- The actual original affine-open halfweight and actual original raw generators have exactly the SAME density. -/
theorem affineOpen_integrability_normalization {s : ℕ} (a : Fin s → R) :
    let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
    let π := S.composite
    ∀ (U : S.last.affineOpens) (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ f))
      (c : ℝ) (T : ComplexModel n → ℂ),
    MultiplierIntegrableAt (centeredWeight
      (fun z => pulledWeight f n I hI a (affineOpenPointMap f π U.2.fromSpec z)) q)
        (2*c) T 0 volume ↔
      MultiplierIntegrableAt (generatorLog
        (fun i => centeredOriginalFunction f (U.2.fromSpec ≫ π) n q (a i))) c T 0 volume := by
  intro S π U q c T
  have hcomp : pointMap f n I hI ∘ affineOpenPointMap f π U.2.fromSpec =
      schemeComplexPointMap ((U.2.fromSpec ≫ π) ≫ f) f (U.2.fromSpec ≫ π) rfl := by
    funext z
    apply Subtype.ext
    exact Category.assoc z.val U.2.fromSpec π
  have hc : (0 : ℝ) < 2*c ↔ 0 < c := by constructor <;> intro h <;> linarith
  have hd : multiplierDensity (centeredWeight
      (fun z => pulledWeight f n I hI a (affineOpenPointMap f π U.2.fromSpec z)) q) (2*c) T =
      multiplierDensity (generatorLog
        (fun i => centeredOriginalFunction f (U.2.fromSpec ≫ π) n q (a i))) c T := by
    funext z
    change ENNReal.ofReal (‖T z‖ ^ 2) * multiplierWeight (2*c)
      (NativeAffineIdealWeight.weight f a (pointMap f n I hI
        (affineOpenPointMap f π U.2.fromSpec
          ((complexChartAt (n := n) q).val.symm
            (z + (complexChartAt (n := n) q).val q))))) = _
    rw [NativeAffineIdealWeight.multiplierWeight_normalization]
    have he := congrFun hcomp ((complexChartAt (n := n) q).val.symm
      (z + (complexChartAt (n := n) q).val q))
    change pointMap f n I hI (affineOpenPointMap f π U.2.fromSpec _) = _ at he
    rw [he]
    rfl
  simp only [MultiplierIntegrableAt, WeightedL2On, hd, hc]

/-- EVERY whole original global BP germ has the literal raw-generator test on the SAME actual affine open. -/
theorem weightedGermIdeal_affineOpen_iff_generatorLog {s : ℕ} (a : Fin s → R) :
    let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
    let π := S.composite
    ∀ (U : S.last.affineOpens) (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ f))
      {c : ℝ} (hc : 0 < c) (H : HolGerm (ComplexModel n)),
    H ∈ weightedGermIdeal (by positivity : 0 < 2*c)
      (centeredWeight_quasiPSH (pulledWeight_quasiPSH f n I hI a)
        (affineOpenPointMap f π U.2.fromSpec q)) volume ↔
      affineOpenGermPullback f π U.2.fromSpec n q H ∈
        weightedGermIdeal hc (centeredGeneratorLog_quasiPSH f (U.2.fromSpec ≫ π) n q a) volume := by
  intro S π U q c hc H
  have hcov := weightedGermIdeal_openPullback_iff
    (π ≫ f) ((U.2.fromSpec ≫ π) ≫ f) U.2.fromSpec (Category.assoc U.2.fromSpec π f) n
    (pulledWeight_quasiPSH f n I hI a) (by positivity : 0 < 2*c) q H
  have hnorm : affineOpenGermPullback f π U.2.fromSpec n q H ∈
      weightedGermIdeal (by positivity : 0 < 2*c)
        (centeredWeight_quasiPSH (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
          (schemeComplexPointMap_contMDiff_of_structure (π ≫ f) ((U.2.fromSpec ≫ π) ≫ f)
            U.2.fromSpec (Category.assoc U.2.fromSpec π f) n ∞)
          (pulledWeight_quasiPSH f n I hI a)) q) volume ↔
      affineOpenGermPullback f π U.2.fromSpec n q H ∈
        weightedGermIdeal hc (centeredGeneratorLog_quasiPSH f (U.2.fromSpec ≫ π) n q a) volume := by
    constructor
    · rintro ⟨T, hT, hrep, hint⟩
      exact ⟨T, hT, hrep,
        (affineOpen_integrability_normalization f n I hI a U q c T).mp hint⟩
    · rintro ⟨T, hT, hrep, hint⟩
      exact ⟨T, hT, hrep,
        (affineOpen_integrability_normalization f n I hI a U q c T).mpr hint⟩
  exact hcov.trans hnorm

variable [Algebra ℂ R]
  [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]

/-- ORIGINAL same-BP geometry gives a SAME actual affine chart which tests EVERY whole global-source
germ against the ENTIRE ORIGINAL rounded ideal. Both point and weight comparisons are internally derived. -/
theorem exists_original_rounded_analytic_chart {s : ℕ} (a : Fin s → R)
    (ha : Ideal.span (Set.range a) = I) :
    let f₀ := Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
    let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f₀ n I hI)
    let π := S.composite
    ∀ p : SchemeComplexPoint (π ≫ f₀),
    ∃ (U : S.last.affineOpens) (v : Fin n → Γ(S.last, U.1))
      (_hv : Etale (toAffineSpace (π ≫ f₀) U.1 v))
      (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ f₀))
      (_ht : letI := affinePointFieldAlgebra ((U.2.fromSpec ≫ π) ≫ f₀)
        (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale),
      q.val ≫ U.2.fromSpec = p.val ∧
      ∀ (r : ℚ) (hr : (0 : ℝ) < r) (H : HolGerm (ComplexModel n)),
      H ∈ weightedGermIdeal (by positivity : 0 < 2*(r : ℝ))
        (centeredWeight_quasiPSH (pulledWeight_quasiPSH f₀ n I hI a) p) volume ↔
      affineOpenGermPullback f₀ π U.2.fromSpec n q H ∈
        ((RoundedSncIdealSheaf.rounded ((specIdealSheaf I).comap π)
          (affinePrincipalization_isIdealOfSncDivisor f₀ n I hI) r).ideal U).map
          (coefficientGerm ((U.2.fromSpec ≫ π) ≫ f₀) n q) := by
  intro f₀ S π p
  obtain ⟨U, v, hv, q, ht, hfac, hrounded⟩ :=
    exists_original_rounded_multiplier_ideal_chart n I hI a ha p
  refine ⟨U, v, hv, q, ht, hfac, ?_⟩
  intro r hr H
  have hqp : affineOpenPointMap f₀ π U.2.fromSpec q = p := Subtype.ext hfac
  rw [← hqp]
  have hraw := weightedGermIdeal_affineOpen_iff_generatorLog f₀ n I hI a U q hr H
  rw [hrounded r hr] at hraw
  exact hraw

end EnvelopeProperty.Char0.NativeBPAffineRoundedCriterion
