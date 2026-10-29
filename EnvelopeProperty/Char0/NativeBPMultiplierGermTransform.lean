import EnvelopeProperty.Char0.NativeMultiplierGermTransform
import EnvelopeProperty.Char0.NativeBPModification
import EnvelopeProperty.Char0.NativeAffineIdealWeight
import EnvelopeProperty.Char0.NativePreferredJacobian

/-! # Actual whole native multiplier germs on the SAME original BP principalization -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EnvelopeProperty.Char0.NativeBPMultiplierGermTransform
open CategoryTheory AlgebraicGeometry ComplexSchemes HolomorphicGerms Set Filter MeasureTheory
open ComplexGeometry ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HolomorphicIdealSheaves AnalyticModificationLocalDiscrepancy WeightedHolomorphicGermIdealIntegralClosure
open NativeMultiplierGermTransform
open scoped Topology Manifold ContDiff ENNReal

variable {R : Type} [CommRing R] [IsDomain R]
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (I : Ideal R) (hI : I ≠ ⊥)

private instance transformBPSmooth : SmoothOfRelativeDimension n
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) :=
  affinePrincipalization_smoothOfRelativeDimension f n I hI

private instance transformBPProper :
    IsProper (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsLocallyNoetherian (Spec (.of R)) := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian (affinePrincipalizationTriple f n I hI).X.left := by
    change IsLocallyNoetherian (Spec (.of R))
    infer_instance
  exact (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).isProper_composite

private instance transformBPSeparated : IsSeparated
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) := by
  let π := (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite
  let : IsProper π := transformBPProper f n I hI
  have hπ : IsSeparated π := inferInstance
  have hf : IsSeparated f := inferInstance
  exact IsSeparated.stableUnderComposition.comp_mem π f hπ hf
private instance transformBPQuasiCompact : QuasiCompact
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) := by
  let π := (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite
  let : IsProper π := transformBPProper f n I hI
  let : IsAffineHom f := isAffineHom_of_isAffine f
  have hf : QuasiCompact f := inferInstance
  exact @quasiCompact_comp _ _ _ π f inferInstance hf
private instance transformBPIntegral :
    IsIntegral (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last :=
  affinePrincipalization_isIntegral_last f n I hI

local instance transformBaseTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance transformBPTopology : TopologicalSpace (SchemeComplexPoint
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f)) :=
  schemeAnalyticPointTopology _
local instance transformBaseCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance transformBPCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f)) :=
  schemeAnalyticComplexChartedSpace _ n
local instance transformBaseManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n
local instance transformBPManifold : IsComplexManifold n (SchemeComplexPoint
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f)) :=
  schemeAnalyticComplex_isComplexManifold _ n

/-- The literal native point map of the SAME original BP composite. -/
def pointMap : SchemeComplexPoint
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) →
      SchemeComplexPoint f :=
  schemeComplexPointMap _ f (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite rfl

/-- Genuine modification geometry is supplied by the same original BP producer. -/
theorem pointMap_isAnalyticModification : IsAnalyticModification (n := n) (pointMap f n I hI) :=
  NativeBPModification.affinePrincipalization_isAnalyticModification f n I hI

/-- The actual original finite-tuple halfweight pulled by the same BP map. -/
def pulledWeight {m : ℕ} (a : Fin m → R) :=
  fun y => NativeAffineIdealWeight.weight f a (pointMap f n I hI y)

/-- Genuine source quasi-PSH regularity is internally pulled from the actual original tuple. -/
theorem pulledWeight_quasiPSH {m : ℕ} (a : Fin m → R) :
    ManifoldQuasiPlurisubharmonic (n := n) (pulledWeight f n I hI a) :=
  GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
    (pointMap_isAnalyticModification f n I hI).1 (NativeAffineIdealWeight.weight_quasiPSH f n a)

/-- Whole arbitrary analytic germs are pulled by the same BP map and its actual centered Jacobian. -/
def weightedPullback (y : SchemeComplexPoint
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f))
    (g : NativeHolGerm n (SchemeComplexPoint f) (pointMap f n I hI y)) : HolGerm (ComplexModel n) :=
  jacobianWeightedPullback (pointMap f n I hI) (pointMap_isAnalyticModification f n I hI).1 y g

/-- The ENTIRE transformed germ uses the existing original scheme-morphism pullback and default Jacobian. -/
theorem weightedPullback_eq_preferred (y : SchemeComplexPoint
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f))
    (g : NativeHolGerm n (SchemeComplexPoint f) (pointMap f n I hI y)) :
    weightedPullback f n I hI y g =
      NativeHolGerm.chartEquiv y
        (schemeMorphismNativeGermPullback f
          (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n n y g) *
      NativePreferredJacobian.preferredJacobian f
        (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n y := rfl

/-- Arbitrary bottom holomorphic functions satisfy the literal SAME BP all-fibre integral criterion. -/
theorem function_mem_iff {m : ℕ} (a : Fin m → R) (ha : Ideal.span (Set.range a) = I)
    {c : ℝ} (hc : 0 < c) (x : SchemeComplexPoint f) (F : SchemeComplexPoint f → ℂ)
    (hF : HolomorphicAt n F x) :
    (multiplierIdeal (n := n) (2*c) (NativeAffineIdealWeight.weight f a)).mem x F ↔
      ∀ y : SchemeComplexPoint
        ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f),
        pointMap f n I hI y = x →
        MultiplierIntegrableAt (centeredWeight (n := n) (pulledWeight f n I hI a) y) (2*c)
          (centeredPullbackTest (n := n) (pointMap f n I hI) F y) 0 volume := by
  have hgen : Ideal.span (Set.range a) ≠ ⊥ := fun hz => hI (ha.symm.trans hz)
  exact multiplierIdeal_mem_iff_fiber_centered (pointMap_isAnalyticModification f n I hI)
    (NativeAffineIdealWeight.weight_isGlobalQuasiPshPotential f n a hgen) (by positivity) x F hF

/-- Every WHOLE arbitrary bottom native germ is characterized on the SAME original BP fibre, in ALL dimensions. -/
theorem native_mem_iff {m : ℕ} (a : Fin m → R) (ha : Ideal.span (Set.range a) = I)
    {c : ℝ} (hc : 0 < c) (x : SchemeComplexPoint f) (g : NativeHolGerm n (SchemeComplexPoint f) x) :
    g ∈ nativeMultiplierIdeal (NativeAffineIdealWeight.weight_quasiPSH f n a) (2*c) (by positivity) x ↔
      ∀ (y : SchemeComplexPoint
        ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f))
        (hy : pointMap f n I hI y = x),
        weightedPullback f n I hI y (fiberGerm (n := n) g y hy) ∈
          weightedGermIdeal (by positivity : 0 < 2*c)
            (centeredWeight_quasiPSH (pulledWeight_quasiPSH f n I hI a) y) volume := by
  have hgen : Ideal.span (Set.range a) ≠ ⊥ := fun hz => hI (ha.symm.trans hz)
  exact nativeMultiplierIdeal_mem_iff_fiber (pointMap_isAnalyticModification f n I hI)
    (NativeAffineIdealWeight.weight_isGlobalQuasiPshPotential f n a hgen) (by positivity) x g

/-- Actual original affine generators in the same centered BP source chart. -/
def sourceGenerators {m : ℕ} (a : Fin m → R)
    (y : SchemeComplexPoint ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f)) :
    Fin m → ComplexModel n → ℂ :=
  fun i z => NativeAffineIdealWeight.generators f a i
    (pointMap f n I hI ((complexChartAt (n := n) y).val.symm
      (z + (complexChartAt (n := n) y).val y)))

/-- The half-log normalization is exact for the actual pulled source integrals, including all poles. -/
theorem source_integrability_normalization {m : ℕ} (a : Fin m → R)
    (y : SchemeComplexPoint ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f))
    (c : ℝ) (T : ComplexModel n → ℂ) :
    MultiplierIntegrableAt (centeredWeight (n := n) (pulledWeight f n I hI a) y) (2*c) T 0 volume ↔
      MultiplierIntegrableAt (generatorLog (sourceGenerators f n I hI a y)) c T 0 volume := by
  have hc : (0 : ℝ) < 2*c ↔ 0 < c := by constructor <;> intro h <;> linarith
  have hd : multiplierDensity (centeredWeight (n := n) (pulledWeight f n I hI a) y) (2*c) T =
      multiplierDensity (generatorLog (sourceGenerators f n I hI a y)) c T := by
    funext z
    change ENNReal.ofReal (‖T z‖ ^ 2) * multiplierWeight (2*c)
      (NativeAffineIdealWeight.weight f a
        (pointMap f n I hI ((complexChartAt (n := n) y).val.symm
          (z + (complexChartAt (n := n) y).val y)))) = _
    rw [NativeAffineIdealWeight.multiplierWeight_normalization]
    rfl
  simp only [MultiplierIntegrableAt,WeightedL2On,hd,hc]

/-- The actual standard-level generator-log criterion is ready for the arbitrary-test SNC theorem. -/
theorem function_mem_generatorLog_iff {m : ℕ} (a : Fin m → R)
    (ha : Ideal.span (Set.range a) = I) {c : ℝ} (hc : 0 < c)
    (x : SchemeComplexPoint f) (F : SchemeComplexPoint f → ℂ) (hF : HolomorphicAt n F x) :
    (multiplierIdeal (n := n) c (generatorLog (NativeAffineIdealWeight.generators f a))).mem x F ↔
      ∀ y : SchemeComplexPoint
        ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f),
        pointMap f n I hI y = x →
        MultiplierIntegrableAt (generatorLog (sourceGenerators f n I hI a y)) c
          (centeredPullbackTest (n := n) (pointMap f n I hI) F y) 0 volume := by
  rw [← NativeAffineIdealWeight.multiplierIdeal_normalization f n a c]
  refine (function_mem_iff f n I hI a ha hc x F hF).trans
    (forall_congr' fun y => forall_congr' fun _ => ?_)
  exact source_integrability_normalization f n I hI a y c _

end EnvelopeProperty.Char0.NativeBPMultiplierGermTransform
