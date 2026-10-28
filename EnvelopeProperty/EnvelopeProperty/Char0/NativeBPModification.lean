import EnvelopeProperty.Char0.NativeProperModification
import EnvelopeProperty.Char0.BPIntegralTarget
import SGPT.Okounkov.SchemeNativeBirationalModification

/-! # The SAME original BP morphism is an actual native analytic modification -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeBPModification

open CategoryTheory AlgebraicGeometry BingWangEntropy SGPT.Okounkov
open TranscendentalNakamaye.FirstPass
open TranscendentalNakamaye.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold

variable {R : Type} [CommRing R] [IsDomain R]
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (I : Ideal R) (hI : I ≠ ⊥)

private instance originalBPSmooth : SmoothOfRelativeDimension n
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) :=
  affinePrincipalization_smoothOfRelativeDimension f n I hI

private instance originalBPProper :
    IsProper (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsLocallyNoetherian (Spec (.of R)) := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian (affinePrincipalizationTriple f n I hI).X.left := by
    change IsLocallyNoetherian (Spec (.of R))
    infer_instance
  exact (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).isProper_composite

private instance originalBPSeparated : IsSeparated
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) := by
  let π := (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite
  let : IsProper π := originalBPProper f n I hI
  have hπ : IsSeparated π := inferInstance
  have hf : IsSeparated f := inferInstance
  exact IsSeparated.stableUnderComposition.comp_mem π f hπ hf
private instance originalBPQuasiCompact : QuasiCompact
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) := by
  let π := (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite
  let : IsProper π := originalBPProper f n I hI
  let : IsAffineHom f := isAffineHom_of_isAffine f
  have hf : QuasiCompact f := inferInstance
  exact @quasiCompact_comp _ _ _ π f inferInstance hf
private instance originalBPIntegral :
    IsIntegral (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last :=
  affinePrincipalization_isIntegral_last f n I hI

local instance originalBaseTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance originalBPTopology : TopologicalSpace (SchemeComplexPoint
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f)) :=
  schemeAnalyticPointTopology _
local instance originalBaseCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance originalBPCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f)) :=
  schemeAnalyticTNChartedSpace _ n
local instance originalBaseManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
local instance originalBPManifold : IsComplexManifold n (SchemeComplexPoint
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f)) :=
  schemeAnalyticTN_isComplexManifold _ n

/-- The SAME original BP composite is an actual analytic modification in its actual native
manifolds. Properness, analytic exceptional sets, empty interior and the holomorphic inverse
are all derived internally from the original algebraic geometry. -/
theorem affinePrincipalization_isAnalyticModification :
    let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
    IsAnalyticModification (n := n) (schemeComplexPointMap (S.composite ≫ f) f S.composite rfl) := by
  let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
  let U := (specIdealSheaf I).support.compl
  let : IsIso (S.composite ∣_ U) := affinePrincipalization_isIso_restrict f n I hI
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsNoetherianRing R := isLocallyNoetherian_Spec.mp
    (LocallyOfFiniteType.isLocallyNoetherian f)
  exact schemeNative_isAnalyticModification_of_isIso_restrict f S.composite n U
    (nonempty_compl_support_specIdealSheaf I hI)
    (NativeProperModification.blowupSequence_isProper f S)

end EnvelopeProperty.Char0.NativeBPModification
