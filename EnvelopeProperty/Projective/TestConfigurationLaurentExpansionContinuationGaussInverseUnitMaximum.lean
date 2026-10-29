import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussInverseUnitNorm

/-! # Actual original finite local coefficient/model-norm weighted maxima -/
open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial Classical
noncomputable section
universe u w
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich SchemeLineSectionEvaluation SchemeLineSectionUnitFrames Scheme.Modules CanonicalGeometry
open SchemeModuleFrameCoefficients

/-- The entire actual coefficient valuation function equals the original native whole-section norm. -/
theorem originalResidueFramedSectionCoefficients_local_value_fun
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
    {v : Valuation k ℝ≥0} (hb : ∀ a, v a ≤ 1) (x : RelativeSchemeValuedPoint v X.hom)
    (N : X.left.Modules) (hN : IsInvertible N) (U : X.left.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (δ : (pullback U.ι).obj N ≅ unitObj U.toScheme) :
    (fun s : Γ(N, ⊤) => x.1.residueVal (originalResidueFramedSectionCoefficients x N
      (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc δ) s)) =
      fun s : Γ(N, ⊤) => RelativeSchemeValuedPoint.modelLineNorm hb x hN
        (sectionAtOne (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
          (topSectionHom N s))) := by
  funext s
  exact originalResidueFramedSectionCoefficients_local_value hb x N hN U hc δ s

/-- EVERY actual original finite coefficient family retains its SAME-support weighted native norm maximum. -/
theorem originalResidueFramedSectionCoefficients_local_weighted_max
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
    {v : Valuation k ℝ≥0} (hb : ∀ a, v a ≤ 1) (x : RelativeSchemeValuedPoint v X.hom)
    (N : X.left.Modules) (hN : IsInvertible N) (U : X.left.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (δ : (pullback U.ι).obj N ≅ unitObj U.toScheme)
    {ι : Type w} (c : ι →₀ originalBaseSections X.hom N) (w : ι → ℝ≥0) :
    c.support.sup (fun n => x.1.residueVal (originalResidueFramedSectionCoefficients x N
      (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc δ) (c n)) * w n) =
      c.support.sup (fun n => RelativeSchemeValuedPoint.modelLineNorm hb x hN
        (sectionAtOne (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
          (topSectionHom N (c n)))) * w n) := by
  exact congrArg (fun F : Γ(N, ⊤) → ℝ≥0 => c.support.sup (fun n => F (c n) * w n))
    (originalResidueFramedSectionCoefficients_local_value_fun hb x N hN U hc δ)

/-- Genuine original local frames compute EVERY finite weighted maximum in ALL tensor powers. -/
theorem originalLocalPowerFramedSectionCoefficients_weighted_max
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
    {v : Valuation k ℝ≥0} (hb : ∀ a, v a ≤ 1) (x : RelativeSchemeValuedPoint v X.hom)
    (L : X.left.Modules) (hL : IsInvertible L) (m : ℕ) (U : X.left.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (δp : (pullback U.ι).obj (bundleTensorPower L m) ≅ unitObj U.toScheme)
    {ι : Type w} (c : ι →₀ originalBaseSections X.hom (bundleTensorPower L m)) (a : ι → ℝ≥0) :
    c.support.sup (fun n => x.1.residueVal
      (originalResidueFramedSectionCoefficients x (bundleTensorPower L m)
        (RelativeSchemeValuedPoint.localFrameGenericIso hb x U hc δp) (c n)) * a n) =
      c.support.sup (fun n => RelativeSchemeValuedPoint.modelLineNorm hb x
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m)
        (sectionAtOne (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
          (topSectionHom (bundleTensorPower L m) (c n)))) * a n) :=
  originalResidueFramedSectionCoefficients_local_weighted_max hb x (bundleTensorPower L m)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) U hc δp c a

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
