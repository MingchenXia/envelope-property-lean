import EnvelopeProperty.Global.NativeTestConfigurationPowerCoherence
import EnvelopeProperty.Berkovich.SchemeSupportPowerFrames

/-! # Literal original TC/reference native frame transitions are powers of ONE actual unit -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory CartesianMonoidalCategory
open Scheme.Modules
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open CanonicalGeometry BundleTensorPowerPullback SchemePulledPowerFrames SchemeTensorPowerFrames
open Berkovich Berkovich.SchemeFramedSectionPullback Berkovich.SchemeInducedPowerFrames
open Berkovich.SchemeSupportPowerFrames Berkovich.SchemeResidueFrameComparison
open SchemeSupportLineFrames SchemeLineSectionEvaluation
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}

/-- The SAME actual original support-open line frame defines the original product reference residue frame. -/
def productReferenceResidueFrame (L : X.left.Modules)
    (y : SchemeValuedPoint (X ⊗ ProjBerk.nativeMultiplicativeGroup k).left)
    (U : X.left.Opens) (hy : y.point ∈ (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U)
    (eU : (pullback U.ι).obj L ≅ unitObj U.toScheme) :=
  supportGenericFrame y.point ((fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U) hy
    (localPullbackFrame (fst X (ProjBerk.nativeMultiplicativeGroup k)).left U eU)

variable (C : TestConfiguration k X) (M : C.total.Modules) (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
    (y : SchemeValuedPoint (X ⊗ ProjBerk.nativeMultiplicativeGroup k).left)
    (eM : (pullback (C.total.fromSpecResidueField (C.productTotalMap y.point))).obj M ≅
      unitObj (Spec (.of (C.total.residueField (C.productTotalMap y.point)))))

/-- ONE actual target residue frame and original action/fibre data define the native source model frame. -/
def productModelResidueFrame := inducedResidueFrame C.productTotalMap (C.productTotalLineIso M L α e₁) y eM

/-- All native source model power frames are constructed from the SAME original target frame. -/
def productModelPowerResidueFrame (n : ℕ) :=
  inducedResidueFrame C.productTotalMap (C.productTotalLinePowerIso M L α e₁ n) y
    (pullbackPowerFrame (C.total.fromSpecResidueField (C.productTotalMap y.point)) eM n)

/-- The LITERAL original beta_n transports actual powers of the SAME target residue frame. -/
theorem productTotalLinePowerIso_inducedResidueFrame (n : ℕ) :
    C.productModelPowerResidueFrame M L α e₁ y eM n =
      (pullback ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField y.point)).mapIso
        (pullbackIso (fst X (ProjBerk.nativeMultiplicativeGroup k)).left L n) ≪≫
          pullbackPowerFrame ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField y.point)
            (C.productModelResidueFrame M L α e₁ y eM) n := by
  have hc := congrArg (fun E => inducedResidueFrame C.productTotalMap E y
    (pullbackPowerFrame (C.total.fromSpecResidueField (C.productTotalMap y.point)) eM n))
    (C.productTotalLinePowerIso_coherence M L α e₁ n)
  exact hc.trans (inducedResidueFrame_normalizedPower C.productTotalMap
    (fst X (ProjBerk.nativeMultiplicativeGroup k)).left (C.productTotalLineIso M L α e₁) y eM n)

variable (U : X.left.Opens) (hy : y.point ∈ (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U)
    (eU : (pullback U.ι).obj L ≅ unitObj U.toScheme)

/-- ONE actual original support frame gives the true native unit before ALL degrees/sections/families. -/
def productFrameTransitionUnit :=
  transitionUnit (productReferenceResidueFrame L y U hy eU) (C.productModelResidueFrame M L α e₁ y eM)

omit C M α e₁ eM in
/-- The SAME original U,eU construct compatible reference power frames with the actual native comparison. -/
theorem productReferenceResidueFrame_power (n : ℕ) :
    productReferenceResidueFrame (bundleTensorPower L n) y U hy (pullbackPowerFrame U.ι eU n) =
      (pullback ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField y.point)).mapIso
        (pullbackIso (fst X (ProjBerk.nativeMultiplicativeGroup k)).left L n) ≪≫
          pullbackPowerFrame ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField y.point)
            (productReferenceResidueFrame L y U hy eU) n :=
  supportGenericFrame_localPullbackPower (fst X (ProjBerk.nativeMultiplicativeGroup k)).left y.point U hy eU n

/-- Actual native original power-frame transitions are the SAME original native unit to that power. -/
theorem productPowerFrame_transitionUnit (n : ℕ) :
    transitionUnit
      (productReferenceResidueFrame (bundleTensorPower L n) y U hy (pullbackPowerFrame U.ι eU n))
      (C.productModelPowerResidueFrame M L α e₁ y eM n) =
        C.productFrameTransitionUnit M L α e₁ y eM U hy eU ^ n := by
  have hh := congrArg₂ (fun E F => transitionUnit E F)
    (productReferenceResidueFrame_power L y U hy eU n)
    (C.productTotalLinePowerIso_inducedResidueFrame M L α e₁ y eM n)
  have hc := transitionUnit_precompIso
    ((pullback ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField y.point)).mapIso
      (pullbackIso (fst X (ProjBerk.nativeMultiplicativeGroup k)).left L n))
    (pullbackPowerFrame ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField y.point)
      (productReferenceResidueFrame L y U hy eU) n)
    (pullbackPowerFrame ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField y.point)
      (C.productModelResidueFrame M L α e₁ y eM) n)
  have hp := transitionUnit_precompIso
    (pullbackIso ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField y.point)
      ((pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj L) n)
    (powerFrame (productReferenceResidueFrame L y U hy eU) n)
    (powerFrame (C.productModelResidueFrame M L α e₁ y eM) n)
  exact hh.trans (hc.trans (hp.trans (transitionUnit_powerFrame _ _ n)))

/-- Every actual native residue valuation gives a positive factor fixed before ALL powers. -/
theorem productFrameTransitionUnit_value_pos
    (ν : Valuation ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.residueField y.point) ℝ≥0) :
    0 < ν (C.productFrameTransitionUnit M L α e₁ y eM U hy eU).val :=
  transitionUnit_value_pos _ _ ν

/-- Every degree's actual native transition value equals ONE positive original native factor to that power. -/
theorem productPowerFrame_transitionUnit_value
    (ν : Valuation ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.residueField y.point) ℝ≥0) (n : ℕ) :
    ν (transitionUnit
      (productReferenceResidueFrame (bundleTensorPower L n) y U hy (pullbackPowerFrame U.ι eU n))
      (C.productModelPowerResidueFrame M L α e₁ y eM n)).val =
        ν (C.productFrameTransitionUnit M L α e₁ y eM U hy eU).val ^ n := by
  have h := congrArg (fun u => ν (Units.val u)) (C.productPowerFrame_transitionUnit M L α e₁ y eM U hy eU n)
  exact h.trans (ν.map_pow _ n)

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
