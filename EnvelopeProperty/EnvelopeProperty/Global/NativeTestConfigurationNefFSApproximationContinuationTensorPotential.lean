import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationPowerPotential
import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationTensorResidueFrames
import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationTensorLines
import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationRayOperations
import EnvelopeProperty.AlgGeom.SchemeCommonAffineLineFrames
import EnvelopeProperty.AlgGeom.AmpleTensorLines

/-! # Additivity of native model potentials and exact FS functions from central nefness

Let `C` be a test configuration of an integral `X`, and `(M, α, e)`, `(H, β, f)` linearized
lines on its total space with generic lines `L`, `K` on `X`.

* `gaussNativeNormFactor_tensor_comparisons`, `gaussNativeModelPotential_tensor_comparisons`:
  for ample `L`, `K`, the native factor of `M ⊗ H` is the product of the factors, so
  `pot(M ⊗ H) = pot(M) + pot(H)`;
* `gaussNativeModelPotential_powerTensor_comparisons`: for ample `L^{⊗ b}`, `K^{⊗ a}`,
  `pot(M^{⊗ b} ⊗ H^{⊗ a}) = b · pot(M) + a · pot(H)`;
* `isFinFS_power_tensor_potential_sum_of_central_nef`: if moreover `M|_{𝒳₀}` is nef,
  `H|_{𝒳₀}` is ample and `a > 0`, then `b · pot(M) + a · pot(H)` is an exact finite rational
  FS function of class `1` for `L^{⊗ b} ⊗ K^{⊗ a}`;
* `isFinFS_potential_add_div_of_central_nef`: dividing by `b > 0`,
  `pot(M) + (a / b) · pot(H)` is an exact finite rational FS function of class `1 / b`.

Mathematically: `φ_{b𝓛 + a𝓗} = b φ_𝓛 + a φ_𝓗` for PL functions of test configurations, and
`b𝓛 + a𝓗` is relatively ample once `𝓛|_{𝒳₀}` is nef and `𝓗|_{𝒳₀}` is ample, so its PL
function is a Fubini--Study function (FHX, proof of `lem:local-PL-positivity`; BJ22,
Definition 3.2 and Lemma 4.3, where a nef `𝓛|_{𝒳₀}` gives `φ_𝓛 ∈ PSH`).
-/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped NNReal Classical
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint Scheme.Modules CanonicalGeometry
open SchemeTensorPowerFrames SchemePulledPowerFrames
open Berkovich.SchemeFramedSectionPullback Berkovich.SchemeInducedPowerFrames
open Berkovich.SchemeResidueFrameComparison
open NativeTestConfigurationNefFSTensorResidueFrames ProjectiveCentralFiberSectionLifting
noncomputable local instance nfTensorPotentialModulesMonoidal (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y
noncomputable local instance nfTensorPotentialPullbackMonoidal {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (pullback f).Monoidal := pullbackMonoidal f
variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [IsIntegral X.left]
    (C : TestConfiguration k X) (M H : C.total.Modules) (hM : IsInvertible M) (hH : IsInvertible H)
    (L K : X.left.Modules)
    (alpha : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (beta : (pullback C.lineActionMap).obj H ≅ (pullback C.lineProjectionMap).obj H)
    (e : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
    (f : (pullback C.fibreOneInclusion.left).obj H ≅ (pullback C.fibreOneIso.hom.left).obj K)
    (hL : IsInvertible L) (hK : IsInvertible K)
private local instance projectionProper : IsProper C.projection := C.projection_isProper

/-- Actual tensor action and fibre-one data force multiplication of the
defined original native factors.  Ordinary ampleness of the original
generic lines supplies frame independence; no desired factor is input. -/
theorem gaussNativeNormFactor_tensor_comparisons
    (hAmpL : SchemeLineAmpleness.IsAmple X.hom L)
    (hAmpK : SchemeLineAmpleness.IsAmple X.hom K)
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    C.gaussNativeNormFactor (M ⊗ H) (hM.monoidalTensor hH) (L ⊗ K)
        (C.tensorLineActionComparison M H alpha beta) (C.tensorFibreOneComparison M H L K e f)
        (hL.monoidalTensor hK) r hr hru x =
      C.gaussNativeNormFactor M hM L alpha e hL r hr hru x *
        C.gaussNativeNormFactor H hH K beta f hK r hr hru x := by
  let : IsProper X.hom := C.original_isProper
  let P := (C.productGaussSource x r hr).1
  let z := RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)
  let hb := Spectrum.trivialGaussValuation_le_one k r hru
  let ref := (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
  let t := (X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField P.point
  obtain ⟨U, hcU, _, ⟨eL⟩, ⟨eK⟩⟩ := SchemeCommonAffineLineFrames.exists_in_open L K hL hK
    (center Valuation.one_apply_le_one x) ⊤ (by trivial)
  have hy : P.point ∈ ref ⁻¹ᵁ U.1 := by
    have hh := congrArg SchemeValuedPoint.point
      (SchemePointLaurentLocalFrame.openPoint_comp X.hom x Valuation.one_apply_le_one U.1 hcU r hr)
    change (SchemePointLaurentGauss.productPoint X.hom x r hr).1.point ∈ ref ⁻¹ᵁ U.1
    rw [← hh]
    exact (SchemePointLaurentLocalFrame.openPoint X.hom x Valuation.one_apply_le_one
      U.1 hcU r hr).point.property
  let eCM := C.gaussCompatibleCenterFrame M hM r hr hru x
  let eCH := C.gaussCompatibleCenterFrame H hH r hr hru x
  let eCT := centerTensorFrame hb z eCM eCH
  let eM := C.gaussCompatibleTargetFrame M hM r hr hru x
  let eH := C.gaussCompatibleTargetFrame H hH r hr hru x
  let eU := (Functor.Monoidal.μIso (pullback U.1.ι) L K).symm ≪≫ tensorFrame eL eK
  let A := C.tensorLineActionComparison M H alpha beta
  let E := C.tensorFibreOneComparison M H L K e f
  let common := (pullback t).mapIso (Functor.Monoidal.μIso (pullback ref) L K).symm ≪≫
    (Functor.Monoidal.μIso (pullback t) ((pullback ref).obj L) ((pullback ref).obj K)).symm
  let refL := productReferenceResidueFrame L P U.1 hy eL
  let refK := productReferenceResidueFrame K P U.1 hy eK
  let modelM := C.productModelResidueFrame M L alpha e P eM
  let modelH := C.productModelResidueFrame H K beta f P eH
  have htarget : C.gaussCenterTargetFrame (M ⊗ H) r hr hru x eCT =
      (Functor.Monoidal.μIso
        (pullback (C.total.fromSpecResidueField (C.productTotalMap P.point))) M H).symm ≪≫
          tensorFrame eM eH := centerFrameGenericIso_tensor hb z eCM eCH
  have href : productReferenceResidueFrame (L ⊗ K) P U.1 hy eU =
      common ≪≫ tensorFrame refL refK :=
    (supportGenericFrame_localPullbackTensor ref P.point U.1 hy eL eK).trans
      (Iso.trans_assoc _ _ _).symm
  have hmodel : C.productModelResidueFrame (M ⊗ H) (L ⊗ K) A E P
      (C.gaussCenterTargetFrame (M ⊗ H) r hr hru x eCT) =
      common ≪≫ tensorFrame modelM modelH := by
    let prodM := C.productTotalLineIso M L alpha e
    let prodH := C.productTotalLineIso H K beta f
    let delta := (Functor.Monoidal.μIso (pullback C.productTotalMap) M H).symm
    let mu := Functor.Monoidal.μIso (pullback ref) L K
    let eT := (Functor.Monoidal.μIso
      (pullback (C.total.fromSpecResidueField (C.productTotalMap P.point))) M H).symm ≪≫
        tensorFrame eM eH
    have hp := inducedResidueFrame_postcomp C.productTotalMap (delta ≪≫ (prodM ⊗ᵢ prodH)) mu P eT
    have ht := inducedResidueFrame_tensor C.productTotalMap prodM prodH P eM eH
    have hg := C.productTotalLineIso_tensor_comparisons M H L K alpha beta e f
    have hfirst := congrArg (fun v => inducedResidueFrame C.productTotalMap v P eT) hg
    have hgroup := congrArg (fun v => inducedResidueFrame C.productTotalMap v P eT)
      (Iso.trans_assoc delta (prodM ⊗ᵢ prodH) mu).symm
    have hwhole := hfirst.trans (hgroup.trans hp)
    rw [ht] at hwhole
    have hT : C.gaussCenterTargetFrame (M ⊗ H) r hr hru x eCT = eT := htarget
    calc C.productModelResidueFrame (M ⊗ H) (L ⊗ K) A E P
          (C.gaussCenterTargetFrame (M ⊗ H) r hr hru x eCT)
        = inducedResidueFrame C.productTotalMap
            (C.productTotalLineIso (M ⊗ H) (L ⊗ K) A E) P eT :=
          congrArg (inducedResidueFrame C.productTotalMap
            (C.productTotalLineIso (M ⊗ H) (L ⊗ K) A E) P) hT
      _ = ((pullback t).mapIso mu).symm ≪≫
            (Functor.Monoidal.μIso (pullback t) ((pullback ref).obj L)
              ((pullback ref).obj K)).symm ≪≫ tensorFrame modelM modelH := hwhole
      _ = common ≪≫ tensorFrame modelM modelH :=
          (congrArg (fun F' => F' ≪≫ (Functor.Monoidal.μIso (pullback t) ((pullback ref).obj L)
            ((pullback ref).obj K)).symm ≪≫ tensorFrame modelM modelH)
            (Functor.mapIso_symm (pullback t) mu).symm).trans (Iso.trans_assoc _ _ _).symm
  have hAmpTensor := AmpleTensorLines.isAmple_tensor X.hom L K hAmpL hAmpK
  have hnativeT := C.gaussNativeNormFactor_eq_centerFactor (M ⊗ H) (hM.monoidalTensor hH)
    r hr hru x eCT (L ⊗ K) A E U.1 hy eU (hL.monoidalTensor hK) hAmpTensor hcU
  have hnativeM := C.gaussNativeNormFactor_eq_compatibleFactor M hM L alpha e hL
    r hr hru x hAmpL U.1 hcU hy eL
  have hnativeH := C.gaussNativeNormFactor_eq_compatibleFactor H hH K beta f hK
    r hr hru x hAmpK U.1 hcU hy eK
  rw [hnativeT, hnativeM, hnativeH]
  change P.residueVal (transitionUnit
      (productReferenceResidueFrame (L ⊗ K) P U.1 hy eU)
      (C.productModelResidueFrame (M ⊗ H) (L ⊗ K) A E P
        (C.gaussCenterTargetFrame (M ⊗ H) r hr hru x eCT))).val =
    P.residueVal (transitionUnit refL modelM).val * P.residueVal (transitionUnit refK modelH).val
  rw [href, hmodel]
  have hu := (transitionUnit_precompIso common (tensorFrame refL refK)
      (tensorFrame modelM modelH)).trans
    (transitionUnit_tensorFrame refL modelM refK modelH)
  exact (congrArg (fun u => P.residueVal (Units.val u)) hu).trans (P.residueVal.map_mul _ _)

/-- The actual original model potential of tensor action/fibre-one data
is the sum of the two original potentials, by the derived native unit product. -/
theorem gaussNativeModelPotential_tensor_comparisons
    (hAmpL : SchemeLineAmpleness.IsAmple X.hom L)
    (hAmpK : SchemeLineAmpleness.IsAmple X.hom K)
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    C.gaussNativeModelPotential (M ⊗ H) (hM.monoidalTensor hH) (L ⊗ K)
        (C.tensorLineActionComparison M H alpha beta) (C.tensorFibreOneComparison M H L K e f)
        (hL.monoidalTensor hK) r hr hru x =
      C.gaussNativeModelPotential M hM L alpha e hL r hr hru x +
        C.gaussNativeModelPotential H hH K beta f hK r hr hru x := by
  dsimp only [gaussNativeModelPotential]
  rw [C.gaussNativeNormFactor_tensor_comparisons M H hM hH L K alpha beta e f hL hK
    hAmpL hAmpK r hr hru x, NNReal.coe_mul]
  rw [Real.log_mul (NNReal.coe_ne_zero.mpr
    (C.gaussNativeNormFactor_pos M hM L alpha e hL r hr hru x).ne')
    (NNReal.coe_ne_zero.mpr
      (C.gaussNativeNormFactor_pos H hH K beta f hK r hr hru x).ne')]
  exact neg_add _ _

/-- The SAME literal power-tensor action/fibre data have the actual
potential b*phi+a*psi; ordinary generic power ampleness is the only extra input. -/
theorem gaussNativeModelPotential_powerTensor_comparisons
    (a b : ℕ)
    (hAmpLb : SchemeLineAmpleness.IsAmple X.hom (bundleTensorPower L b))
    (hAmpKa : SchemeLineAmpleness.IsAmple X.hom (bundleTensorPower K a))
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    C.gaussNativeModelPotential (bundleTensorPower M b ⊗ bundleTensorPower H a)
        ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hM b).monoidalTensor
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH a))
        (bundleTensorPower L b ⊗ bundleTensorPower K a)
        (C.powerTensorLineActionComparison M H alpha beta a b)
        (C.powerTensorFibreOneComparison M H L K e f a b)
        ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hL b).monoidalTensor
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hK a)) r hr hru x =
      (b : ℝ) * C.gaussNativeModelPotential M hM L alpha e hL r hr hru x +
        (a : ℝ) * C.gaussNativeModelPotential H hH K beta f hK r hr hru x := by
  refine (C.gaussNativeModelPotential_tensor_comparisons (bundleTensorPower M b)
      (bundleTensorPower H a)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM b)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH a)
    (bundleTensorPower L b) (bundleTensorPower K a)
    (C.powerLineActionComparison M alpha b) (C.powerLineActionComparison H beta a)
    (C.powerFibreOneComparison M L e b) (C.powerFibreOneComparison H K f a)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL b)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hK a) hAmpLb hAmpKa r hr hru x).trans ?_
  rw [C.gaussNativeModelPotential_power_comparisons M hM L alpha e hL b hAmpLb r hr hru x,
    C.gaussNativeModelPotential_power_comparisons H hH K beta f hK a hAmpKa r hr hru x]

/-- Actual central nefness and central auxiliary ampleness produce exact
finite FS data for the original potential sum.  The whole potential
identity is DERIVED above from the actual original tensor action data. -/
theorem isFinFS_power_tensor_potential_sum_of_central_nef [Infinite k]
    [IsIntegral C.total] [IsDominant C.projection]
    (hnef :
      letI : IsProjective (Limits.pullback.snd C.projection (zeroMap k)) :=
        C.centralProjection_isProjective
      NativeRealNumericalClasses.lineClass (Limits.pullback.snd C.projection (zeroMap k))
          ((pullback (zeroInclusion C.projection)).obj M)
              (hM.pullback (zeroInclusion C.projection)) ∈
        NativeRealNumericalClasses.nefCone (Limits.pullback.snd C.projection (zeroMap k)))
    (hAmp : SchemeLineAmpleness.IsAmple (Limits.pullback.snd C.projection (zeroMap k))
      ((pullback (zeroInclusion C.projection)).obj H))
    (a b : ℕ) (ha : 0 < a)
    (hAmpLb : SchemeLineAmpleness.IsAmple X.hom (bundleTensorPower L b))
    (hAmpKa : SchemeLineAmpleness.IsAmple X.hom (bundleTensorPower K a)) :
    letI : IsProper X.hom := C.original_isProper
    let Q := bundleTensorPower L b ⊗ bundleTensorPower K a
    let hQ := (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL b).monoidalTensor
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hK a)
    NativeLineFubiniStudy.IsFinFS X.hom Q hQ 1 (fun x =>
      (((b : ℝ) * C.gaussNativeModelPotential M hM L alpha e hL weightedFSRadius
          weightedFSRadius_properties.1 weightedFSRadius_properties.2.1 x +
        (a : ℝ) * C.gaussNativeModelPotential H hH K beta f hK weightedFSRadius
          weightedFSRadius_properties.1 weightedFSRadius_properties.2.1 x : ℝ) : EReal)) := by
  let : IsProper X.hom := C.original_isProper
  obtain ⟨D, hD, hNZ, hφ⟩ := C.isFinFS_power_tensor_modelPotential_of_central_nef M H hM hH L K
    hL hK alpha beta e f hnef hAmp a b ha
  refine ⟨D, hD, hNZ, fun x => ?_⟩
  refine Eq.trans ?_ (hφ x)
  exact congrArg (fun t : ℝ => (t : EReal))
    (C.gaussNativeModelPotential_powerTensor_comparisons M H hM hH L K alpha beta e f hL hK
      a b hAmpLb hAmpKa weightedFSRadius weightedFSRadius_properties.1
      weightedFSRadius_properties.2.1 x).symm

/-- Dividing the preceding exact realization by `b > 0` (`IsFinFS.divideDenominator`): the
real potential `pot(M) + (a / b) · pot(H)` is an exact finite rational FS function of class
`1 / b` for the same original line `L^{⊗ b} ⊗ K^{⊗ a}`, with the same sections and weights. -/
theorem isFinFS_potential_add_div_of_central_nef [Infinite k]
    [IsIntegral C.total] [IsDominant C.projection]
    (hnef :
      letI : IsProjective (Limits.pullback.snd C.projection (zeroMap k)) :=
        C.centralProjection_isProjective
      NativeRealNumericalClasses.lineClass (Limits.pullback.snd C.projection (zeroMap k))
          ((pullback (zeroInclusion C.projection)).obj M)
              (hM.pullback (zeroInclusion C.projection)) ∈
        NativeRealNumericalClasses.nefCone (Limits.pullback.snd C.projection (zeroMap k)))
    (hAmp : SchemeLineAmpleness.IsAmple (Limits.pullback.snd C.projection (zeroMap k))
      ((pullback (zeroInclusion C.projection)).obj H))
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hAmpLb : SchemeLineAmpleness.IsAmple X.hom (bundleTensorPower L b))
    (hAmpKa : SchemeLineAmpleness.IsAmple X.hom (bundleTensorPower K a)) :
    letI : IsProper X.hom := C.original_isProper
    let Q := bundleTensorPower L b ⊗ bundleTensorPower K a
    let hQ := (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL b).monoidalTensor
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hK a)
    NativeLineFubiniStudy.IsFinFS X.hom Q hQ (1 / (b : ℚ)) (fun x =>
      ((C.gaussNativeModelPotential M hM L alpha e hL weightedFSRadius
          weightedFSRadius_properties.1 weightedFSRadius_properties.2.1 x +
        ((a : ℝ) / (b : ℝ)) * C.gaussNativeModelPotential H hH K beta f hK weightedFSRadius
          weightedFSRadius_properties.1 weightedFSRadius_properties.2.1 x : ℝ) : EReal)) := by
  let : IsProper X.hom := C.original_isProper
  obtain ⟨D, hD, hNZ, hφ⟩ := NativeLineFubiniStudy.IsFinFS.divideDenominator X.hom _ b hb
    (C.isFinFS_power_tensor_potential_sum_of_central_nef M H hM hH L K alpha beta e f hL hK
      hnef hAmp a b ha hAmpLb hAmpKa)
  refine ⟨D, hD, hNZ, fun x => Eq.trans ?_ (hφ x)⟩
  dsimp only
  rw [← EReal.coe_mul]
  congr 1
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
