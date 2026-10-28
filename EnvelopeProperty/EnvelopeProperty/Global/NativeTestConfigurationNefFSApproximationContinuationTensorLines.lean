import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationTensorComparisons
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedWholeGeneratorExactFS
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionNefAmple
import EnvelopeProperty.AlgGeom.NativeProjectivityFromPolynomialFactorization
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberSectionLifting
import EnvelopeProperty.AlgGeom.AmpleTensorLines
import EnvelopeProperty.Projective.FactorizationBaseChange

/-! # Central nefness gives exact finite FS functions for power-tensor perturbations

Let `C : TestConfiguration k X` be a test configuration, `M` a line on the total space whose
restriction to the (scheme-theoretic, possibly reducible or nonreduced) central fibre
`𝒳₀ = π⁻¹(0)` is nef on every closed integral curve, and `H` a line whose restriction to
`𝒳₀` is ample.

* `centralProjection_isProjective`: `𝒳₀ → Spec k` is projective (base change of the
  projective factorization of `π : 𝒳 → 𝔸¹`).
* `central_ample_power_tensor_of_nef`: `(M^{⊗ b} ⊗ H^{⊗ a})|_{𝒳₀}` is ample for `a > 0`
  (nef + ample is ample, `SeshadriAmplenessCriterionNefAmple.isAmple_tensor_nef`, the
  Kleiman/Nakai consequence used in FHX §5 and BJ22).
* `isFinFS_power_tensor_modelPotential_of_central_nef`: with the action and fibre-one
  comparisons of `…ContinuationTensorComparisons`, the native model potential of
  `M^{⊗ b} ⊗ H^{⊗ a}` is an exact finite rational FS function of class `1` for
  `L^{⊗ b} ⊗ K^{⊗ a}` (central ampleness ⇒ exact FS,
  `ProjectiveCentralFiberEmbeddingNeighborhoodClosedWholeGeneratorExactFS`).

No potential additivity formula is used here; the identification of that potential with
`b · pot(M) + a · pot(H)` is `…ContinuationTensorPotential`.
-/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint CanonicalGeometry
open ProjectiveCentralFiberSectionLifting
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
  (C : TestConfiguration k X)

/-- The SAME whole scheme-theoretic central fibre is genuinely projective,
derived by base change of the original parameter projection. -/
theorem centralProjection_isProjective :
    IsProjective (Limits.pullback.snd C.projection (zeroMap k)) := by
  let : Algebra (Polynomial k) k := (Polynomial.evalRingHom (0 : k)).toAlgebra
  apply NativeProjectivityFromPolynomialFactorization.of_isProjectiveFactorization
  change IsProjectiveFactorization (FlatGlobalSections.structureMap (S := k) C.projection)
  exact ProjectiveFactorizationBaseChange.baseChange (S := k) C.projection
    C.projection_isProjectiveFactorization

/-- Actual central curve-nefness and an actual central ample auxiliary line
derive central ampleness of the SAME literal perturbation.  The whole zero
fibre may be reducible or nonreduced, and all power conditions are internal. -/
theorem central_ample_power_tensor_of_nef
    (M H : C.total.Modules) (hM : IsInvertible M)
    (hnef :
      letI : IsProjective (Limits.pullback.snd C.projection (zeroMap k)) :=
        C.centralProjection_isProjective
      NativeRealNumericalClasses.lineClass (Limits.pullback.snd C.projection (zeroMap k))
          ((pullback (zeroInclusion C.projection)).obj M)
              (hM.pullback (zeroInclusion C.projection)) ∈
        NativeRealNumericalClasses.nefCone (Limits.pullback.snd C.projection (zeroMap k)))
    (hAmp : SchemeLineAmpleness.IsAmple (Limits.pullback.snd C.projection (zeroMap k))
      ((pullback (zeroInclusion C.projection)).obj H))
    (a b : ℕ) (ha : 0 < a) :
    SchemeLineAmpleness.IsAmple (Limits.pullback.snd C.projection (zeroMap k))
      ((pullback (zeroInclusion C.projection)).obj
        (bundleTensorPower M b ⊗ bundleTensorPower H a)) := by
  let p := Limits.pullback.snd C.projection (zeroMap k)
  let i := zeroInclusion C.projection
  let : IsProjective p := C.centralProjection_isProjective
  let F := pullback i
  let : F.Monoidal := pullbackMonoidal i
  let N := F.obj M
  let A := F.obj H
  let hN : IsInvertible N := hM.pullback i
  have hNef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p := hnef
  have hPowerNef : NativeRealNumericalClasses.lineClass p (bundleTensorPower N b)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN b) ∈
        NativeRealNumericalClasses.nefCone p := by
    rw [NativeRealNumericalClasses.lineClass_tensorPower]
    exact NativeRealNumericalClasses.nefCone_smul_nonneg p hNef (by positivity)
  have hPowerAmp := SeshadriAmplenessCriterionNefAmple.positive_power_ample_general p A hAmp a ha
  have h := SeshadriAmplenessCriterionNefAmple.isAmple_tensor_nef p
    (bundleTensorPower N b) (bundleTensorPower A a)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN b) hPowerNef hPowerAmp
  let e : F.obj (bundleTensorPower M b ⊗ bundleTensorPower H a) ≅
      bundleTensorPower N b ⊗ bundleTensorPower A a :=
    (Functor.Monoidal.μIso F (bundleTensorPower M b) (bundleTensorPower H a)).symm ≪≫
      (BundleTensorPowerPullback.pullbackIso i M b ⊗ᵢ BundleTensorPowerPullback.pullbackIso i H a)
  exact AmpleTensorLines.ample_of_iso h e.symm

/-- Central nefness and the actual central ample auxiliary line produce an
EXACT finite rational FS realization of the defined tensor-model potential.
No central ampleness of the perturbation or desired potential identity is input. -/
theorem isFinFS_power_tensor_modelPotential_of_central_nef [Infinite k]
    [IsIntegral C.total] [IsDominant C.projection]
    (M H : C.total.Modules) (hM : IsInvertible M) (hH : IsInvertible H)
    (L K : X.left.Modules) (hL : IsInvertible L) (hK : IsInvertible K)
    (alpha : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (beta : (pullback C.lineActionMap).obj H ≅ (pullback C.lineProjectionMap).obj H)
    (e : (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)
    (f : (pullback C.fibreOneInclusion.left).obj H ≅
      (pullback C.fibreOneIso.hom.left).obj K)
    (hnef :
      letI : IsProjective (Limits.pullback.snd C.projection (zeroMap k)) :=
        C.centralProjection_isProjective
      NativeRealNumericalClasses.lineClass (Limits.pullback.snd C.projection (zeroMap k))
          ((pullback (zeroInclusion C.projection)).obj M)
              (hM.pullback (zeroInclusion C.projection)) ∈
        NativeRealNumericalClasses.nefCone (Limits.pullback.snd C.projection (zeroMap k)))
    (hAmp : SchemeLineAmpleness.IsAmple (Limits.pullback.snd C.projection (zeroMap k))
      ((pullback (zeroInclusion C.projection)).obj H))
    (a b : ℕ) (ha : 0 < a) :
    letI : IsProper X.hom := C.original_isProper
    let P := bundleTensorPower M b ⊗ bundleTensorPower H a
    let hP := (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM b).monoidalTensor
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH a)
    let Q := bundleTensorPower L b ⊗ bundleTensorPower K a
    let hQ := (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL b).monoidalTensor
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hK a)
    NativeLineFubiniStudy.IsFinFS X.hom Q hQ 1
      (fun x => (C.gaussNativeModelPotential P hP Q
        (C.powerTensorLineActionComparison M H alpha beta a b)
        (C.powerTensorFibreOneComparison M H L K e f a b) hQ weightedFSRadius
        weightedFSRadius_properties.1 weightedFSRadius_properties.2.1 x : EReal)) := by
  let : IsProper X.hom := C.original_isProper
  dsimp only
  exact ProjectiveCentralFiberEmbeddingNeighborhoodClosedWholeGeneratorExactFS.isFinFS_modelPotential_of_central_ample
    C (bundleTensorPower M b ⊗ bundleTensorPower H a)
    ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hM b).monoidalTensor
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH a))
    (bundleTensorPower L b ⊗ bundleTensorPower K a)
    (C.powerTensorLineActionComparison M H alpha beta a b)
    (C.powerTensorFibreOneComparison M H L K e f a b)
    ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hL b).monoidalTensor
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hK a))
    (C.central_ample_power_tensor_of_nef M H hM hnef hAmp a b ha)

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
