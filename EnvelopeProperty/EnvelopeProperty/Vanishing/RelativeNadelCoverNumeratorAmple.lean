import EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedAmple
import EnvelopeProperty.Vanishing.RelativeNadelCoverNumeratorPower
import EnvelopeProperty.Vanishing.RelativeNadelCoverPulledPowers
import EnvelopeProperty.Vanishing.NadelNefBigGlobalGenerators
import EnvelopeProperty.AlgGeom.AmpleLinePositivePowers

/-! # Actual ampleness of the SAME original fixed-source perturbed numerator

The original C and original generating family of I tensor B are retained.
All exceptional weights, bounds, perturbed ideal, rounding and actual ample
numerator are produced internally, with genuine whole power comparisons.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.MonoidalCategory
open Scheme.Modules Scheme.IdealSheafData
universe u

namespace EnvelopeProperty.Vanishing.RelativeNadelCoverNumeratorAmple
open CanonicalGeometry Char0 RelativeNadelCoverWeightedExceptional
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private noncomputable instance actualPullbackMonoidal {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pullback g).Monoidal := pullbackMonoidal g

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [FiniteType f] [IsSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
local notation "S" => NadelRelativePrincipalization.sequence f n I hI

/-- Fixed original source positivity and SAME original finite generators
internally produce a genuinely ample perturbed numerator on the SAME BP,
retaining the ENTIRE original intrinsic rounded ideal and original q. -/
theorem exists_ample_perturbed_numerator
    {R : Type u} [CommRing R] [Algebra k R] (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (M : X.Modules) (hM : IsInvertible M) (B : X.Modules) (hB : IsInvertible B)
    (C : X.Modules) (hC : SchemeLineAmpleness.IsAmple π C)
    (G : (I.toModules ⊗ B).GeneratingSections) (hG : G.IsFiniteType)
    (q : ℚ) (hq : 0 ≤ q) (d t : ℕ) (hd : 0 < d) (hdt : (d : ℚ) * q = (t : ℚ))
    (e₀ : bundleTensorPower M d ≅ C ⊗ bundleTensorPower B t) (lowerBound : ℕ) :
    ∃ (w : Fin (S).length → ℕ) (N a : ℕ)
      (hK : ((I.comap (S).composite) ^ a * weightedIdeal f n I hI w).IsIdealOfSncDivisor),
      (∀ i, 0 < w i) ∧ 0 < N ∧ lowerBound ≤ N ∧ q.den ∣ N ∧
      a * q.den = q.num.toNat * N ∧ a * d = t * N ∧
      RoundedSncIdealSheaf.rounded
          ((I.comap (S).composite) ^ a * weightedIdeal f n I hI w) hK
          ((1 : ℚ) / (N : ℚ)) =
        RoundedSncIdealSheaf.rounded (I.comap (S).composite)
          (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q ∧
      SchemeLineAmpleness.IsAmple ((S).composite ≫ π)
        ((pullback (S).composite).obj (bundleTensorPower M N) ⊗
          ((I.comap (S).composite) ^ a * weightedIdeal f n I hI w).toModules) := by
  let μ := (S).composite
  let g := μ ≫ π
  let gp := μ ≫ f
  let P := pullback μ
  let J := I.comap μ
  let : IsIntegral (S).last := NadelRelativePrincipalization.last_isIntegral f n I hI
  let : SmoothOfRelativeDimension n gp :=
    NadelRelativePrincipalization.stage_smoothOfRelativeDimension f n I hI (Fin.last _)
  let : Smooth gp := SmoothOfRelativeDimension.smooth n gp
  have hJ : J.IsInvertible :=
    (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI).isInvertible gp
  obtain ⟨w, r, hw, hr, hE⟩ :=
    RelativeNadelCoverWeightedAmple.exists_positive_weights_isAmple (S) f π hπ C hC
  let E := weightedIdeal f n I hI w
  let Ed := bundleTensorPower E.toModules d
  let A := Ed ⊗ P.obj (bundleTensorPower C (r * d))
  have hEd : SchemeLineAmpleness.IsAmple g
      (bundleTensorPower (E.toModules ⊗ P.obj (bundleTensorPower C r)) d) :=
    AmpleLinePositivePowers.isAmple_tensorPower g _ hE d hd
  let eA : bundleTensorPower (E.toModules ⊗ P.obj (bundleTensorPower C r)) d ≅ A :=
    BundleTensorPowerTensor.powerTensorIso E.toModules (P.obj (bundleTensorPower C r)) d ≪≫
      (Iso.refl Ed ⊗ᵢ
        ((BundleTensorPowerPullback.pullbackIso μ (bundleTensorPower C r) d).symm ≪≫
          P.mapIso (BundleTensorPowerPullback.powerMulIso C r d)))
  have hA : SchemeLineAmpleness.IsAmple g A := AmpleTensorLines.ample_of_iso hEd eA
  obtain ⟨N₀, hN₀⟩ :=
    RelativeNadelCoverPulledPowers.exists_eventual_isAmple_tensor_pullback π C hC μ A hA
  obtain ⟨N, a, hK, hN, hbound, hden, ha, hcoeff, hround, ⟨ePower⟩⟩ :=
    RelativeNadelCoverNumeratorPower.exists_perturbed_numerator_powerIso f n I hI w q hq
      (max lowerBound (r * d + N₀)) M B C d t hdt e₀
  have hgiven : lowerBound ≤ N := (le_max_left _ _).trans hbound
  have hlarge : r * d + N₀ ≤ N := (le_max_right _ _).trans hbound
  let b := N - r * d
  have hb : N₀ ≤ b := by dsimp only [b]; omega
  have hsum : r * d + b = N := by dsimp only [b]; omega
  let eExpand : A ⊗ P.obj (bundleTensorPower C b) ≅ Ed ⊗ P.obj (bundleTensorPower C N) :=
    α_ Ed (P.obj (bundleTensorPower C (r * d))) (P.obj (bundleTensorPower C b)) ≪≫
      (Iso.refl Ed ⊗ᵢ
        (Functor.Monoidal.μIso P (bundleTensorPower C (r * d)) (bundleTensorPower C b) ≪≫
          P.mapIso (TensorPowerBaseIdealGrading.tensorPowerAddIso C (r * d) b) ≪≫
          P.mapIso (eqToIso (congrArg (bundleTensorPower C) hsum))))
  have hEN : SchemeLineAmpleness.IsAmple g (Ed ⊗ P.obj (bundleTensorPower C N)) :=
    AmpleTensorLines.ample_of_iso (hN₀ b hb) eExpand
  let L := J.toModules ⊗ P.obj B
  have hL : IsInvertible L :=
    (hJ.isInvertibleModule_toModules.tensorObj (hB.pullback μ)).of_iso
      (ModularCurves.monoidalTensorObjIso J.toModules (P.obj B))
  let H := NadelNefBigGlobalGenerators.comapGenerators I μ B hB G
  have hH : H.IsFiniteType :=
    NadelNefBigGlobalGenerators.generators_isFiniteType I μ B hB G (hG := hG)
  obtain ⟨Q, hQ⟩ := GeneratedLineTensorPowers.exists_generatingSections_tensorPower g L hL H hH (a * d)
  have hR : SchemeLineAmpleness.IsAmple g
      ((Ed ⊗ P.obj (bundleTensorPower C N)) ⊗ bundleTensorPower L (a * d)) :=
    AmpleTensorLines.isAmple_tensor_of_generatingSections g _ _ hEN
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (a * d)) Q hQ
  let K := J ^ a * E
  let T := P.obj (bundleTensorPower M N) ⊗ K.toModules
  have hPower : SchemeLineAmpleness.IsAmple g (bundleTensorPower T d) :=
    AmpleTensorLines.ample_of_iso hR ePower.symm
  have hT : IsInvertible T :=
    (((TensorPowerBaseIdealGrading.tensorPower_isInvertible hM N).pullback μ).tensorObj
      (hK.isInvertible gp).isInvertibleModule_toModules).of_iso
      (ModularCurves.monoidalTensorObjIso (P.obj (bundleTensorPower M N)) K.toModules)
  have hTample : SchemeLineAmpleness.IsAmple g T :=
    AmpleLinePositivePowers.isAmple_of_tensorPower g T hT d hd hPower
  exact ⟨w, N, a, hK, hw, hN, hgiven, hden, ha, hcoeff, hround, hTample⟩

end EnvelopeProperty.Vanishing.RelativeNadelCoverNumeratorAmple
