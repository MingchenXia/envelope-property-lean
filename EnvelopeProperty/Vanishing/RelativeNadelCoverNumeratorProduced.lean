import EnvelopeProperty.Vanishing.RelativeNadelCoverNumeratorAmple
import EnvelopeProperty.Vanishing.RelativeNadelCoverRationalProduced

/-! # The fixed original relative source internally produces its whole ample cover

The original ample perturbed numerator supplies the auxiliary ample seed.
Its actual denominator and native whole pullback-power comparison feed the
actual relative Bertini/cover producer. The original intrinsic rounded
ideal and original affine base are retained throughout.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
open CategoryTheory.MonoidalCategory
open scoped BigOperators
universe u

namespace EnvelopeProperty.Vanishing.RelativeNadelCoverNumeratorProduced
open CanonicalGeometry Char0 RelativeNadelCoverWeightedExceptional
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedRoots
open NadelAuxiliaryBranchSectionsAmple
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [FiniteType f] [IsSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
local notation "S" => NadelRelativePrincipalization.sequence f n I hI
local notation "μ" => Scheme.BlowUpSequence.composite (NadelRelativePrincipalization.sequence f n I hI)
local notation "g" => Scheme.BlowUpSequence.composite (NadelRelativePrincipalization.sequence f n I hI) ≫ f
local notation "J" => Scheme.IdealSheafData.comap I
  (Scheme.BlowUpSequence.composite (NadelRelativePrincipalization.sequence f n I hI))

private instance originalLastIntegral : IsIntegral (S).last :=
  NadelRelativePrincipalization.last_isIntegral f n I hI

/-- The SAME fixed original Nadel source internally produces its actual BP
geometry, perturbed SNC numerator, SAME original intrinsic rounding, original
Bertini sections and whole finite smooth adapted cover. The actual original
rounded cover line is ample over the SAME original arbitrary affine base. -/
theorem exists_original_numerator_cover
    {R : Type u} [CommRing R] [Algebra k R] (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (M : X.Modules) (hM : IsInvertible M) (B : X.Modules) (hB : IsInvertible B)
    (C : X.Modules) (hC : SchemeLineAmpleness.IsAmple π C)
    (G : (I.toModules ⊗ B).GeneratingSections) (hG : G.IsFiniteType)
    (q : ℚ) (hq : 0 ≤ q) (d t : ℕ) (hd : 0 < d) (hdt : (d : ℚ) * q = (t : ℚ))
    (e₀ : bundleTensorPower M d ≅ C ⊗ bundleTensorPower B t) (lowerBound : ℕ) :
    SmoothOfRelativeDimension n g ∧ Nonempty (S).last ∧
    ∃ (w : Fin (S).length → ℕ) (N a : ℕ),
      let K := J ^ a * weightedIdeal f n I hI w
      ∃ (hK : K.IsIdealOfSncDivisor),
      (∀ i, 0 < w i) ∧ 0 < N ∧ lowerBound ≤ N ∧ q.den ∣ N ∧
      a * q.den = q.num.toNat * N ∧ a * d = t * N ∧
      ((1 : ℚ) / (N : ℚ)).den = N ∧
      RoundedSncIdealSheaf.rounded K hK ((1 : ℚ) / (N : ℚ)) =
        RoundedSncIdealSheaf.rounded J
          (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q ∧
      ∃ (F : (S).last.DivisorFamily) (b : F.ι → ℕ) (_hF : F.IsSnc)
        (hD : ∀ i, (F.component i).IsInvertible),
      K = ∏ i, F.component i ^ b i ∧
      ∃ (L : F.ι → (S).last.Modules) (hL : ∀ i, IsInvertible (L i))
        (σ : ∀ i, Fin (n + 1) → (unitObj (S).last ⟶
          Scheme.Modules.tensorObj (bundleTensorPower (L i) ((1 : ℚ) / (N : ℚ)).den)
            (F.component i).toModules)),
        (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
          (OriginalData.ideals F n L (fun _ => ((1 : ℚ) / (N : ℚ)).den) σ hL hD)).IsSnc ∧
        (∀ i, (⨆ j, OriginalData.ideals F n L
          (fun _ => ((1 : ℚ) / (N : ℚ)).den) σ hL hD i j) = ⊤) ∧
        IsFinite (normalizedToOriginal
          (OriginalData.data F n L (fun _ => ((1 : ℚ) / (N : ℚ)).den) σ)) ∧
        SmoothOfRelativeDimension n (normalizedToOriginal
          (OriginalData.data F n L (fun _ => ((1 : ℚ) / (N : ℚ)).den) σ) ≫ g) ∧
        SchemeLineAmpleness.IsAmple (normalizedToOriginal
          (OriginalData.data F n L (fun _ => ((1 : ℚ) / (N : ℚ)).den) σ) ≫ ((S).composite ≫ π))
          (originalRoundedCoverLine F n L ((1 : ℚ) / (N : ℚ)) σ hL
            ((pullback μ).obj M) K hK b) := by
  let : SmoothOfRelativeDimension n g :=
    NadelRelativePrincipalization.stage_smoothOfRelativeDimension f n I hI (Fin.last _)
  let : IsProper (S).composite := NadelRelativePrincipalization.composite_isProper f n I hI
  let : FiniteType g :=
    { toLocallyOfFiniteType := locallyOfFiniteType_comp μ f
      toQuasiCompact := quasiCompact_comp μ f }
  refine ⟨inferInstance, NadelRelativePrincipalization.last_nonempty f n I hI, ?_⟩
  obtain ⟨w, N, a, hK, hw, hN, hbound, hdiv, ha, had, hround, hP⟩ :=
    RelativeNadelCoverNumeratorAmple.exists_ample_perturbed_numerator f n I hI π hπ
      M hM B hB C hC G hG q hq d t hd hdt e₀ lowerBound
  let K := J ^ a * weightedIdeal f n I hI w
  let q' : ℚ := 1 / (N : ℚ)
  have hden : q'.den = N := by
    simpa only [q', one_div] using Rat.inv_natCast_den_of_pos hN
  have hnum : q'.num = 1 := by
    simpa only [q', one_div] using Rat.inv_natCast_num_of_pos hN
  have hq' : 0 ≤ q' := by dsimp only [q']; positivity
  let MY := (pullback μ).obj M
  have hMY : IsInvertible MY := hM.pullback μ
  let eP : ((pullback μ).obj (bundleTensorPower M N) ⊗ K.toModules) ≅
      Scheme.Modules.tensorObj (bundleTensorPower MY N) K.toModules :=
    ((BundleTensorPowerPullback.pullbackIso μ M N) ⊗ᵢ Iso.refl K.toModules) ≪≫
      ModularCurves.monoidalTensorObjIso _ _
  have hA₀ : SchemeLineAmpleness.IsAmple ((S).composite ≫ π)
      (Scheme.Modules.tensorObj (bundleTensorPower MY N) K.toModules) :=
    AmpleTensorLines.ample_of_iso hP eP
  have hA : SchemeLineAmpleness.IsAmple ((S).composite ≫ π)
      (Scheme.Modules.tensorObj (bundleTensorPower MY N) (K ^ (q'.num.toNat * (N / q'.den))).toModules) := by
    simpa only [hden, hnum, Int.toNat_one, one_mul,
      Nat.div_self hN, pow_one] using hA₀
  have hKpresentation : K.IsIdealOfSncDivisor := hK
  obtain ⟨F, b, hF, hKF⟩ := hKpresentation
  let hD := component_isInvertible g n F hF
  obtain ⟨L, hL, σ, hAux, hRows, hfinite, hsmooth, hAmp⟩ :=
    RelativeNadelCoverRationalProduced.exists_original_ample_rounded_cover
      g ((S).composite ≫ π) n F hF MY hMY K hK b hKF q' hq' N hN (hden ▸ dvd_refl N) hA
  exact ⟨w, N, a, hK, hw, hN, hbound, hdiv, ha, had, hden, hround,
    F, b, hF, hD, hKF, L, hL, σ, hAux, hRows, hfinite, hsmooth, hAmp⟩

end EnvelopeProperty.Vanishing.RelativeNadelCoverNumeratorProduced
