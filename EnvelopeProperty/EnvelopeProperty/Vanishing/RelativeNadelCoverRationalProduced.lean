import EnvelopeProperty.Vanishing.RelativeNadelCoverGeometry
import EnvelopeProperty.Vanishing.RelativeNadelCoverRationalAmple

/-! # Actual original rational SNC inputs produce the whole ample relative cover -/
noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
open scoped BigOperators
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelCoverRationalProduced
open CanonicalGeometry Char0 NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedRoots
open NadelAuxiliaryBranchSectionsAmple
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original rational ample data internally produces the actual auxiliary
sections, entire finite smooth normalized cover and its actual ample rounded
line over the SAME original R.  No sections, cover or power certificate is input. -/
theorem exists_original_ample_rounded_cover
    {X : Scheme.{u}} [IsIntegral X] {k R : Type u} [Field k] [CharZero k] [CommRing R]
    (p : X ⟶ Spec (.of k)) [FiniteType p] (π : X ⟶ Spec (.of R))
    (n : ℕ) [SmoothOfRelativeDimension n p]
    (F : X.DivisorFamily) (hF : F.IsSnc) (M : X.Modules) (hM : IsInvertible M)
    (J : X.IdealSheafData) (hJ : J.IsIdealOfSncDivisor)
    (b : F.ι → ℕ) (hJF : J = ∏ i, F.component i ^ b i)
    (q : ℚ) (hq : 0 ≤ q) (d : ℕ) (hdpos : 0 < d) (hd : q.den ∣ d)
    (hA : SchemeLineAmpleness.IsAmple π
      (tensorObj (bundleTensorPower M d) (J ^ (q.num.toNat * (d / q.den))).toModules)) :
    let hD := component_isInvertible p n F hF
    ∃ (L : F.ι → X.Modules) (hL : ∀ i, IsInvertible (L i))
      (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
        tensorObj (bundleTensorPower (L i) q.den) (F.component i).toModules)),
      (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
        (OriginalData.ideals F n L (fun _ => q.den) σ hL hD)).IsSnc ∧
      (∀ i, (⨆ j, OriginalData.ideals F n L (fun _ => q.den) σ hL hD i j) = ⊤) ∧
      IsFinite (normalizedToOriginal (OriginalData.data F n L (fun _ => q.den) σ)) ∧
      SmoothOfRelativeDimension n
        (normalizedToOriginal (OriginalData.data F n L (fun _ => q.den) σ) ≫ p) ∧
      SchemeLineAmpleness.IsAmple
        (normalizedToOriginal (OriginalData.data F n L (fun _ => q.den) σ) ≫ π)
        (originalRoundedCoverLine F n L q σ hL M J hJ b) := by
  let H := tensorObj (bundleTensorPower M d) (J ^ (q.num.toNat * (d / q.den))).toModules
  let hD := component_isInvertible p n F hF
  obtain ⟨a, _ha, _hV, σ, hG, hRows, hfinite, _hflat, hsmooth, _hproj⟩ :=
    RelativeNadelCoverGeometry.exists_original_finite_flat_smooth_projective
      p π n F hF H hA (fun _ => q.den) (fun _ => q.den_pos)
  let L : F.ι → X.Modules := fun _ => bundleTensorPower H a
  have hL : ∀ i, IsInvertible (L i) :=
    fun _ => TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible a
  refine ⟨L, hL, σ, hG, hRows, hfinite, hsmooth, ?_⟩
  exact RelativeNadelCoverRationalAmple.originalRoundedCoverLine_isAmple
    F n L q σ hL hD p π hG hRows M hM J hJ hF b hJF hq d hdpos hd hA

end EnvelopeProperty.Vanishing.RelativeNadelCoverRationalProduced
