import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsOriginalLinePower
import EnvelopeProperty.Vanishing.NadelGlobalAdaptedModelGeometry
import EnvelopeProperty.Vanishing.RelativeFiniteAmplePullback
import EnvelopeProperty.AlgGeom.AmpleLinePositivePowers

/-! # Actual original rounded root-line ampleness over an arbitrary base

The same original rational exponent, actual whole line-power comparison and
entire finite cover are retained.  The original coefficient ring need not be
a domain, and smoothness is over the original field, not over that ring.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
open scoped BigOperators
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelCoverRationalAmple
open CanonicalGeometry Char0 NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedRoots
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
  (L : F.ι → X.Modules) (q : ℚ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
    tensorObj (bundleTensorPower (L i) q.den) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
  {k R : Type u} [Field k] [CharZero k] [CommRing R]
  (p : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n p] (π : X ⟶ Spec (.of R))
  (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
    (OriginalData.ideals F n L (fun _ => q.den) σ hL hD)).IsSnc)
  (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L (fun _ => q.den) σ hL hD i j) = ⊤)

include hD p hG hRows

/-- The actual original cleared ample line proves ampleness of the SAME
entire original rounded root line over the SAME arbitrary coefficient ring. -/
theorem originalRoundedCoverLine_isAmple (M : X.Modules) (hM : IsInvertible M)
    (J : X.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (hF : F.IsSnc)
    (b : F.ι → ℕ) (hJF : J = ∏ i, F.component i ^ b i) (hq : 0 ≤ q)
    (d : ℕ) (hdpos : 0 < d) (hd : q.den ∣ d)
    (hA : SchemeLineAmpleness.IsAmple π
      (tensorObj (bundleTensorPower M d) (J ^ (q.num.toNat * (d / q.den))).toModules)) :
    SchemeLineAmpleness.IsAmple
      (normalizedToOriginal (OriginalData.data F n L (fun _ => q.den) σ) ≫ π)
      (originalRoundedCoverLine F n L q σ hL M J hJ b) := by
  let : Smooth p := SmoothOfRelativeDimension.smooth n p
  have htame : IsUnit (q.den : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr q.den_ne_zero)
  obtain ⟨hfinite, _hflat, _hsmooth⟩ := NadelGlobalAdaptedModel.finite_flat_smooth
    F n L (fun _ => q.den) σ hL hD p hG hRows
    (fun _ => q.den_pos) (fun _ => htame)
  let ν := normalizedToOriginal (OriginalData.data F n L (fun _ => q.den) σ)
  let : IsFinite ν := hfinite
  have hC : IsInvertible (tensorObj M (RoundedCanonicalModule.idealModule J hJ q)) :=
    hM.tensorObj (RoundedCanonicalModule.idealModule_isInvertible p J hJ q)
  have hN : IsInvertible (originalRoundedCoverLine F n L q σ hL M J hJ b) :=
    wholeRoundedLine_isInvertible F n L (fun _ => q.den) σ hL hD p hG hRows
      (fun _ => q.den_pos) (fun _ => htame)
      (tensorObj M (RoundedCanonicalModule.idealModule J hJ q)) hC
      (fun i => fractionalRootWeight q (b i))
  have hPull := RelativeFiniteAmplePullback.isAmple_pullback π _ hA ν
  exact AmpleLinePositivePowers.isAmple_of_tensorPower (ν ≫ π) _ hN d hdpos
    (AmpleTensorLines.ample_of_iso hPull
      (originalRoundedCoverLinePowerIso F n L q σ hL hD p hG hRows
        M J hJ hF b hJF hq d hd).symm)

end EnvelopeProperty.Vanishing.RelativeNadelCoverRationalAmple
