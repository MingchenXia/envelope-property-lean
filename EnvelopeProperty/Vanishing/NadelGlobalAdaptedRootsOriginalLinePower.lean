import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsOriginalRounding

/-! # The actual whole cover line of the ORIGINAL rational SNC exponent

The original intrinsic rounded ideal and original denominator determine every
fractional row weight and the same actual whole cover line. Its whole power
isomorphism to the pullback of the original rational positive line is proved.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
open scoped BigOperators
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
open CanonicalGeometry Char0 NadelAuxiliaryMulticover NadelGlobalNormalization

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
  (L : F.ι → X.Modules) (q : ℚ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
    tensorObj (bundleTensorPower (L i) q.den) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i))

/-- The ORIGINAL rational SNC exponent and intrinsic original rounded ideal
determine the actual line on the SAME whole native adapted normalization. -/
def originalRoundedCoverLine (M : X.Modules) (J : X.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (b : F.ι → ℕ) :
    (normalizedScheme (OriginalData.data F n L (fun _ => q.den) σ)).Modules :=
  wholeRoundedLine F n L (fun _ => q.den) σ hL
    (tensorObj M (RoundedCanonicalModule.idealModule J hJ q))
    (fun i => fractionalRootWeight q (b i))

variable (hD : ∀ i, (F.component i).IsInvertible)
  {k : Type u} [Field k] [CharZero k]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
  (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
    (OriginalData.ideals F n L (fun _ => q.den) σ hL hD)).IsSnc)
  (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L (fun _ => q.den) σ hL hD i j) = ⊤)

include hD f hG hRows

/-- The SAME original rounded cover line has its actual whole original
rational line power comparison. No arbitrary residue, rounding, chart matching,
power-isomorphism, or cover geometry certificate is supplied. -/
def originalRoundedCoverLinePowerIso (M : X.Modules) (J : X.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (hF : F.IsSnc) (b : F.ι → ℕ)
    (hJF : J = ∏ i, F.component i ^ b i) (hq : 0 ≤ q)
    (d : ℕ) (hd : q.den ∣ d) :
    bundleTensorPower (originalRoundedCoverLine F n L q σ hL M J hJ b) d ≅
      (pullback (normalizedToOriginal (OriginalData.data F n L (fun _ => q.den) σ))).obj
        (tensorObj (bundleTensorPower M d) (J ^ (q.num.toNat * (d / q.den))).toModules) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hfield : IsUnit (q.den : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr q.den_ne_zero)
  exact wholeRoundedLinePowerIso F n L (fun _ => q.den) σ hL hD f hG hRows
      (fun _ => q.den_pos) (fun _ => hfield)
      (tensorObj M (RoundedCanonicalModule.idealModule J hJ q))
      (fun i => fractionalRootWeight q (b i)) d (fun _ => hd) ≪≫
    (pullback (normalizedToOriginal (OriginalData.data F n L (fun _ => q.den) σ))).mapIso
      (originalClearedRoundedLineIso f J hJ F hF b hJF M q hq d hd)

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
