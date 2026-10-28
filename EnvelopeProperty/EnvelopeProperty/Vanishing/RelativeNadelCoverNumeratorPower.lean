import EnvelopeProperty.Vanishing.RelativeNadelCoverWeightedExceptionalRounding
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealPowers
import EnvelopeProperty.AlgGeom.BundleTensorPowerTensor

/-! # The SAME whole original fixed-source perturbed numerator power

Original M/B/C and their original source power equation determine the whole
normal form. Perturbation coefficients and their exact original power triangle
are internally produced. The SAME original generated line is retained.
No matching certificate, pair closedness, or ampleness is assumed or asserted.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.MonoidalCategory
open Scheme.Modules Scheme.IdealSheafData
universe u

namespace EnvelopeProperty.Vanishing.RelativeNadelCoverNumeratorPower
open CanonicalGeometry Char0 RelativeNadelCoverWeightedExceptional
open RelativeNadelCoverWeightedExceptionalRounding
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

/-- The SAME actual numerator has its whole original power normal form.
Original M/B/C and source equation are retained; actual perturbation and
coefficient matching are derived internally, without positivity certificates. -/
theorem exists_perturbed_numerator_powerIso (w : Fin (S).length → ℕ)
    (q : ℚ) (hq : 0 ≤ q) (lowerBound : ℕ)
    (M B C : X.Modules) (d t : ℕ) (hdt : (d : ℚ) * q = (t : ℚ))
    (e₀ : bundleTensorPower M d ≅ C ⊗ bundleTensorPower B t) :
    ∃ (N a : ℕ)
      (hK : ((I.comap (S).composite) ^ a * weightedIdeal f n I hI w).IsIdealOfSncDivisor),
      0 < N ∧ lowerBound ≤ N ∧ q.den ∣ N ∧ a * q.den = q.num.toNat * N ∧
      a * d = t * N ∧
      RoundedSncIdealSheaf.rounded
          ((I.comap (S).composite) ^ a * weightedIdeal f n I hI w) hK
          ((1 : ℚ) / (N : ℚ)) =
        RoundedSncIdealSheaf.rounded (I.comap (S).composite)
          (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q ∧
      Nonempty (bundleTensorPower
          ((pullback (S).composite).obj (bundleTensorPower M N) ⊗
            ((I.comap (S).composite) ^ a * weightedIdeal f n I hI w).toModules) d ≅
        (bundleTensorPower (weightedIdeal f n I hI w).toModules d ⊗
          (pullback (S).composite).obj (bundleTensorPower C N)) ⊗
          bundleTensorPower ((I.comap (S).composite).toModules ⊗
            (pullback (S).composite).obj B) (a * d)) := by
  obtain ⟨N, a, hK, hN, hbound, hden, ha, hround⟩ :=
    exists_rounding_preserving_perturbation_ge f n I hI w q hq lowerBound
  have hnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hcast : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum
  have hqRat : q = (q.num.toNat : ℚ) / (q.den : ℚ) := by
    rw [hcast]
    exact q.num_div_den.symm
  have haRat : (a : ℚ) * (q.den : ℚ) = (q.num.toNat : ℚ) * (N : ℚ) := by exact_mod_cast ha
  have hdRat : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have haCoeff : (a : ℚ) = q * (N : ℚ) := by
    rw [hqRat, div_mul_eq_mul_div]
    exact (eq_div_iff hdRat).mpr haRat
  have hcoeff : a * d = t * N := by
    have hh : (a : ℚ) * (d : ℚ) = (t : ℚ) * (N : ℚ) := by
      calc
        (a : ℚ) * (d : ℚ) = (q * (N : ℚ)) * (d : ℚ) := by rw [haCoeff]
        _ = ((d : ℚ) * q) * (N : ℚ) := by ring
        _ = (t : ℚ) * (N : ℚ) := by rw [hdt]
    exact_mod_cast hh
  let μ := (S).composite
  let P := pullback μ
  let J := I.comap μ
  let E := weightedIdeal f n I hI w
  let K := J ^ a * E
  let g := μ ≫ f
  let : SmoothOfRelativeDimension n g :=
    NadelRelativePrincipalization.stage_smoothOfRelativeDimension f n I hI (Fin.last _)
  let : Smooth g := SmoothOfRelativeDimension.smooth n g
  have hJ : J.IsInvertible :=
    (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI).isInvertible g
  let eK : K.toModules ≅ bundleTensorPower J.toModules a ⊗ E.toModules :=
    (NadelBlowupCanonicalIdealProduct.tensorProductIso (J ^ a) (isInvertible_pow hJ a) E).symm ≪≫
      (ModularCurves.monoidalTensorObjIso (J ^ a).toModules E.toModules).symm ≪≫
        ((NadelBlowupCanonicalIdealPowers.tensorPowerIso J hJ a).symm ⊗ᵢ Iso.refl _)
  let eKPower : bundleTensorPower K.toModules d ≅
      bundleTensorPower J.toModules (a * d) ⊗ bundleTensorPower E.toModules d :=
    BundleTensorPowerPullback.powerIso eK d ≪≫
      BundleTensorPowerTensor.powerTensorIso (bundleTensorPower J.toModules a) E.toModules d ≪≫
        (BundleTensorPowerPullback.powerMulIso J.toModules a d ⊗ᵢ Iso.refl _)
  let eSource : bundleTensorPower (P.obj (bundleTensorPower M N)) d ≅
      P.obj (bundleTensorPower C N) ⊗ bundleTensorPower (P.obj B) (a * d) :=
    (BundleTensorPowerPullback.pullbackIso μ (bundleTensorPower M N) d).symm ≪≫
      P.mapIso (BundleTensorPowerPullback.powerMulIso M N d) ≪≫
      P.mapIso (eqToIso (congrArg (bundleTensorPower M) (Nat.mul_comm N d))) ≪≫
      P.mapIso (BundleTensorPowerPullback.powerMulIso M d N).symm ≪≫
      P.mapIso (BundleTensorPowerPullback.powerIso e₀ N) ≪≫
      P.mapIso (BundleTensorPowerTensor.powerTensorIso C (bundleTensorPower B t) N) ≪≫
      (Functor.Monoidal.μIso P (bundleTensorPower C N)
        (bundleTensorPower (bundleTensorPower B t) N)).symm ≪≫
      (Iso.refl _ ⊗ᵢ
        (P.mapIso (BundleTensorPowerPullback.powerMulIso B t N) ≪≫
          P.mapIso (eqToIso (congrArg (bundleTensorPower B) hcoeff.symm)) ≪≫
          BundleTensorPowerPullback.pullbackIso μ B (a * d)))
  let CN := P.obj (bundleTensorPower C N)
  let Bd := bundleTensorPower (P.obj B) (a * d)
  let Jd := bundleTensorPower J.toModules (a * d)
  let Ed := bundleTensorPower E.toModules d
  let interchange : (CN ⊗ Bd) ⊗ (Ed ⊗ Jd) ≅ (CN ⊗ Ed) ⊗ (Bd ⊗ Jd) :=
    { hom := tensorμ CN Bd Ed Jd
      inv := tensorδ CN Bd Ed Jd
      hom_inv_id := tensorμ_tensorδ CN Bd Ed Jd
      inv_hom_id := tensorδ_tensorμ CN Bd Ed Jd }
  let eWhole : bundleTensorPower (P.obj (bundleTensorPower M N) ⊗ K.toModules) d ≅
      (Ed ⊗ CN) ⊗ bundleTensorPower (J.toModules ⊗ P.obj B) (a * d) :=
    BundleTensorPowerTensor.powerTensorIso (P.obj (bundleTensorPower M N)) K.toModules d ≪≫
      (eSource ⊗ᵢ eKPower) ≪≫
      (Iso.refl (CN ⊗ Bd) ⊗ᵢ β_ Jd Ed) ≪≫ interchange ≪≫
      (β_ CN Ed ⊗ᵢ β_ Bd Jd) ≪≫
      (Iso.refl (Ed ⊗ CN) ⊗ᵢ (BundleTensorPowerTensor.powerTensorIso J.toModules (P.obj B) (a * d)).symm)
  exact ⟨N, a, hK, hN, hbound, hden, ha, hcoeff, hround, ⟨eWhole⟩⟩

end EnvelopeProperty.Vanishing.RelativeNadelCoverNumeratorPower
