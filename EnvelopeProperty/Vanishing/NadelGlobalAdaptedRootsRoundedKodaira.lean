import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRoundedLine
import EnvelopeProperty.Vanishing.NadelGlobalAdaptedModelGeometry
import EnvelopeProperty.Vanishing.NadelFiniteRootKodaira

/-! # Kodaira cohomology of the same actual rounded line on the whole cover

The common denominator, finite smooth original cover, and actual power
isomorphism are all produced internally. The ample premise concerns only the
actual original cleared base line, not a vanishing group or cover certificate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
open scoped BigOperators
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization

/-- A definite common degree computed from ALL original positive degrees. -/
def commonRootDegree {X : Scheme.{u}} (F : X.DivisorFamily) (m : F.ι → ℕ) : ℕ :=
  ∏ i, m i

/-- The computed common degree is positive, including the empty family. -/
theorem commonRootDegree_pos {X : Scheme.{u}} (F : X.DivisorFamily)
    (m : F.ι → ℕ) (hm : ∀ i, 0 < m i) : 0 < commonRootDegree F m := by
  unfold commonRootDegree
  exact Finset.prod_pos (fun i _ => hm i)

/-- Every original degree divides this SAME internally computed degree. -/
theorem commonRootDegree_dvd {X : Scheme.{u}} (F : X.DivisorFamily)
    (m : F.ι → ℕ) (i : F.ι) : m i ∣ commonRootDegree F m :=
  Finset.dvd_prod_of_mem m (Finset.mem_univ i)

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
  (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
    tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
  {k : Type u} [Field k] [CharZero k]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
  (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
    (OriginalData.ideals F n L m σ hL hD)).IsSnc)
  (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
  (hm : ∀ i, 0 < m i)

include hD f hG hRows hm

/-- Original geometry INTERNALLY produces ampleness of the actual rounded
line from the actual ample cleared base line. No cover certificate is supplied. -/
theorem wholeRoundedLine_isAmple (M : X.Modules) (hM : IsInvertible M)
    (a : F.ι → ℕ)
    (hA : SchemeLineAmpleness.IsAmple f
      (tensorObj (bundleTensorPower M (commonRootDegree F m))
        (clearedRoundedIdeal F m a (commonRootDegree F m)).toModules)) :
    SchemeLineAmpleness.IsAmple
      (normalizedToOriginal (OriginalData.data F n L m σ) ≫ f)
      (wholeRoundedLine F n L m σ hL M a) := by
  have hfield (i : F.ι) : IsUnit (m i : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hm i)))
  obtain ⟨hfinite, _hflat, _hsmooth⟩ := NadelGlobalAdaptedModel.finite_flat_smooth
    F n L m σ hL hD f hG hRows hm hfield
  let : IsFinite (normalizedToOriginal (OriginalData.data F n L m σ)) := hfinite
  exact NadelFiniteRootKodaira.isAmple_of_finite_power f _ hA _ _
    (wholeRoundedLine_isInvertible F n L m σ hL hD f hG hRows hm hfield M hM a)
    (commonRootDegree F m) (commonRootDegree_pos F m hm)
    (wholeRoundedLinePowerIso F n L m σ hL hD f hG hRows hm hfield M a
      (commonRootDegree F m) (commonRootDegree_dvd F m))

/-- The same original actual rounded cover line has zero positive canonical
cohomology, by the proved DI-based characteristic-zero Kodaira theorem. -/
theorem wholeRoundedLine_kodaira (M : X.Modules) (hM : IsInvertible M)
    (a : F.ι → ℕ)
    (hA : SchemeLineAmpleness.IsAmple f
      (tensorObj (bundleTensorPower M (commonRootDegree F m))
        (clearedRoundedIdeal F m a (commonRootDegree F m)).toModules)) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (tensorObj
        (canonicalLineSheaf (normalizedToOriginal (OriginalData.data F n L m σ) ≫ f) n)
        (wholeRoundedLine F n L m σ hL M a)).sheaf (q + 1)) := by
  have hfield (i : F.ι) : IsUnit (m i : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hm i)))
  obtain ⟨_hfinite, _hflat, hsmooth⟩ := NadelGlobalAdaptedModel.finite_flat_smooth
    F n L m σ hL hD f hG hRows hm hfield
  let : SmoothOfRelativeDimension n
      (normalizedToOriginal (OriginalData.data F n L m σ) ≫ f) := hsmooth
  exact KodairaCharacteristicZero.kodaira_tensorObj _ n _
    (wholeRoundedLine_isAmple F n L m σ hL hD f hG hRows hm M hM a hA) q

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
