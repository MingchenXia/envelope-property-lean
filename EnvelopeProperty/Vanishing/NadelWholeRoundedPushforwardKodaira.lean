import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRoundedKodaira
import EnvelopeProperty.AlgGeom.AffinePushforwardCohomology
import ModularCurves.ForMathlib.FiniteAffineOpenCover

/-! # Actual positive vanishing of the whole rounded canonical pushforward

Original ampleness and geometry internally supply the cover, finiteness,
smoothness and quasicoherence. No trace or cohomology-vanishing certificate
is an input.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelWholeRoundedPushforwardKodaira
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules TopologicalSpace
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedRoots
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)

include hD f hG hRows hm
/-- Positive cohomology of the SAME entire rounded canonical pushforward
vanishes from the original ample cleared line and original geometry. -/
theorem wholeRoundedCanonicalPushforward_kodaira (M : X.Modules) (hM : IsInvertible M)
    (a : F.ι → ℕ)
    (hA : SchemeLineAmpleness.IsAmple f
      (tensorObj (bundleTensorPower M (commonRootDegree F m))
        (clearedRoundedIdeal F m a (commonRootDegree F m)).toModules)) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((pushforward π).obj
        (tensorObj (canonicalLineSheaf (π ≫ f) n)
          (wholeRoundedLine F n L m σ hL M a))).sheaf (q + 1)) := by
  have hfield (i : F.ι) : IsUnit (m i : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hm i)))
  obtain ⟨hfinite, _hflat, hsmooth⟩ := NadelGlobalAdaptedModel.finite_flat_smooth
    F n L m σ hL hD f hG hRows hm hfield
  let : IsFinite π := hfinite
  let : SmoothOfRelativeDimension n (π ≫ f) := hsmooth
  let N := tensorObj (canonicalLineSheaf (π ≫ f) n) (wholeRoundedLine F n L m σ hL M a)
  have hN : IsInvertible N :=
    (canonicalLineSheaf_isInvertible (π ≫ f) n).tensorObj
      (wholeRoundedLine_isInvertible F n L m σ hL hD f hG hRows hm hfield M hM a)
  let : N.IsQuasicoherent := hN.isQuasicoherent
  let : IsProper f := hA.isProjectiveFactorization.isProper
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨ι, hι, U, hU, hUa⟩ := X.exists_finite_affine_openCover
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let : LinearOrder ι :=
    LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact (AffinePushforwardCohomology.subsingleton_H_iff_pushforward π f N U hU hUa q).mp
    (wholeRoundedLine_kodaira F n L m σ hL hD f hG hRows hm M hM a hA q)

end EnvelopeProperty.Vanishing.NadelWholeRoundedPushforwardKodaira
