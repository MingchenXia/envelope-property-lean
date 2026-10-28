import EnvelopeProperty.Char0.NativeStalkCompletion
import SGPT.Okounkov.SchemeNativeFormalGerm
import Hironaka.Algebra.Local.PowerSeriesEndomorphism
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Canonical completions of the actual original formal coefficient maps -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeFormalCompletion

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter Set
open SGPT.Okounkov TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open HironakaActualFormalCoordinatePowerDivision

/-- The actual formal coefficient ring is complete for its genuine maximal ideal. -/
theorem formalSeries_complete (n : ℕ) :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) ℂ))
      (MvPowerSeries (Fin n) ℂ) := by
  rw [MvPowerSeries.maximalIdeal_eq_span_range_X]
  infer_instance

/-- The inverse of the CANONICAL completion map of the actual formal series ring. -/
def formalCompletionEquiv (n : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) ℂ))
      (MvPowerSeries (Fin n) ℂ) ≃+* MvPowerSeries (Fin n) ℂ :=
  (RingEquiv.ofBijective (algebraMap (MvPowerSeries (Fin n) ℂ)
    (AdicCompletion (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) ℂ))
      (MvPowerSeries (Fin n) ℂ))) (by
        change Function.Bijective (AdicCompletion.of _ _)
        exact AdicCompletion.of_bijective_iff.mpr (formalSeries_complete n))).symm

/-- Every ENTIRE original series retains itself under the canonical completion inverse. -/
theorem formalCompletionEquiv_algebraMap (n : ℕ) (s : MvPowerSeries (Fin n) ℂ) :
    formalCompletionEquiv n (algebraMap _ _ s) = s :=
  RingEquiv.symm_apply_apply _ s

section Native

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] (p : M)

/-- Localness of the actual native Taylor map follows from its actual constant coefficient. -/
instance nativeTaylor_isLocalHom : IsLocalHom (NativeHolGerm.taylor (n := n) p) where
  map_nonunit g hg := by
    apply (NativeHolGerm.isUnit_iff_eval_ne_zero g).mpr
    have hc := (MvPowerSeries.isUnit_iff_constantCoeff.mp hg).ne_zero
    rwa [NativeHolGerm.taylor_constantCoeff] at hc

/-- The WHOLE actual native maximal ideal generates the whole actual formal maximal ideal. -/
theorem nativeTaylor_map_maximalIdeal :
    (IsLocalRing.maximalIdeal (NativeHolGerm n M p)).map (NativeHolGerm.taylor p) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) ℂ) := by
  rw [NativeHolGerm.taylor_map_maximalIdeal]
  simpa [actualFormalCoordinateIdeal] using
    (MvPowerSeries.maximalIdeal_eq_span_range_X (Fin n) ℂ).symm

/-- Actual original constant germs supply every residue class in the formal coefficient ring. -/
theorem nativeTaylor_residue_bijective :
    Function.Bijective (IsLocalRing.ResidueField.map (NativeHolGerm.taylor (n := n) p)) := by
  refine ⟨(IsLocalRing.ResidueField.map (NativeHolGerm.taylor (n := n) p)).injective, ?_⟩
  intro y
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨IsLocalRing.residue _ (NativeHolGerm.constHom (MvPowerSeries.constantCoeff s)), ?_⟩
  rw [IsLocalRing.ResidueField.map_residue, NativeHolGerm.taylor_const]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal_mvPowerSeries_iff, map_sub,
    MvPowerSeries.constantCoeff_C, sub_self]

/-- The CANONICAL completed actual Taylor map is bijective, with no completion certificate. -/
theorem nativeTaylor_completionMap_bijective :
    Function.Bijective (IsLocalRing.completionMap (NativeHolGerm.taylor (n := n) p)) := by
  let : Algebra (NativeHolGerm n M p) (MvPowerSeries (Fin n) ℂ) :=
    (NativeHolGerm.taylor p).toAlgebra
  let : Module.FaithfullyFlat (NativeHolGerm n M p) (MvPowerSeries (Fin n) ℂ) :=
    NativeHolGerm.taylor_faithfullyFlat p
  exact IsLocalRing.bijective_completionMap_of_flat_of_map_maximalIdeal
    (NativeHolGerm.taylor p)
    (inferInstance : Module.Flat (NativeHolGerm n M p) (MvPowerSeries (Fin n) ℂ))
    (nativeTaylor_map_maximalIdeal p)
    (nativeTaylor_residue_bijective p)

end Native

section Scheme

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance formalCompletionPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance formalCompletionPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance formalCompletionPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable (p : SchemeComplexPoint f)

instance originalFormal_isLocalHom : IsLocalHom (schemeNativeFormalGerm f n p) := by
  unfold schemeNativeFormalGerm
  infer_instance

/-- Functoriality retains the SAME original native and actual Taylor maps on completions. -/
theorem originalFormal_completionMap_bijective :
    Function.Bijective (IsLocalRing.completionMap (schemeNativeFormalGerm f n p)) := by
  change Function.Bijective (IsLocalRing.completionMap
    ((NativeHolGerm.taylor p).comp (schemeNativeStalkGerm f n p)))
  rw [IsLocalRing.completionMap_comp]
  exact (nativeTaylor_completionMap_bijective p).comp
    (NativeStalkCompletion.nativeCompletionEquiv f n p).bijective

/-- The original algebraic stalk completion is the actual formal coefficient ring. -/
def originalFormalCompletionEquiv :
    AdicCompletion
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (schemeComplexPointImage f p)))
      (X.presheaf.stalk (schemeComplexPointImage f p)) ≃+* MvPowerSeries (Fin n) ℂ :=
  (RingEquiv.ofBijective (IsLocalRing.completionMap (schemeNativeFormalGerm f n p))
    (originalFormal_completionMap_bijective f n p)).trans (formalCompletionEquiv n)

/-- Every original algebraic coefficient is its SAME actual Taylor series. -/
theorem originalFormalCompletionEquiv_algebraMap
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    originalFormalCompletionEquiv f n p (algebraMap _ _ a) = schemeNativeFormalGerm f n p a := by
  change formalCompletionEquiv n
    (IsLocalRing.completionMap (schemeNativeFormalGerm f n p) (algebraMap _ _ a)) = _
  rw [IsLocalRing.completionMap_algebraMap, formalCompletionEquiv_algebraMap]

/-- The WHOLE original ideal extension has exactly its actual original Taylor extension. -/
theorem originalFormalCompletionEquiv_map_ideal
    (I : Ideal (X.presheaf.stalk (schemeComplexPointImage f p))) :
    (I.map (algebraMap _ (AdicCompletion
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (schemeComplexPointImage f p)))
        (X.presheaf.stalk (schemeComplexPointImage f p))))).map
          (originalFormalCompletionEquiv f n p).toRingHom = I.map (schemeNativeFormalGerm f n p) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext (originalFormalCompletionEquiv_algebraMap f n p)

end Scheme

end EnvelopeProperty.Char0.NativeFormalCompletion
