import EnvelopeProperty.AlgGeom.SchemeGlobalSectionTensorPowerNorms
import EnvelopeProperty.AlgGeom.SchemeGlobalSectionNormDetection
import EnvelopeProperty.AlgGeom.BundleTensorPowerTensor

/-! # Actual original tensor sections retain true norms and genuine nonvanishing -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open Scheme.Modules
open scoped Classical NNReal
noncomputable section
universe u
namespace EnvelopeProperty.SchemeGlobalSectionTensorProductNorms
open CanonicalGeometry SchemeGlobalSectionModelNormIsometries SchemeTensorSectionHoms
open SchemeGlobalSectionTensorPowerNorms Berkovich RelativeSchemeValuedPoint
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {p : X ⟶ Spec (.of R)} [IsProper p]
  (hb : ∀ r,v r ≤ 1) (y : RelativeSchemeValuedPoint v p)

/-- The TRUE original proper-model norm multiplies for every actual whole tensor section. -/
theorem globalSectionNorm_tensorSection (M N : X.Modules)
    (hM : IsInvertible M) (hN : IsInvertible N) (s : Γ(M,⊤)) (t : Γ(N,⊤)) :
    globalSectionNorm hb y (M ⊗ N) (hM.monoidalTensor hN)
      (ModularCurves.tensorSection M N ⊤ s t) =
        globalSectionNorm hb y M hM s * globalSectionNorm hb y N hN t := by
  simp only [globalSectionNorm,modelLineNorm_fibreSection]
  rw [← tensorSectionHom_sectionHom]
  exact modelHomNorm_tensorSectionHom hb y hM hN
    (SchemeModuleGlobalSections.sectionHom M s) (SchemeModuleGlobalSections.sectionHom N t)

/-- Two actual original power sections multiply into the SAME actual tensor-product line power. -/
def powerTensorSection (M N : X.Modules) (d : ℕ)
    (s : Γ(bundleTensorPower M d,⊤)) (t : Γ(bundleTensorPower N d,⊤)) :
    Γ(bundleTensorPower (M ⊗ N) d,⊤) :=
  SchemeModuleIsoGlobalSections.moduleIsoTopEquiv
    (BundleTensorPowerTensor.powerTensorIso M N d).symm
      (ModularCurves.tensorSection (bundleTensorPower M d) (bundleTensorPower N d) ⊤ s t)

/-- Actual whole tensor-power section products have EXACT original factor norms at every native point. -/
theorem globalSectionNorm_powerTensorSection (M N : X.Modules)
    (hM : IsInvertible M) (hN : IsInvertible N) (d : ℕ)
    (s : Γ(bundleTensorPower M d,⊤)) (t : Γ(bundleTensorPower N d,⊤)) :
    globalSectionNorm hb y (bundleTensorPower (M ⊗ N) d)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible (hM.monoidalTensor hN) d)
      (powerTensorSection M N d s t) =
        globalSectionNorm hb y (bundleTensorPower M d)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM d) s *
        globalSectionNorm hb y (bundleTensorPower N d)
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN d) t := by
  unfold powerTensorSection
  rw [← globalSectionNorm_moduleIso hb y
    ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hM d).monoidalTensor
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN d))
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible (hM.monoidalTensor hN) d)
    (BundleTensorPowerTensor.powerTensorIso M N d).symm]
  exact globalSectionNorm_tensorSection hb y _ _ _ _ s t

section Integral
variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (q : Y ⟶ Spec (.of k)) [IsProper q]

include q in
/-- Actual original nonzero whole sections have a nonzero actual whole tensor product,
derived from the SAME genuine native generic point, without a nonvanishing certificate. -/
theorem tensorSection_eq_zero_iff (M N : Y.Modules)
    (hM : IsInvertible M) (hN : IsInvertible N) (s : Γ(M,⊤)) (t : Γ(N,⊤)) :
    ModularCurves.tensorSection M N ⊤ s t = 0 ↔ s = 0 ∨ t = 0 := by
  constructor
  · intro hz
    by_contra h
    have hs : s ≠ 0 := fun hs => h (Or.inl hs)
    have ht : t ≠ 0 := fun ht => h (Or.inr ht)
    have he := globalSectionNorm_tensorSection Valuation.one_apply_le_one
      (SchemeGlobalSectionNormDetection.trivialPoint q (genericPoint Y)) M N hM hN s t
    rw [hz,SchemeGlobalSectionNormDetection.globalSectionNorm_zero,
      SchemeGlobalSectionNormDetection.globalSectionNorm_trivialGenericPoint_eq_one q M hM s hs,
      SchemeGlobalSectionNormDetection.globalSectionNorm_trivialGenericPoint_eq_one q N hN t ht] at he
    exact zero_ne_one (by simpa only [one_mul] using he)
  · intro hz
    apply (SchemeGlobalSectionNormDetection.eq_zero_iff_forall_globalSectionNorm_eq_zero q
      (M ⊗ N) (hM.monoidalTensor hN) _).mpr
    intro z
    rw [globalSectionNorm_tensorSection Valuation.one_apply_le_one z M N hM hN]
    rcases hz with hs | ht
    · rw [hs,SchemeGlobalSectionNormDetection.globalSectionNorm_zero,zero_mul]
    · rw [ht,SchemeGlobalSectionNormDetection.globalSectionNorm_zero,mul_zero]

include q in
/-- The original tensor-power product vanishes EXACTLY when an original factor section vanishes. -/
theorem powerTensorSection_eq_zero_iff (M N : Y.Modules)
    (hM : IsInvertible M) (hN : IsInvertible N) (d : ℕ)
    (s : Γ(bundleTensorPower M d,⊤)) (t : Γ(bundleTensorPower N d,⊤)) :
    powerTensorSection M N d s t = 0 ↔ s = 0 ∨ t = 0 := by
  have hn := tensorSection_eq_zero_iff q (bundleTensorPower M d) (bundleTensorPower N d)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM d)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN d) s t
  constructor
  · intro hz
    apply hn.mp
    apply (SchemeGlobalSectionNormDetection.eq_zero_iff_forall_globalSectionNorm_eq_zero q _
      ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hM d).monoidalTensor
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN d)) _).mpr
    intro z
    rw [globalSectionNorm_tensorSection Valuation.one_apply_le_one z _ _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM d)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN d)]
    rw [← globalSectionNorm_powerTensorSection Valuation.one_apply_le_one z M N hM hN d s t,
      hz,SchemeGlobalSectionNormDetection.globalSectionNorm_zero]
  · intro hz
    apply (SchemeGlobalSectionNormDetection.eq_zero_iff_forall_globalSectionNorm_eq_zero q _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible (hM.monoidalTensor hN) d) _).mpr
    intro z
    rw [globalSectionNorm_powerTensorSection Valuation.one_apply_le_one z M N hM hN d s t,
      ← globalSectionNorm_tensorSection Valuation.one_apply_le_one z _ _
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM d)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN d)]
    rw [hn.mpr hz,SchemeGlobalSectionNormDetection.globalSectionNorm_zero]
end Integral
end EnvelopeProperty.SchemeGlobalSectionTensorProductNorms
