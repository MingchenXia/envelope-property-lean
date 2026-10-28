import EnvelopeProperty.Vanishing.NadelGlobalAdaptedModelAlgebra
import DeJongAlterations.Geometry.FiniteProjectivePreservation

/-! # Actual whole normalized adapted geometry over the original field

The actual finite-flat/same-dimension theorem of the original section producer
is combined with the native finite-projective preservation theorem.  Every
scheme is the original whole relative normalization, including all components.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedModel
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization

variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k] [PerfectField k]
  (F : X.DivisorFamily) (n : ℕ) (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
    tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)

/-- The actual ENTIRE original normalized cover is finite flat, has the SAME
original relative dimension, and is projective over the SAME original field.
Projectivity of the original base is the only projectivity input. -/
theorem finite_flat_smooth_projective
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hf : DeJongAlterations.IsProjectiveOver f)
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k)) :
    IsFinite (normalizedToOriginal (OriginalData.data F n L m σ)) ∧
      Flat (normalizedToOriginal (OriginalData.data F n L m σ)) ∧
      SmoothOfRelativeDimension n (normalizedToOriginal (OriginalData.data F n L m σ) ≫ f) ∧
      DeJongAlterations.IsProjectiveOver
        (normalizedToOriginal (OriginalData.data F n L m σ) ≫ f) := by
  obtain ⟨hfinite, hflat, hsmooth⟩ := finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield
  let : IsFinite (normalizedToOriginal (OriginalData.data F n L m σ)) := hfinite
  exact ⟨hfinite, hflat, hsmooth,
    DeJongAlterations.Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite f hf
      (normalizedToOriginal (OriginalData.data F n L m σ))⟩

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedModel
