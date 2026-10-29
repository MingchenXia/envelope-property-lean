import EnvelopeProperty.Vanishing.RelativeNadelAuxiliaryFamily
import EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsAmple
import EnvelopeProperty.Vanishing.NadelGlobalAdaptedModelGeometry

/-! # Actual whole relative ample auxiliary root-cover geometry

The original relatively ample seed supplies the auxiliary exponents.  Actual
nonproper Bertini supplies the original sections, and their entire original
normalized cover is finite flat and smooth over k, while staying projective
over the SAME arbitrary R.  No cover or positivity certificate is supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelCoverGeometry
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
  NadelAuxiliaryBranchSectionsAmple

/-- The actual original ample/SNC geometry produces the entire finite flat
smooth normalization of its original sections.  The original base R may have
zero divisors; field-properness is unnecessary and no component is selected. -/
theorem exists_original_finite_flat_smooth_projective
    {X : Scheme.{u}} [IsIntegral X] {k R : Type u}
    [Field k] [CharZero k] [CommRing R]
    (p : X ⟶ Spec (.of k)) [FiniteType p] (π : X ⟶ Spec (.of R))
    (n : ℕ) [SmoothOfRelativeDimension n p]
    (F : X.DivisorFamily) (hF : F.IsSnc)
    (H : X.Modules) (hH : SchemeLineAmpleness.IsAmple π H)
    (m : F.ι → ℕ) (hm : ∀ i, 0 < m i) :
    ∃ r : ℕ, 0 < r ∧ SchemeLineAmpleness.IsVeryAmple π (bundleTensorPower H r) ∧
      ∃ σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
        tensorObj (bundleTensorPower (bundleTensorPower H r) (m i)) (F.component i).toModules),
      (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
        (fun i j => componentSectionIdeal p n F hF H hH.isInvertible r m i (σ i j))).IsSnc ∧
      (∀ i, (⨆ j, componentSectionIdeal p n F hF H hH.isInvertible r m i (σ i j)) = ⊤) ∧
      IsFinite (normalizedToOriginal
        (OriginalData.data F n (fun _ => bundleTensorPower H r) m σ)) ∧
      Flat (normalizedToOriginal
        (OriginalData.data F n (fun _ => bundleTensorPower H r) m σ)) ∧
      SmoothOfRelativeDimension n (normalizedToOriginal
        (OriginalData.data F n (fun _ => bundleTensorPower H r) m σ) ≫ p) ∧
      Alterations.IsProjectiveOver (normalizedToOriginal
        (OriginalData.data F n (fun _ => bundleTensorPower H r) m σ) ≫ π) := by
  obtain ⟨r, hr, hV, hAux⟩ :=
    NadelAuxiliaryPositivity.exists_uniform_auxiliary_power_tensorObj π H hH
      (fun i => (F.component i).toModules)
      (fun i => (component_isInvertible p n F hF i).isInvertibleModule_toModules) m hm
  obtain ⟨σ, _hC, hG, hRows⟩ := RelativeNadelAuxiliaryFamily.exists_veryAmple_auxiliary_family
    p π n F hF
    (fun i => tensorObj (bundleTensorPower (bundleTensorPower H r) (m i))
      (F.component i).toModules) hAux
  have hbase : Alterations.IsProjectiveOver π := by
    obtain ⟨a, _ha, d, i, hi, hip, _e⟩ := hH.2
    exact ⟨d, i, hi, hip⟩
  have hfield (i : F.ι) : IsUnit (m i : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hm i)))
  obtain ⟨hfinite, hflat, hsmooth⟩ := NadelGlobalAdaptedModel.finite_flat_smooth
    F n (fun _ => bundleTensorPower H r) m σ
    (fun _ => TensorPowerBaseIdealGrading.tensorPower_isInvertible hH.isInvertible r)
    (component_isInvertible p n F hF) p hG hRows hm hfield
  let : IsFinite (normalizedToOriginal
    (OriginalData.data F n (fun _ => bundleTensorPower H r) m σ)) := hfinite
  exact ⟨r, hr, hV, σ, hG, hRows, hfinite, hflat, hsmooth,
    Alterations.Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite π hbase
      (normalizedToOriginal (OriginalData.data F n (fun _ => bundleTensorPower H r) m σ))⟩

end EnvelopeProperty.Vanishing.RelativeNadelCoverGeometry
