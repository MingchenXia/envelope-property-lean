import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionSchemeDimension
import EnvelopeProperty.AlgGeom.IntegralSchemeDimension
import EnvelopeProperty.AlgGeom.FiniteSchemeNormalization
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Whole dimension under the actual finite dominant normalization projection

Original section maps are internally integral and injective. Genuine going-up
and incomparability compare SAME coordinate dimensions. The actual original
normalization projection supplies finiteness and dominance internally.
-/
noncomputable section
open scoped Classical
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionNormalizationDimension
variable {k : Type u} [Field k] {Y D : Scheme.{u}}

/-- A SAME original finite dominant integral map preserves WHOLE scheme dimension, without a dimension certificate. -/
theorem whole_dimension_eq_of_finite_dominant (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [IsIntegral Y] [IsIntegral D]
    (f : D ⟶ Y) [IsFinite f] [IsDominant f] :
    topologicalKrullDim D = topologicalKrullDim Y := by
  let : Surjective f := surjective_of_isDominant_of_isClosed_range f (by
    simpa only [Set.image_univ] using f.isClosedMap Set.univ isClosed_univ)
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  let : Nonempty U := ⟨⟨genericPoint Y, hyU⟩⟩
  obtain ⟨z, hz⟩ := f.surjective (genericPoint Y)
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let : Nonempty V := ⟨⟨z, by change f z ∈ U; rw [hz]; exact hyU⟩⟩
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have hinj : Function.Injective (f.app U).hom := f.app_injective U
  have hint : (f.app U).hom.IsIntegral := f.isIntegral_app U hU
  have hrings : ringKrullDim Γ(D, V) = ringKrullDim Γ(Y, U) :=
    le_antisymm (EnvelopeProperty.ringKrullDim_le_of_isIntegral (f.app U).hom hint)
      (IntegralSchemeDimension.ringKrullDim_le_of_isIntegral_of_injective (f.app U).hom hint hinj)
  calc
    topologicalKrullDim D = ringKrullDim Γ(D, V) :=
      PLGaussVerticalCurveSurfaceSelectionSchemeDimension.whole_dimension_eq_affine (f ≫ p) hV
    _ = ringKrullDim Γ(Y, U) := hrings
    _ = topologicalKrullDim Y :=
      (PLGaussVerticalCurveSurfaceSelectionSchemeDimension.whole_dimension_eq_affine p hU).symm

/-- The SAME actual original generic-field normalization preserves WHOLE dimension; its projection data are internally derived. -/
theorem normalization_dimension_eq (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [IsIntegral Y] :
    topologicalKrullDim (IntegralSchemeNormalization.normalization Y) = topologicalKrullDim Y := by
  let : IsIntegral (IntegralSchemeNormalization.normalization Y) := inferInstance
  let : IsFinite (IntegralSchemeNormalization.projection Y) :=
    IntegralSchemeNormalization.projection_isFinite k Y p
  let : IsDominant (IntegralSchemeNormalization.projection Y) :=
    ⟨(IntegralSchemeNormalization.projection_surjective Y).denseRange⟩
  exact whole_dimension_eq_of_finite_dominant p (IntegralSchemeNormalization.projection Y)

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionNormalizationDimension
