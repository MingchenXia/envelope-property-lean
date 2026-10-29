/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.GaussScalarLifts
import EnvelopeProperty.Berkovich.SchemeScalarBaseChangeGlobal

/-!
# Whole-scheme lifts to the actual original completed Gauss field

Actual original affine Spec charts and their genuine whole coefficient maps
construct a point of the literal scalar scheme pullback over every original
native point. All comparisons preserve the entire point, not only support.
-/

open scoped Classical NNReal TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeScalarBaseChange
variable {R : Type u} [CommRing R] (v : Valuation R ℝ≥0) (r : ℝ≥0)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every whole native point of any actual scheme lifts to its literal scalar
pullback by the completed residue field of the actual original Gauss point.
The affine chart, exact coefficient map and entire lifted point are constructed. -/
theorem nativeMap_surjective_gauss :
    Function.Surjective (nativeMap (RelativeSpectrum.fcGaussField_val_algebraMap v r) f) := by
  intro x
  let 𝒰 := X.affineOpenCover
  obtain ⟨i, p, hp⟩ := 𝒰.openCover.exists_eq x.1.point
  let φ : R →+* 𝒰.X i := (Scheme.Spec.preimage (𝒰.f i ≫ f)).unop.hom
  let : Algebra R (𝒰.X i) := φ.toAlgebra
  have hg : 𝒰.f i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (𝒰.X i))) :=
    (Scheme.Spec.map_preimage (𝒰.f i ≫ f)).symm
  have hx : x ∈ Set.range (RelativeSchemeValuedPoint.map (v := v) (𝒰.f i) hg) := by
    rw [RelativeSchemeValuedPoint.range_map_of_isOpenImmersion]
    exact ⟨p, hp⟩
  obtain ⟨z, hz⟩ := hx
  let zA := RelativeSchemeValuedPoint.affineSpectrumHomeomorph z
  let y := (affineTensorHomeomorph (S := RelativeSpectrum.fcGaussField v r)).symm
    (RelativeSpectrum.fcGaussScalarLift v r zA)
  let j : model (S := RelativeSpectrum.fcGaussField v r)
      (Spec.map (CommRingCat.ofHom (algebraMap R (𝒰.X i)))) ⟶
      model (S := RelativeSpectrum.fcGaussField v r) f :=
    pullback.map _ _ _ _ (𝒰.f i) (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using hg.symm) (by simp)
  have hjs : j ≫ structureMap (S := RelativeSpectrum.fcGaussField v r) f =
      structureMap (S := RelativeSpectrum.fcGaussField v r)
        (Spec.map (CommRingCat.ofHom (algebraMap R (𝒰.X i)))) := by
    simp [j, structureMap, pullback.map]
  have hjp : j ≫ projection (S := RelativeSpectrum.fcGaussField v r) f =
      projection (S := RelativeSpectrum.fcGaussField v r)
        (Spec.map (CommRingCat.ofHom (algebraMap R (𝒰.X i)))) ≫ 𝒰.f i := by
    simp [j, projection, pullback.map]
  have hy : nativeMap (RelativeSpectrum.fcGaussField_val_algebraMap v r)
      (Spec.map (CommRingCat.ofHom (algebraMap R (𝒰.X i)))) y = z := by
    apply RelativeSchemeValuedPoint.affineSpectrumHomeomorph.injective
    rw [affineTensorHomeomorph_nativeMap]
    change RelativeSpectrum.baseChangeRestriction
      (RelativeSpectrum.fcGaussField_val_algebraMap v r)
      (affineTensorHomeomorph ((affineTensorHomeomorph).symm
        (RelativeSpectrum.fcGaussScalarLift v r zA))) = zA
    rw [Homeomorph.apply_symm_apply]
    exact RelativeSpectrum.fcGaussScalarLift_baseChangeRestriction v r zA
  refine ⟨RelativeSchemeValuedPoint.map j hjs y, ?_⟩
  have hc : nativeMap (RelativeSpectrum.fcGaussField_val_algebraMap v r) f
      (RelativeSchemeValuedPoint.map j hjs y) =
      RelativeSchemeValuedPoint.map (v := v) (𝒰.f i) hg
        (nativeMap (RelativeSpectrum.fcGaussField_val_algebraMap v r)
          (Spec.map (CommRingCat.ofHom (algebraMap R (𝒰.X i)))) y) := by
    apply Subtype.ext
    change SchemeValuedPoint.map (projection f) (SchemeValuedPoint.map j y.1) =
      SchemeValuedPoint.map (𝒰.f i) (SchemeValuedPoint.map (projection _) y.1)
    rw [← SchemeValuedPoint.map_comp, hjp, SchemeValuedPoint.map_comp]
  exact hc.trans ((congrArg (RelativeSchemeValuedPoint.map (v := v) (𝒰.f i) hg) hy).trans hz)

end EnvelopeProperty.Berkovich.SchemeScalarBaseChange
