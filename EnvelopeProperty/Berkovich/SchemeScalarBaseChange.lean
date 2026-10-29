/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeRelativeBaseChange
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas
import EnvelopeProperty.Berkovich.SpectrumBaseChangeProper
import EnvelopeProperty.Berkovich.ExtensionLifts
import EnvelopeProperty.Berkovich.SchemeLocalPSH
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual scheme scalar base change and its affine tensor comparison

The literal scheme pullback, its whole projections and its fixed-coefficient
native map are constructed. On an original affine scheme the actual tensor
scheme comparison identifies this map with the actual scalar restriction.
-/

open scoped Classical NNReal TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeScalarBaseChange
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
    (hw : ∀ r, w (algebraMap R S r) = v r)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal actual coefficient scheme pullback. -/
abbrev model : Scheme.{u} := pullback f (Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- Its whole actual original-scheme projection. -/
abbrev projection : model (S := S) f ⟶ X := pullback.fst _ _

/-- The literal actual new coefficient structure morphism. -/
abbrev structureMap : model (S := S) f ⟶ Spec (CommRingCat.of S) := pullback.snd _ _

/-- The entire genuine coefficient pullback square commutes. -/
theorem projection_comp_structure :
    projection (S := S) f ≫ f =
      structureMap (S := S) f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  pullback.condition

/-- The true scalar base-change map on whole native prescribed-coefficient points. -/
def nativeMap : RelativeSchemeValuedPoint w (structureMap (S := S) f) →
    RelativeSchemeValuedPoint v f :=
  RelativeSchemeValuedPoint.mapOverBase (algebraMap R S) hw
    (projection f) (projection_comp_structure f)

/-- The entire original projection on actual whole native points. -/
theorem nativeMap_coe (y : RelativeSchemeValuedPoint w (structureMap (S := S) f)) :
    (nativeMap hw f y).1 = SchemeValuedPoint.map (projection f) y.1 := rfl

/-- The genuine native scalar restriction is continuous. -/
theorem continuous_nativeMap : Continuous (nativeMap hw f) :=
  RelativeSchemeValuedPoint.continuous_mapOverBase (algebraMap R S) hw _ _

/-- Actual regular-unit local psh presentations pull back through the genuine
scheme scalar map, for arbitrary original coefficient seminorms. -/
theorem isLocallyPSHOn_comp_nativeMap
    {U : Set (RelativeSchemeValuedPoint v f)} {u : RelativeSchemeValuedPoint v f → EReal}
    (hu : RelativeSchemeValuedPoint.IsLocallyPSHOn U u) :
    RelativeSchemeValuedPoint.IsLocallyPSHOn (nativeMap hw f ⁻¹' U)
      (fun y => u (nativeMap hw f y)) :=
  hu.comp_mapOverBase (algebraMap R S) hw (projection f) (projection_comp_structure f)

section Affine
variable {A : Type u} [CommRing A] [Algebra R A]

/-- The actual affine scheme pullback is the literal original tensor-product Spec. -/
def affineTensorIso : model (S := S) (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≅
    Spec (CommRingCat.of (S ⊗[R] A)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso R S A

/-- The actual tensor comparison preserves the whole original A projection. -/
theorem affineTensorIso_hom_projection :
    (affineTensorIso (R := R) (S := S) (A := A)).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom) =
        projection (S := S) (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R S A).hom) ≫ _ = _
  rw [Category.assoc]
  erw [pullbackSpecIso_hom_snd]
  exact pullbackSymmetry_hom_comp_snd _ _

/-- The same actual tensor comparison preserves the whole new coefficient map. -/
theorem affineTensorIso_hom_structure :
    (affineTensorIso (R := R) (S := S) (A := A)).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) =
        structureMap (S := S) (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R S A).hom) ≫ _ = _
  rw [Category.assoc, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]

/-- The actual affine tensor scheme isomorphism preserves the exact whole
coefficient norm, hence gives the genuine prescribed-spectrum homeomorphism. -/
def affineTensorHomeomorph :
    RelativeSchemeValuedPoint w
      (structureMap (S := S) (Spec.map (CommRingCat.ofHom (algebraMap R A)))) ≃ₜ
      RelativeSpectrum w (S ⊗[R] A) :=
  ((SchemeValuedPoint.isoHomeomorph (affineTensorIso (R := R) (S := S) (A := A))).subtype
    (fun y => by
      change (SchemeValuedPoint.map (structureMap (S := S)
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))) y = _) ↔
        (SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))))
          (SchemeValuedPoint.map (affineTensorIso (R := R) (S := S) (A := A)).hom y) = _)
      rw [← SchemeValuedPoint.map_comp, affineTensorIso_hom_structure])).trans
    RelativeSchemeValuedPoint.affineSpectrumHomeomorph

/-- On whole native affine points, the actual scheme scalar map is exactly
the actual tensor scalar restriction. -/
theorem affineTensorHomeomorph_nativeMap
    (y : RelativeSchemeValuedPoint w
      (structureMap (S := S) (Spec.map (CommRingCat.ofHom (algebraMap R A))))) :
    RelativeSchemeValuedPoint.affineSpectrumHomeomorph
      (nativeMap hw (Spec.map (CommRingCat.ofHom (algebraMap R A))) y) =
      RelativeSpectrum.baseChangeRestriction hw (affineTensorHomeomorph y) := by
  apply Subtype.ext
  change SchemeValuedPoint.spectrumHomeomorph
    (SchemeValuedPoint.map (projection (S := S)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) y.1) =
    Spectrum.comap (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom
      (SchemeValuedPoint.spectrumHomeomorph
        (SchemeValuedPoint.map (affineTensorIso (R := R) (S := S) (A := A)).hom y.1))
  rw [← SchemeValuedPoint.spectrumHomeomorph_map, ← SchemeValuedPoint.map_comp,
    affineTensorIso_hom_projection]

/-- True native scalar restriction on the literal affine scheme pullback is
proper, with no coefficient bounds or finite-type/properness assumption. -/
theorem isProperMap_nativeMap_affine :
    IsProperMap (nativeMap hw (Spec.map (CommRingCat.ofHom (algebraMap R A)))) := by
  have h := (RelativeSchemeValuedPoint.affineSpectrumHomeomorph
    (R := R) (A := A) (v := v)).symm.isClosedEmbedding.isProperMap.comp
      ((RelativeSpectrum.isProperMap_baseChangeRestriction (A := A) hw).comp
        (affineTensorHomeomorph (R := R) (S := S) (A := A) (w := w)).isClosedEmbedding.isProperMap)
  have he : (RelativeSchemeValuedPoint.affineSpectrumHomeomorph
      (R := R) (A := A) (v := v)).symm ∘ RelativeSpectrum.baseChangeRestriction hw ∘
        affineTensorHomeomorph = nativeMap hw (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    funext y
    apply RelativeSchemeValuedPoint.affineSpectrumHomeomorph.injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact (affineTensorHomeomorph_nativeMap hw y).symm
  exact he ▸ h

end Affine

private abbrev affineSourceRingMap [IsAffine X] : R →+* Γ(X, ⊤) :=
  (Scheme.Spec.preimage (X.isoSpec.inv ≫ f)).unop.hom

private theorem affineSourceRingMap_spec [IsAffine X] :
    Spec.map (CommRingCat.ofHom (affineSourceRingMap f)) = X.isoSpec.inv ≫ f :=
  Scheme.Spec.map_preimage _

private def affineSourcePullbackIso [IsAffine X] :
    let := (affineSourceRingMap f).toAlgebra
    model (S := S) (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))) ≅ model (S := S) f := by
  let := (affineSourceRingMap f).toAlgebra
  exact asIso (pullback.map _ _ _ _ X.isoSpec.inv (𝟙 _) (𝟙 _)
    (by
      change Spec.map (CommRingCat.ofHom (affineSourceRingMap f)) ≫ 𝟙 _ = X.isoSpec.inv ≫ f
      rw [Category.comp_id]
      exact affineSourceRingMap_spec f) (by simp))

private theorem affineSourcePullbackIso_hom_structure [IsAffine X] :
    let := (affineSourceRingMap f).toAlgebra
    (affineSourcePullbackIso (S := S) f).hom ≫ structureMap (S := S) f =
      structureMap (S := S) (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))) := by
  let := (affineSourceRingMap f).toAlgebra
  simp [affineSourcePullbackIso, structureMap, pullback.map]

private theorem affineSourcePullbackIso_hom_projection [IsAffine X] :
    let := (affineSourceRingMap f).toAlgebra
    (affineSourcePullbackIso (S := S) f).hom ≫ projection (S := S) f =
      projection (S := S) (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))) ≫ X.isoSpec.inv := by
  let := (affineSourceRingMap f).toAlgebra
  simp [affineSourcePullbackIso, projection, pullback.map]

private theorem affineSourcePullbackIso_inv_projection [IsAffine X] :
    let := (affineSourceRingMap f).toAlgebra
    (affineSourcePullbackIso (S := S) f).inv ≫
      projection (S := S) (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))) =
        projection (S := S) f ≫ X.isoSpec.hom := by
  let := (affineSourceRingMap f).toAlgebra
  apply (cancel_epi (affineSourcePullbackIso (S := S) f).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc,
    affineSourcePullbackIso_hom_projection, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def affineSourceTensorHomeomorph [IsAffine X] :
    let := (affineSourceRingMap f).toAlgebra
    RelativeSchemeValuedPoint w (structureMap (S := S) f) ≃ₜ
      RelativeSpectrum w (S ⊗[R] Γ(X, ⊤)) := by
  let := (affineSourceRingMap f).toAlgebra
  let e := affineSourcePullbackIso (S := S) f
  have hs : e.inv ≫ structureMap (S := S)
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))) = structureMap (S := S) f := by
    rw [← affineSourcePullbackIso_hom_structure f, Iso.inv_hom_id_assoc]
  exact ((SchemeValuedPoint.isoHomeomorph e.symm).subtype (fun y => by
    change (SchemeValuedPoint.map (structureMap (S := S) f) y = _) ↔
      (SchemeValuedPoint.map (structureMap (S := S)
        (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))))
        (SchemeValuedPoint.map e.inv y) = _)
    rw [← SchemeValuedPoint.map_comp, hs])).trans affineTensorHomeomorph

private def affineSourceOriginalHomeomorph [IsAffine X] :
    let := (affineSourceRingMap f).toAlgebra
    RelativeSchemeValuedPoint v f ≃ₜ RelativeSpectrum v Γ(X, ⊤) := by
  let := (affineSourceRingMap f).toAlgebra
  exact ((SchemeValuedPoint.isoHomeomorph X.isoSpec).subtype (fun y => by
    change (SchemeValuedPoint.map f y = _) ↔
      (SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))))
        (SchemeValuedPoint.map X.isoSpec.hom y) = _)
    rw [← SchemeValuedPoint.map_comp]
    change (SchemeValuedPoint.map f y = _) ↔
      (SchemeValuedPoint.map (X.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (affineSourceRingMap f))) y = _)
    rw [affineSourceRingMap_spec, Iso.hom_inv_id_assoc])).trans
      RelativeSchemeValuedPoint.affineSpectrumHomeomorph

private theorem affineSourceTensorHomeomorph_nativeMap [IsAffine X]
    (y : RelativeSchemeValuedPoint w (structureMap (S := S) f)) :
    let := (affineSourceRingMap f).toAlgebra
    affineSourceOriginalHomeomorph f (nativeMap hw f y) =
      RelativeSpectrum.baseChangeRestriction hw (affineSourceTensorHomeomorph f y) := by
  let := (affineSourceRingMap f).toAlgebra
  apply Subtype.ext
  change SchemeValuedPoint.spectrumHomeomorph
    (SchemeValuedPoint.map X.isoSpec.hom
      (SchemeValuedPoint.map (projection (S := S) f) y.1)) =
    Spectrum.comap (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := Γ(X, ⊤))).toRingHom
      (SchemeValuedPoint.spectrumHomeomorph
        (SchemeValuedPoint.map (affineTensorIso (R := R) (S := S) (A := Γ(X, ⊤))).hom
          (SchemeValuedPoint.map (affineSourcePullbackIso (S := S) f).inv y.1)))
  rw [← SchemeValuedPoint.spectrumHomeomorph_map]
  simp only [← SchemeValuedPoint.map_comp]
  rw [Category.assoc, affineTensorIso_hom_projection, affineSourcePullbackIso_inv_projection]

/-- Any actual affine original source scheme has genuinely proper scalar
restriction under arbitrary compatible coefficient seminorms. The section-ring
coefficient action and the actual pullback comparison are both derived. -/
theorem isProperMap_nativeMap_of_isAffine [IsAffine X] : IsProperMap (nativeMap hw f) := by
  let := (affineSourceRingMap f).toAlgebra
  have h := (affineSourceOriginalHomeomorph (v := v) f).symm.isClosedEmbedding.isProperMap.comp
    ((RelativeSpectrum.isProperMap_baseChangeRestriction (A := Γ(X, ⊤)) hw).comp
      (affineSourceTensorHomeomorph (S := S) (w := w) f).isClosedEmbedding.isProperMap)
  have he : (affineSourceOriginalHomeomorph (v := v) f).symm ∘
      RelativeSpectrum.baseChangeRestriction hw ∘ affineSourceTensorHomeomorph f = nativeMap hw f := by
    funext y
    apply (affineSourceOriginalHomeomorph (v := v) f).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact (affineSourceTensorHomeomorph_nativeMap hw f y).symm
  exact he ▸ h

/-- Every whole native point of an actual affine scheme lifts through the
completion of an algebraic normed scalar extension of a complete field.
The actual affine section action and the true tensor point are derived. -/
theorem nativeMap_surjective_algebraicCompletion_of_isAffine
    {K L : Type u} [NormedField K] [NormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [CompleteSpace K] [Algebra.IsAlgebraic K L]
    {Y : Scheme.{u}} [IsAffine Y] (fK : Y ⟶ Spec (CommRingCat.of K)) :
    Function.Surjective (nativeMap
      (RelativeSpectrum.fcCompletedExtension_val_algebraMap (K := K) (L := L)) fK) := by
  let := (affineSourceRingMap fK).toAlgebra
  intro x
  obtain ⟨z, hz⟩ := RelativeSpectrum.fc_baseChangeRestriction_algebraicCompletion_surjective
    (A := Γ(Y, ⊤)) (L := L) (affineSourceOriginalHomeomorph fK x)
  refine ⟨(affineSourceTensorHomeomorph (S := UniformSpace.Completion L) fK).symm z, ?_⟩
  apply (affineSourceOriginalHomeomorph fK).injective
  rw [affineSourceTensorHomeomorph_nativeMap, Homeomorph.apply_symm_apply]
  exact hz

end EnvelopeProperty.Berkovich.SchemeScalarBaseChange
