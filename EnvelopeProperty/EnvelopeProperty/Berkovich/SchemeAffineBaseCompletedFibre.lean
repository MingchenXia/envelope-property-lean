/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeAffineCompletedFibre
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas
import EnvelopeProperty.Berkovich.SchemeRelativeBaseChange

open scoped NNReal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeCompletedFibre
variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- The actual completed-residue scheme fibre of an original morphism to an affine base. -/
abbrev affineBaseModel (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom a.toH))

/-- The true original projection of this same fibre. -/
abbrev affineBaseProjection (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    affineBaseModel f a ⟶ X := pullback.fst _ _

/-- Its exact original completed-field structure map. -/
abbrev affineBaseStructureMap (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    affineBaseModel f a ⟶ Spec (CommRingCat.of (Spectrum.H a)) := pullback.snd _ _

/-- The genuine coefficient norm point maps to the ENTIRE original affine base point. -/
theorem map_norm_toH (a : Spectrum A) :
    SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom a.toH))
      (SchemeValuedPoint.basePoint (NormedField.valuation (K := Spectrum.H a))) =
      SchemeValuedPoint.spectrumHomeomorph.symm a :=
  SchemeValuedPoint.map_basePoint a.toH (fun b => Spectrum.nnnorm_toH a b)

/-- Whole native projection from the true scheme fibre to the original native point fibre. -/
def affineBaseNativeProjection (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (affineBaseStructureMap f a) →
      {x : SchemeValuedPoint X // SchemeValuedPoint.map f x =
        SchemeValuedPoint.spectrumHomeomorph.symm a} := fun y =>
  ⟨SchemeValuedPoint.map (affineBaseProjection f a) y.1, by
    rw [← SchemeValuedPoint.map_comp, pullback.condition, SchemeValuedPoint.map_comp,
      show SchemeValuedPoint.map (affineBaseStructureMap f a) y.1 =
        SchemeValuedPoint.basePoint (NormedField.valuation (K := Spectrum.H a)) from y.2,
      map_norm_toH]⟩

/-- This is the actual continuous projection on WHOLE original native points. -/
theorem continuous_affineBaseNativeProjection (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    Continuous (affineBaseNativeProjection f a) :=
  ((SchemeValuedPoint.continuous_map (affineBaseProjection f a)).comp
    continuous_subtype_val).subtype_mk _

private abbrev affineSourceRingMap [IsAffine X] (f : X ⟶ Spec (CommRingCat.of A)) :
    A →+* Γ(X, ⊤) := (Scheme.Spec.preimage (X.isoSpec.inv ≫ f)).unop.hom

private theorem affineSourceRingMap_spec [IsAffine X] (f : X ⟶ Spec (CommRingCat.of A)) :
    Spec.map (CommRingCat.ofHom (affineSourceRingMap f)) = X.isoSpec.inv ≫ f :=
  by
    change Scheme.Spec.map (Scheme.Spec.preimage (X.isoSpec.inv ≫ f)) = _
    exact Scheme.Spec.map_preimage _

private def affineSourcePullbackIso [IsAffine X] (f : X ⟶ Spec (CommRingCat.of A))
    (a : Spectrum A) :
    let := (affineSourceRingMap f).toAlgebra
    affineModel (B := Γ(X, ⊤)) a ≅ affineBaseModel f a := by
  let := (affineSourceRingMap f).toAlgebra
  exact asIso (pullback.map _ _ _ _ X.isoSpec.inv (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using affineSourceRingMap_spec f) (by simp))

private theorem affineSourcePullbackIso_hom_structure [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    let := (affineSourceRingMap f).toAlgebra
    (affineSourcePullbackIso f a).hom ≫ affineBaseStructureMap f a =
      affineStructureMap (B := Γ(X, ⊤)) a := by
  let := (affineSourceRingMap f).toAlgebra
  simp [affineSourcePullbackIso, affineBaseStructureMap, affineStructureMap, pullback.map, pullback.lift_snd]

private theorem affineSourcePullbackIso_hom_projection [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    let := (affineSourceRingMap f).toAlgebra
    (affineSourcePullbackIso f a).hom ≫ affineBaseProjection f a =
      affineProjection (B := Γ(X, ⊤)) a ≫ X.isoSpec.inv := by
  let := (affineSourceRingMap f).toAlgebra
  simp [affineSourcePullbackIso, affineBaseProjection, affineProjection, pullback.map, pullback.lift_fst]

private def affineSourceRelativeHomeomorph [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    let := (affineSourceRingMap f).toAlgebra
    RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (affineBaseStructureMap f a) ≃ₜ
    RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (affineStructureMap (B := Γ(X, ⊤)) a) := by
  let := (affineSourceRingMap f).toAlgebra
  let i := affineSourcePullbackIso f a
  have hs : i.inv ≫ affineStructureMap (B := Γ(X, ⊤)) a = affineBaseStructureMap f a := by
    rw [← affineSourcePullbackIso_hom_structure f a, Iso.inv_hom_id_assoc]
  exact (SchemeValuedPoint.isoHomeomorph i.symm).subtype (fun y => by
    change (SchemeValuedPoint.map (affineBaseStructureMap f a) y = _) ↔
      (SchemeValuedPoint.map (affineStructureMap (B := Γ(X, ⊤)) a)
        (SchemeValuedPoint.map i.inv y) = _)
    rw [← SchemeValuedPoint.map_comp, hs])

private def affineSourceOriginalFibreHomeomorph [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    let := (affineSourceRingMap f).toAlgebra
    {z : SchemeValuedPoint (Spec Γ(X, ⊤)) //
      SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤)))) z =
        SchemeValuedPoint.spectrumHomeomorph.symm a} ≃ₜ
      {x : SchemeValuedPoint X // SchemeValuedPoint.map f x =
        SchemeValuedPoint.spectrumHomeomorph.symm a} := by
  let := (affineSourceRingMap f).toAlgebra
  exact (SchemeValuedPoint.isoHomeomorph X.isoSpec.symm).subtype (fun z => by
    change (SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (affineSourceRingMap f))) z = _) ↔
      (SchemeValuedPoint.map f (SchemeValuedPoint.map X.isoSpec.inv z) = _)
    rw [← SchemeValuedPoint.map_comp, ← affineSourceRingMap_spec f])

/-- An actual affine SOURCE scheme fibre retains the entire original native fibre,
for its genuine structure map, without a separately supplied section action. -/
def affineSourceFibreHomeomorph [IsAffine X] (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (affineBaseStructureMap f a) ≃ₜ
      {x : SchemeValuedPoint X // SchemeValuedPoint.map f x =
        SchemeValuedPoint.spectrumHomeomorph.symm a} := by
  let := (affineSourceRingMap f).toAlgebra
  exact (affineSourceRelativeHomeomorph f a).trans
    ((affineFibreHomeomorph (B := Γ(X, ⊤)) a).trans (affineSourceOriginalFibreHomeomorph f a))

/-- The actual affine-source homeomorphism is the WHOLE original pullback projection. -/
theorem affineSourceFibreHomeomorph_apply [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (affineBaseStructureMap f a)) :
    affineSourceFibreHomeomorph f a y = affineBaseNativeProjection f a y := by
  let := (affineSourceRingMap f).toAlgebra
  apply Subtype.ext
  change SchemeValuedPoint.map X.isoSpec.inv
    ((affineFibreHomeomorph (B := Γ(X, ⊤)) a (affineSourceRelativeHomeomorph f a y)).1) = _
  rw [affineFibreHomeomorph_apply, ← SchemeValuedPoint.map_comp]
  change SchemeValuedPoint.map (affineProjection (B := Γ(X, ⊤)) a ≫ X.isoSpec.inv)
    (SchemeValuedPoint.map (affineSourcePullbackIso f a).inv y.1) = _
  rw [← SchemeValuedPoint.map_comp]
  rw [← affineSourcePullbackIso_hom_projection f a, Iso.inv_hom_id_assoc]
  rfl

private def sourceOpenChartMap {U : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) (g : U ⟶ X) :
    affineBaseModel (g ≫ f) a ⟶ affineBaseModel f a :=
  (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom a.toH)) g).inv ≫
    pullback.snd g (pullback.fst f (Spec.map (CommRingCat.ofHom a.toH)))

private instance sourceOpenChartMap_isOpenImmersion {U : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) (g : U ⟶ X) [IsOpenImmersion g] :
    IsOpenImmersion (sourceOpenChartMap f a g) := by
  dsimp only [sourceOpenChartMap]
  infer_instance

private theorem sourceOpenChartMap_structure {U : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) (g : U ⟶ X) :
    sourceOpenChartMap f a g ≫ affineBaseStructureMap f a = affineBaseStructureMap (g ≫ f) a :=
  by
    simpa only [sourceOpenChartMap, affineBaseStructureMap, Category.assoc] using
      pullbackRightPullbackFstIso_inv_snd_snd f (Spec.map (CommRingCat.ofHom a.toH)) g

private theorem sourceOpenChartMap_projection {U : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) (g : U ⟶ X) :
    sourceOpenChartMap f a g ≫ affineBaseProjection f a = affineBaseProjection (g ≫ f) a ≫ g :=
  by
    simpa only [sourceOpenChartMap, affineBaseProjection, Category.assoc] using
      pullbackRightPullbackFstIso_inv_snd_fst f (Spec.map (CommRingCat.ofHom a.toH)) g

private theorem sourceOpenChartMap_range {U : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) (g : U ⟶ X) [IsOpenImmersion g] :
    (sourceOpenChartMap f a g).opensRange = (affineBaseProjection f a) ⁻¹ᵁ g.opensRange := by
  change ((pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom a.toH)) g).inv ≫
    pullback.snd g (pullback.fst f (Spec.map (CommRingCat.ofHom a.toH)))).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackSnd]

private theorem sourceOpenChartNative_commutes {U : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) (g : U ⟶ X)
    (z : RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (affineBaseStructureMap (g ≫ f) a)) :
    affineBaseNativeProjection f a
      (RelativeSchemeValuedPoint.map (sourceOpenChartMap f a g) (sourceOpenChartMap_structure f a g) z) =
    RelativeSchemeValuedPoint.map (v := a.val) g rfl (affineBaseNativeProjection (g ≫ f) a z) := by
  apply Subtype.ext
  change SchemeValuedPoint.map (affineBaseProjection f a)
    (SchemeValuedPoint.map (sourceOpenChartMap f a g) z.1) =
    SchemeValuedPoint.map g (SchemeValuedPoint.map (affineBaseProjection (g ≫ f) a) z.1)
  rw [← SchemeValuedPoint.map_comp, sourceOpenChartMap_projection,
    SchemeValuedPoint.map_comp]

private theorem exists_sourceOpenChartNative {U : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) (g : U ⟶ X) [IsOpenImmersion g]
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (affineBaseStructureMap f a))
    (hy : (affineBaseProjection f a) y.1.point ∈ g.opensRange) :
    ∃ z, RelativeSchemeValuedPoint.map (sourceOpenChartMap f a g)
      (sourceOpenChartMap_structure f a g) z = y := by
  change y ∈ Set.range (RelativeSchemeValuedPoint.map (sourceOpenChartMap f a g)
    (sourceOpenChartMap_structure f a g))
  rw [RelativeSchemeValuedPoint.range_map_of_isOpenImmersion]
  change y.1.point ∈ (sourceOpenChartMap f a g).opensRange
  rw [sourceOpenChartMap_range]
  exact hy

/-- Every original native point in the completed-residue fibre has a genuine lift
on the ACTUAL base-changed scheme, using its true source-affine cover. -/
theorem affineBaseNativeProjection_surjective
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    Function.Surjective (affineBaseNativeProjection f a) := by
  intro y
  obtain ⟨i, p, hp⟩ := X.affineCover.exists_eq y.1.point
  have hy : y.1.point ∈ (X.affineCover.f i).opensRange := ⟨p, hp⟩
  have hrange : y ∈ Set.range (RelativeSchemeValuedPoint.map
      (v := a.val) (fY := f) (X.affineCover.f i) rfl) := by
    rw [RelativeSchemeValuedPoint.range_map_of_isOpenImmersion]
    exact hy
  obtain ⟨z, hz⟩ := hrange
  let w := (affineSourceFibreHomeomorph (X.affineCover.f i ≫ f) a).symm z
  refine ⟨RelativeSchemeValuedPoint.map (sourceOpenChartMap f a (X.affineCover.f i))
    (sourceOpenChartMap_structure f a (X.affineCover.f i)) w, ?_⟩
  rw [sourceOpenChartNative_commutes, ← affineSourceFibreHomeomorph_apply]
  exact ((congrArg (RelativeSchemeValuedPoint.map (v := a.val) (X.affineCover.f i) rfl)
    ((affineSourceFibreHomeomorph (X.affineCover.f i ≫ f) a).apply_symm_apply z))).trans hz

/-- The original completed-residue projection is injective on WHOLE native points,
by the actual same-affine-source fibre comparisons. -/
theorem affineBaseNativeProjection_injective
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    Function.Injective (affineBaseNativeProjection f a) := by
  intro y z hyz
  obtain ⟨i, p, hp⟩ := X.affineCover.exists_eq ((affineBaseProjection f a) y.1.point)
  have hy : (affineBaseProjection f a) y.1.point ∈ (X.affineCover.f i).opensRange := ⟨p, hp⟩
  have hz : (affineBaseProjection f a) z.1.point ∈ (X.affineCover.f i).opensRange := by
    have hpoint := congrArg (fun t => t.1.point) hyz
    change (affineBaseProjection f a) y.1.point = (affineBaseProjection f a) z.1.point at hpoint
    exact hpoint ▸ hy
  obtain ⟨y', rfl⟩ := exists_sourceOpenChartNative f a (X.affineCover.f i) y hy
  obtain ⟨z', rfl⟩ := exists_sourceOpenChartNative f a (X.affineCover.f i) z hz
  rw [sourceOpenChartNative_commutes, sourceOpenChartNative_commutes] at hyz
  have hlocal := (RelativeSchemeValuedPoint.isOpenEmbedding_map_of_isOpenImmersion
    (v := a.val) (fY := f) (X.affineCover.f i) rfl).injective hyz
  have he : y' = z' := (affineSourceFibreHomeomorph (X.affineCover.f i ≫ f) a).injective (by
    apply Subtype.ext
    simpa only [affineSourceFibreHomeomorph_apply] using congrArg Subtype.val hlocal)
  exact congrArg _ he

private theorem sourceOpenChartNative_jointly_surjective
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (affineBaseStructureMap f a)) :
    ∃ i, ∃ z, RelativeSchemeValuedPoint.map (sourceOpenChartMap f a (X.affineCover.f i))
      (sourceOpenChartMap_structure f a (X.affineCover.f i)) z = y := by
  obtain ⟨i, p, hp⟩ := X.affineCover.exists_eq ((affineBaseProjection f a) y.1.point)
  exact ⟨i, exists_sourceOpenChartNative f a (X.affineCover.f i) y ⟨p, hp⟩⟩

private theorem isOpenMap_comp_sourceOpenChartNative {U : Scheme.{u}} [IsAffine U]
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) (g : U ⟶ X) [IsOpenImmersion g] :
    IsOpenMap (fun z => affineBaseNativeProjection f a
      (RelativeSchemeValuedPoint.map (sourceOpenChartMap f a g)
        (sourceOpenChartMap_structure f a g) z)) := by
  have he : (fun z => affineBaseNativeProjection f a
      (RelativeSchemeValuedPoint.map (sourceOpenChartMap f a g)
        (sourceOpenChartMap_structure f a g) z)) =
    (RelativeSchemeValuedPoint.map (v := a.val) (fY := f) g rfl) ∘
      affineSourceFibreHomeomorph (g ≫ f) a := by
    funext z
    rw [sourceOpenChartNative_commutes]
    exact congrArg (RelativeSchemeValuedPoint.map (v := a.val) (fY := f) g rfl)
      (affineSourceFibreHomeomorph_apply (g ≫ f) a z).symm
  rw [he]
  exact (RelativeSchemeValuedPoint.isOpenEmbedding_map_of_isOpenImmersion
    (v := a.val) (fY := f) g rfl).isOpenMap.comp (affineSourceFibreHomeomorph (g ≫ f) a).isOpenMap

/-- The actual projection is OPEN, by its true base-changed source-affine cover
and the same whole local homeomorphisms; no compactness or Hausdorffness is used. -/
theorem isOpenMap_affineBaseNativeProjection
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    IsOpenMap (affineBaseNativeProjection f a) := by
  intro W hW
  let J := fun i => RelativeSchemeValuedPoint.map (v := NormedField.valuation (K := Spectrum.H a))
    (sourceOpenChartMap f a (X.affineCover.f i))
    (sourceOpenChartMap_structure f a (X.affineCover.f i))
  have he : affineBaseNativeProjection f a '' W =
      ⋃ i, (affineBaseNativeProjection f a ∘ J i) '' ((J i) ⁻¹' W) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, z, hz⟩ := sourceOpenChartNative_jointly_surjective f a x
      have hz' : J i z = x := hz
      have hw : z ∈ (J i) ⁻¹' W := by
        change J i z ∈ W
        rw [hz']
        exact hx
      exact Set.mem_iUnion.mpr ⟨i, z, hw, congrArg (affineBaseNativeProjection f a) hz'⟩
    · intro hy
      obtain ⟨i, z, hz, hez⟩ := Set.mem_iUnion.mp hy
      exact ⟨J i z, hz, hez⟩
  rw [he]
  apply isOpen_iUnion
  intro i
  exact (isOpenMap_comp_sourceOpenChartNative f a (X.affineCover.f i))
    _ (hW.preimage (RelativeSchemeValuedPoint.continuous_map _ _))

/-- The WHOLE original native fibre of any scheme over an affine base is
homeomorphic to the fixed-norm native space of its ACTUAL scheme pullback. -/
def affineBaseFibreHomeomorph (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A) :
    RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (affineBaseStructureMap f a) ≃ₜ
      {x : SchemeValuedPoint X // SchemeValuedPoint.map f x =
        SchemeValuedPoint.spectrumHomeomorph.symm a} :=
  (Equiv.ofBijective (affineBaseNativeProjection f a)
    ⟨affineBaseNativeProjection_injective f a, affineBaseNativeProjection_surjective f a⟩).toHomeomorphOfContinuousOpen (continuous_affineBaseNativeProjection f a)
      (isOpenMap_affineBaseNativeProjection f a)

/-- The genuine whole fibre homeomorphism is EXACTLY the original scheme projection. -/
theorem affineBaseFibreHomeomorph_apply (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (affineBaseStructureMap f a)) :
    (affineBaseFibreHomeomorph f a y).1 =
      SchemeValuedPoint.map (affineBaseProjection f a) y.1 := rfl

/-- The actual inverse recovers the ENTIRE original fibre point through the same projection. -/
theorem affineBaseProjection_map_affineBaseFibreHomeomorph_symm
    (f : X ⟶ Spec (CommRingCat.of A)) (a : Spectrum A)
    (y : {x : SchemeValuedPoint X // SchemeValuedPoint.map f x =
      SchemeValuedPoint.spectrumHomeomorph.symm a}) :
    SchemeValuedPoint.map (affineBaseProjection f a)
      ((affineBaseFibreHomeomorph f a).symm y).1 = y.1 :=
  congrArg Subtype.val ((affineBaseFibreHomeomorph f a).apply_symm_apply y)

end EnvelopeProperty.Berkovich.SchemeCompletedFibre
