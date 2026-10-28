/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeAffineBaseCompletedFibre
import EnvelopeProperty.Berkovich.SchemeResidueAffineComparison

open scoped NNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeCompletedFibre
variable {X Y : Scheme.{u}}

/-- The LITERAL scheme fibre over the original native point's actual completed stalk residue field. -/
abbrev model (f : X ⟶ Y) (x : SchemeValuedPoint Y) : Scheme.{u} :=
  pullback f (SchemeValuedPoint.fieldPoint x)

/-- Its true original scheme projection to X. -/
abbrev projection (f : X ⟶ Y) (x : SchemeValuedPoint Y) : model f x ⟶ X := pullback.fst _ _

/-- The ORIGINAL completed-residue structure map of that SAME scheme fibre. -/
abbrev structureMap (f : X ⟶ Y) (x : SchemeValuedPoint Y) :
    model f x ⟶ Spec (CommRingCat.of (SchemeValuedPoint.H x)) := pullback.snd _ _

/-- Whole native projection into the original point fibre, derived from the true pullback square. -/
def nativeProjection (f : X ⟶ Y) (x : SchemeValuedPoint Y) :
    RelativeSchemeValuedPoint (NormedField.valuation (K := SchemeValuedPoint.H x)) (structureMap f x) →
      {y : SchemeValuedPoint X // SchemeValuedPoint.map f y = x} := fun y =>
  ⟨SchemeValuedPoint.map (projection f x) y.1, by
    rw [← SchemeValuedPoint.map_comp, pullback.condition, SchemeValuedPoint.map_comp,
      show SchemeValuedPoint.map (structureMap f x) y.1 =
        SchemeValuedPoint.basePoint (NormedField.valuation (K := SchemeValuedPoint.H x)) from y.2,
      SchemeValuedPoint.map_norm_basePoint_fieldPoint]⟩

/-- The true original fibre projection is continuous on the precise fixed-norm native space. -/
theorem continuous_nativeProjection (f : X ⟶ Y) (x : SchemeValuedPoint Y) :
    Continuous (nativeProjection f x) :=
  ((SchemeValuedPoint.continuous_map (projection f x)).comp continuous_subtype_val).subtype_mk _

private def baseOpenFibreMap {A : Type u} [CommRing A]
    (f : X ⟶ Y) (g : Spec (CommRingCat.of A) ⟶ Y) (a : Spectrum A) :
    {z : SchemeValuedPoint (pullback f g) // SchemeValuedPoint.map (pullback.snd f g) z =
      SchemeValuedPoint.spectrumHomeomorph.symm a} →
    {y : SchemeValuedPoint X // SchemeValuedPoint.map f y =
      SchemeValuedPoint.map g (SchemeValuedPoint.spectrumHomeomorph.symm a)} := fun z =>
  ⟨SchemeValuedPoint.map (pullback.fst f g) z.1, by
    rw [← SchemeValuedPoint.map_comp, pullback.condition, SchemeValuedPoint.map_comp, z.2]⟩

private theorem baseOpenFibreMap_surjective {A : Type u} [CommRing A]
    (f : X ⟶ Y) (g : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion g] (a : Spectrum A) :
    Function.Surjective (baseOpenFibreMap f g a) := by
  intro y
  have hy : y.1.point ∈ Set.range (pullback.fst f g) := by
    rw [IsOpenImmersion.range_pullbackFst]
    have hp := congrArg SchemeValuedPoint.point y.2
    change f y.1.point = g (SchemeValuedPoint.spectrumHomeomorph.symm a).point at hp
    exact ⟨(SchemeValuedPoint.spectrumHomeomorph.symm a).point, hp.symm⟩
  obtain ⟨z, hz⟩ := SchemeValuedPoint.exists_map_eq_of_point_mem_range (pullback.fst f g) y.1 hy
  have hbase : SchemeValuedPoint.map (pullback.snd f g) z =
      SchemeValuedPoint.spectrumHomeomorph.symm a := by
    apply SchemeValuedPoint.map_injective_of_isOpenImmersion g
    rw [← SchemeValuedPoint.map_comp, ← pullback.condition, SchemeValuedPoint.map_comp, hz]
    exact y.2
  exact ⟨⟨z, hbase⟩, Subtype.ext hz⟩

private def baseOpenFibreHomeomorph {A : Type u} [CommRing A]
    (f : X ⟶ Y) (g : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion g] (a : Spectrum A) :
    {z : SchemeValuedPoint (pullback f g) // SchemeValuedPoint.map (pullback.snd f g) z =
      SchemeValuedPoint.spectrumHomeomorph.symm a} ≃ₜ
    {y : SchemeValuedPoint X // SchemeValuedPoint.map f y =
      SchemeValuedPoint.map g (SchemeValuedPoint.spectrumHomeomorph.symm a)} := by
  have hi : IsEmbedding (baseOpenFibreMap f g a) := by
    apply IsEmbedding.subtypeVal.of_comp_iff.mp
    exact (SchemeValuedPoint.isOpenEmbedding_map_of_isOpenImmersion (pullback.fst f g)).isEmbedding.comp
      IsEmbedding.subtypeVal
  exact hi.toHomeomorphOfSurjective (baseOpenFibreMap_surjective f g a)

private def fieldPullbackIso {A K : Type u} [CommRing A] [NormedField K]
    (f : X ⟶ Y) (g : Spec (CommRingCat.of A) ⟶ Y) (a : Spectrum A)
    (q : Spec (CommRingCat.of K) ⟶ Y) (E : K ≃+* Spectrum.H a)
    (hE : Spec.map (CommRingCat.ofHom E.toRingHom) ≫ q =
      Spec.map (CommRingCat.ofHom a.toH) ≫ g) :
    affineBaseModel (pullback.snd f g) a ≅ pullback f q := by
  let e := Scheme.Spec.mapIso E.toCommRingCatIso.op
  exact pullbackLeftPullbackSndIso f g (Spec.map (CommRingCat.ofHom a.toH)) ≪≫
    asIso (pullback.map _ _ _ _ (𝟙 X) e.hom (𝟙 Y)
      (by simp) (by
        change Spec.map (CommRingCat.ofHom a.toH) ≫ g =
          Spec.map (CommRingCat.ofHom E.toRingHom) ≫ q
        exact hE.symm))

private theorem fieldPullbackIso_projection {A K : Type u} [CommRing A] [NormedField K]
    (f : X ⟶ Y) (g : Spec (CommRingCat.of A) ⟶ Y) (a : Spectrum A)
    (q : Spec (CommRingCat.of K) ⟶ Y) (E : K ≃+* Spectrum.H a)
    (hE : Spec.map (CommRingCat.ofHom E.toRingHom) ≫ q =
      Spec.map (CommRingCat.ofHom a.toH) ≫ g) :
    (fieldPullbackIso f g a q E hE).hom ≫ pullback.fst f q =
      affineBaseProjection (pullback.snd f g) a ≫ pullback.fst f g := by
  simp [fieldPullbackIso, pullback.map, pullback.lift_fst, affineBaseProjection]

private theorem fieldPullbackIso_structure {A K : Type u} [CommRing A] [NormedField K]
    (f : X ⟶ Y) (g : Spec (CommRingCat.of A) ⟶ Y) (a : Spectrum A)
    (q : Spec (CommRingCat.of K) ⟶ Y) (E : K ≃+* Spectrum.H a)
    (hE : Spec.map (CommRingCat.ofHom E.toRingHom) ≫ q =
      Spec.map (CommRingCat.ofHom a.toH) ≫ g) :
    (fieldPullbackIso f g a q E hE).hom ≫ pullback.snd f q =
      affineBaseStructureMap (pullback.snd f g) a ≫ Spec.map (CommRingCat.ofHom E.toRingHom) := by
  simp [fieldPullbackIso, pullback.map, pullback.lift_snd, affineBaseStructureMap]

private def fieldPullbackRelativeHomeomorph {A K : Type u} [CommRing A] [NormedField K]
    [IsUltrametricDist K] (f : X ⟶ Y) (g : Spec (CommRingCat.of A) ⟶ Y) (a : Spectrum A)
    (q : Spec (CommRingCat.of K) ⟶ Y) (E : K ≃+* Spectrum.H a)
    (hn : ∀ z, ‖E z‖ = ‖z‖)
    (hE : Spec.map (CommRingCat.ofHom E.toRingHom) ≫ q =
      Spec.map (CommRingCat.ofHom a.toH) ≫ g) :
    RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H a))
      (affineBaseStructureMap (pullback.snd f g) a) ≃ₜ
    RelativeSchemeValuedPoint (NormedField.valuation (K := K)) (pullback.snd f q) := by
  let e := Scheme.Spec.mapIso E.toCommRingCatIso.op
  have hb : SchemeValuedPoint.map e.hom
      (SchemeValuedPoint.basePoint (NormedField.valuation (K := Spectrum.H a))) =
        SchemeValuedPoint.basePoint (NormedField.valuation (K := K)) :=
    SchemeValuedPoint.map_basePoint E.toRingHom (fun z => NNReal.eq (hn z))
  exact (SchemeValuedPoint.isoHomeomorph (fieldPullbackIso f g a q E hE)).subtype (fun y => by
    change (SchemeValuedPoint.map (affineBaseStructureMap (pullback.snd f g) a) y = _) ↔
      (SchemeValuedPoint.map (pullback.snd f q)
        (SchemeValuedPoint.map (fieldPullbackIso f g a q E hE).hom y) = _)
    rw [← SchemeValuedPoint.map_comp, fieldPullbackIso_structure, SchemeValuedPoint.map_comp]
    rw [← hb]
    exact (SchemeValuedPoint.map_injective_of_isOpenImmersion e.hom).eq_iff.symm)

private theorem exists_wholeFibreHomeomorph (f : X ⟶ Y) (x : SchemeValuedPoint Y) :
    ∃ h : RelativeSchemeValuedPoint (NormedField.valuation (K := SchemeValuedPoint.H x))
      (structureMap f x) ≃ₜ {y : SchemeValuedPoint X // SchemeValuedPoint.map f y = x},
      ∀ y, h y = nativeProjection f x y := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x.point ∈ (⊤ : Y.Opens) from trivial)
  let a := SchemeValuedPoint.affineOpenSpectrumHomeomorph hU ⟨x, hx⟩
  have hmap : SchemeValuedPoint.map hU.fromSpec
      (SchemeValuedPoint.spectrumHomeomorph.symm a) = x := by
    have he := congrArg Subtype.val
      ((SchemeValuedPoint.affineOpenSpectrumHomeomorph hU).symm_apply_apply ⟨x, hx⟩)
    rw [SchemeValuedPoint.affineOpenSpectrumHomeomorph_symm_coe] at he
    change SchemeValuedPoint.map U.ι (SchemeValuedPoint.map hU.isoSpec.inv
      (SchemeValuedPoint.spectrumHomeomorph.symm a)) = x at he
    simpa only [IsAffineOpen.fromSpec, SchemeValuedPoint.map_comp] using he
  obtain ⟨E, hn, _, hE⟩ := SchemeValuedPoint.exists_affineCompletionEquiv_fieldPoint x hU hx
  let e := fieldPullbackRelativeHomeomorph f hU.fromSpec a (SchemeValuedPoint.fieldPoint x) E hn hE
  let b := baseOpenFibreHomeomorph f hU.fromSpec a
  let c : {y : SchemeValuedPoint X // SchemeValuedPoint.map f y =
      SchemeValuedPoint.map hU.fromSpec (SchemeValuedPoint.spectrumHomeomorph.symm a)} ≃ₜ
      {y : SchemeValuedPoint X // SchemeValuedPoint.map f y = x} :=
    Homeomorph.setCongr (by rw [hmap])
  let h := e.symm.trans ((affineBaseFibreHomeomorph (pullback.snd f hU.fromSpec) a).trans (b.trans c))
  refine ⟨h, ?_⟩
  intro y
  apply Subtype.ext
  change SchemeValuedPoint.map (pullback.fst f hU.fromSpec)
    ((affineBaseFibreHomeomorph (pullback.snd f hU.fromSpec) a) (e.symm y)).1 = _
  rw [affineBaseFibreHomeomorph_apply, ← SchemeValuedPoint.map_comp]
  change SchemeValuedPoint.map
    (affineBaseProjection (pullback.snd f hU.fromSpec) a ≫ pullback.fst f hU.fromSpec)
      (SchemeValuedPoint.map (fieldPullbackIso f hU.fromSpec a
        (SchemeValuedPoint.fieldPoint x) E hE).inv y.1) = _
  rw [← SchemeValuedPoint.map_comp,
    ← fieldPullbackIso_projection f hU.fromSpec a (SchemeValuedPoint.fieldPoint x) E hE,
    Iso.inv_hom_id_assoc]
  rfl

/-- The native fixed-norm point space of the LITERAL scheme fibre over the
ORIGINAL completed stalk residue field is its WHOLE original native fibre. -/
def nativeFibreHomeomorph (f : X ⟶ Y) (x : SchemeValuedPoint Y) :
    RelativeSchemeValuedPoint (NormedField.valuation (K := SchemeValuedPoint.H x)) (structureMap f x) ≃ₜ
      {y : SchemeValuedPoint X // SchemeValuedPoint.map f y = x} :=
  Classical.choose (exists_wholeFibreHomeomorph f x)

/-- The whole forward point is EXACTLY the original scheme projection. -/
theorem nativeFibreHomeomorph_apply (f : X ⟶ Y) (x : SchemeValuedPoint Y)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := SchemeValuedPoint.H x))
      (structureMap f x)) :
    (nativeFibreHomeomorph f x y).1 = SchemeValuedPoint.map (projection f x) y.1 :=
  congrArg Subtype.val (Classical.choose_spec (exists_wholeFibreHomeomorph f x) y)

/-- The actual inverse recovers EVERY whole original fibre point through the SAME projection. -/
theorem projection_map_nativeFibreHomeomorph_symm (f : X ⟶ Y) (x : SchemeValuedPoint Y)
    (y : {z : SchemeValuedPoint X // SchemeValuedPoint.map f z = x}) :
    SchemeValuedPoint.map (projection f x) ((nativeFibreHomeomorph f x).symm y).1 = y.1 := by
  rw [← nativeFibreHomeomorph_apply]
  exact congrArg Subtype.val ((nativeFibreHomeomorph f x).apply_symm_apply y)

end EnvelopeProperty.Berkovich.SchemeCompletedFibre
