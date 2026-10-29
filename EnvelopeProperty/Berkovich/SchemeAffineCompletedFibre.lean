/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumFibreTopology
import EnvelopeProperty.Berkovich.SchemeRelativeValuedPoints
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The actual affine SCHEME fibre over the original completed residue field -/
open scoped NNReal TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeCompletedFibre
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The ORIGINAL scheme pullback along the actual completed-residue coefficient map. -/
abbrev affineModel (x : Spectrum A) : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom x.toH))

/-- Its SAME original scheme projection to Spec B. -/
abbrev affineProjection (x : Spectrum A) : affineModel (B := B) x ⟶ Spec (CommRingCat.of B) :=
  pullback.fst _ _

/-- The true structure map to the ORIGINAL completed residue field. -/
abbrev affineStructureMap (x : Spectrum A) :
    affineModel (B := B) x ⟶ Spec (CommRingCat.of (Spectrum.H x)) := pullback.snd _ _

/-- Real pullback symmetry and the true Spec tensor pushout supply an actual scheme isomorphism. -/
def affineTensorIso (x : Spectrum A) :
    affineModel (B := B) x ≅ Spec (CommRingCat.of (Spectrum.H x ⊗[A] B)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso A (Spectrum.H x) B

set_option backward.isDefEq.respectTransparency false in
/-- The actual tensor isomorphism preserves the WHOLE original B projection. -/
theorem affineTensorIso_hom_projection (x : Spectrum A) :
    (affineTensorIso (B := B) x).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := Spectrum.H x) (B := B)).toRingHom) =
      affineProjection (B := B) x := by
  change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso A (Spectrum.H x) B).hom) ≫ _ = _
  rw [Category.assoc]
  erw [pullbackSpecIso_hom_snd]
  exact pullbackSymmetry_hom_comp_snd _ _

/-- The SAME actual tensor isomorphism preserves the WHOLE original H(x) coefficient map. -/
theorem affineTensorIso_hom_structureMap (x : Spectrum A) :
    (affineTensorIso (B := B) x).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Spectrum.H x) (Spectrum.H x ⊗[A] B))) =
      affineStructureMap (B := B) x := by
  change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso A (Spectrum.H x) B).hom) ≫ _ = _
  rw [Category.assoc, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]

/-- Restrict the true native tensor scheme isomorphism to the EXACT completed-field norm. -/
def affineTensorRelativeHomeomorph (x : Spectrum A) :
    RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H x))
      (affineStructureMap (B := B) x) ≃ₜ
    RelativeSpectrum (NormedField.valuation (K := Spectrum.H x)) (Spectrum.H x ⊗[A] B) :=
  ((SchemeValuedPoint.isoHomeomorph (affineTensorIso (B := B) x)).subtype (fun y => by
    change (SchemeValuedPoint.map (affineStructureMap (B := B) x) y = _) ↔
      (SchemeValuedPoint.map
        (Spec.map (CommRingCat.ofHom (algebraMap (Spectrum.H x) (Spectrum.H x ⊗[A] B))))
        (SchemeValuedPoint.map (affineTensorIso (B := B) x).hom y) = _)
    rw [← SchemeValuedPoint.map_comp, affineTensorIso_hom_structureMap])).trans
      RelativeSchemeValuedPoint.affineSpectrumHomeomorph

private def affineOriginalFibreHomeomorph (x : Spectrum A) :
    Spectrum.Fibre (B := B) x ≃ₜ
      {y : SchemeValuedPoint (Spec (CommRingCat.of B)) //
        SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (algebraMap A B))) y =
          SchemeValuedPoint.spectrumHomeomorph.symm x} :=
  SchemeValuedPoint.spectrumHomeomorph.symm.subtype (fun y => by
    constructor
    · intro h
      apply SchemeValuedPoint.spectrumHomeomorph.injective
      rw [SchemeValuedPoint.spectrumHomeomorph_map,
        Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
      exact h
    · intro h
      have he := congrArg SchemeValuedPoint.spectrumHomeomorph h
      simpa only [SchemeValuedPoint.spectrumHomeomorph_map,
        Homeomorph.apply_symm_apply] using he)

/-- The ACTUAL affine scheme pullback with prescribed H(x) norm is the WHOLE original native fibre. -/
def affineFibreHomeomorph (x : Spectrum A) :
    RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H x))
      (affineStructureMap (B := B) x) ≃ₜ
      {y : SchemeValuedPoint (Spec (CommRingCat.of B)) //
        SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (algebraMap A B))) y =
          SchemeValuedPoint.spectrumHomeomorph.symm x} :=
  (affineTensorRelativeHomeomorph (B := B) x).trans
    ((Spectrum.fibreHomeomorph (B := B) x).trans (affineOriginalFibreHomeomorph (B := B) x))

/-- The entire forward point is EXACTLY the ORIGINAL scheme projection, on every residue value. -/
theorem affineFibreHomeomorph_apply (x : Spectrum A)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H x))
      (affineStructureMap (B := B) x)) :
    (affineFibreHomeomorph (B := B) x y).1 =
      SchemeValuedPoint.map (affineProjection (B := B) x) y.1 := by
  apply SchemeValuedPoint.spectrumHomeomorph.injective
  simp only [affineFibreHomeomorph, Homeomorph.trans_apply]
  change SchemeValuedPoint.spectrumHomeomorph
    (SchemeValuedPoint.spectrumHomeomorph.symm
      ((Spectrum.fibreHomeomorph (B := B) x) ((affineTensorRelativeHomeomorph (B := B) x) y)).1) = _
  rw [Homeomorph.apply_symm_apply, Spectrum.fibreHomeomorph_apply]
  change Spectrum.comap
      (Algebra.TensorProduct.includeRight (R := A) (A := Spectrum.H x) (B := B)).toRingHom
      (SchemeValuedPoint.spectrumHomeomorph
        (SchemeValuedPoint.map (affineTensorIso (B := B) x).hom y.1)) = _
  rw [← SchemeValuedPoint.spectrumHomeomorph_map, ← SchemeValuedPoint.map_comp,
    affineTensorIso_hom_projection]

/-- The genuine inverse recovers EVERY original native point through the SAME actual projection. -/
theorem affineProjection_map_affineFibreHomeomorph_symm (x : Spectrum A)
    (y : {y : SchemeValuedPoint (Spec (CommRingCat.of B)) //
      SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (algebraMap A B))) y =
        SchemeValuedPoint.spectrumHomeomorph.symm x}) :
    SchemeValuedPoint.map (affineProjection (B := B) x)
      ((affineFibreHomeomorph (B := B) x).symm y).1 = y.1 := by
  rw [← affineFibreHomeomorph_apply]
  exact congrArg Subtype.val ((affineFibreHomeomorph (B := B) x).apply_symm_apply y)

end EnvelopeProperty.Berkovich.SchemeCompletedFibre
