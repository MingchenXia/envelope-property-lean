/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeIdealExtension
import EnvelopeProperty.Berkovich.SchemeCenterAffine
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Actual flat scheme-image closures from field coefficient schemes

Whole geometric scheme-image kernels and actual section coefficient identities
inject every original image section ring into true field-scheme sections.
Torsion-freeness and the genuine Bezout flatness criterion derive flatness of
the whole image structure. No reducedness, Noetherianity, flatness or model
certificate is supplied.
-/

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Hom
variable {X Y : Scheme.{u}}
/-- The actual whole canonical map to the scheme-image kernel has zero genuine scheme-image ideal. -/
theorem isSchemeTheoreticallyDominant_toImage (g : X ⟶ Y) :
    IsSchemeTheoreticallyDominant g.toImage := by
  constructor
  have h : g.toImage.ker.map g.imageι = (⊥ : g.image.IdealSheafData).map g.imageι := by
    rw [Scheme.IdealSheafData.map_ker, g.toImage_imageι,
      Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]
  have h' := congrArg (fun I => I.comap g.imageι) h
  simpa only [Scheme.IdealSheafData.comap_map_of_isClosedImmersion] using h'
end AlgebraicGeometry.Scheme.Hom

namespace EnvelopeProperty.SchemeImage
section Naturality
variable {R K : Type u} [CommRing R] [CommRing K] {X Y : Scheme.{u}}

/-- True whole section coefficient restriction is natural along an actual commuting cross-base scheme map. -/
theorem sectionBaseMap_comp_app (φ : R →+* K)
    (fX : X ⟶ Spec (CommRingCat.of K)) (fY : Y ⟶ Spec (CommRingCat.of R))
    (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ)) (U : Y.Opens) :
    (g.app U).hom.comp (SchemeValuedPoint.sectionBaseMap fY U) =
      (SchemeValuedPoint.sectionBaseMap fX (g ⁻¹ᵁ U)).comp φ := by
  have hn : Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ g.app U =
      g.appTop ≫ X.presheaf.map (homOfLE (show g ⁻¹ᵁ U ≤ ⊤ from le_top)).op := by
    exact g.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
  have hc : fY.appTop ≫ g.appTop =
      (Spec.map (CommRingCat.ofHom φ)).appTop ≫ fX.appTop := by
    rw [← Scheme.Hom.comp_appTop, hg, Scheme.Hom.comp_appTop]
  have he : CommRingCat.ofHom (SchemeValuedPoint.sectionBaseMap fY U) ≫ g.app U =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (SchemeValuedPoint.sectionBaseMap fX (g ⁻¹ᵁ U)) := by
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ fY.appTop ≫
      Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) ≫ g.app U =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ fX.appTop ≫
        X.presheaf.map (homOfLE (show g ⁻¹ᵁ U ≤ ⊤ from le_top)).op
    simp only [Category.assoc]
    rw [hn, ← Category.assoc fY.appTop, hc]
    rw [Category.assoc, ← Category.assoc (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
    rw [← Scheme.ΓSpecIso_inv_naturality]
    simp only [Category.assoc]
  exact congrArg CommRingCat.Hom.hom he

end Naturality

section Flat
variable {R K : Type u} [CommRing R] [IsDomain R] [IsBezout R] [Field K]
  {X Y : Scheme.{u}}

/-- Every whole section coefficient module of the actual field-origin image is flat over the genuine Bezout domain. -/
theorem sectionBaseMap_image_flat (φ : R →+* K) (hφ : Function.Injective φ)
    (fX : X ⟶ Spec (CommRingCat.of K)) (fY : Y ⟶ Spec (CommRingCat.of R))
    (g : X ⟶ Y) [QuasiCompact g]
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ)) (U : g.image.Opens) :
    (SchemeValuedPoint.sectionBaseMap (g.imageι ≫ fY) U).Flat := by
  let : IsSchemeTheoreticallyDominant g.toImage := g.isSchemeTheoreticallyDominant_toImage
  let M := Γ(g.image, U)
  let N := Γ(X, g.toImage ⁻¹ᵁ U)
  let : Algebra R M := SchemeValuedPoint.sectionBaseAlgebra (g.imageι ≫ fY) U
  let : Algebra K N := SchemeValuedPoint.sectionBaseAlgebra fX (g.toImage ⁻¹ᵁ U)
  let : Algebra R N := Algebra.compHom N φ
  have hgi : g.toImage ≫ (g.imageι ≫ fY) = fX ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Category.assoc, g.toImage_imageι, hg]
  let a : M →ₐ[R] N :=
    { __ := (g.toImage.app U).hom
      commutes' := fun r => RingHom.congr_fun (sectionBaseMap_comp_app φ fX
        (g.imageι ≫ fY) g.toImage hgi U) r }
  let : Module.IsTorsionFree R N := Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      change φ r • m = 0 at hrm
      exact (smul_eq_zero.mp hrm).resolve_left (fun h => hr (hφ (h.trans (map_zero φ).symm)))
  let : Module.IsTorsionFree R M := Function.Injective.moduleIsTorsionFree a
    (g.toImage.app_injective U) (fun r m => a.toLinearMap.map_smul r m)
  change Module.Flat R M
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- The whole ACTUAL scheme-image coefficient structure from a field scheme is flat over the specified Bezout domain. -/
theorem image_structureMap_flat (φ : R →+* K) (hφ : Function.Injective φ)
    (fX : X ⟶ Spec (CommRingCat.of K)) (fY : Y ⟶ Spec (CommRingCat.of R))
    (g : X ⟶ Y) [QuasiCompact g]
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ)) :
    AlgebraicGeometry.Flat (g.imageι ≫ fY) := by
  let 𝒰 := g.image.openCoverOfIsOpenCover (fun U : g.image.affineOpens => U.1)
    (iSup_affineOpens_eq_top g.image)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat) 𝒰).mpr
  intro U
  change AlgebraicGeometry.Flat (U.1.ι ≫ (g.imageι ≫ fY))
  apply (MorphismProperty.cancel_left_of_respectsIso @AlgebraicGeometry.Flat U.2.isoSpec.inv _).mp
  change AlgebraicGeometry.Flat (U.2.fromSpec ≫ (g.imageι ≫ fY))
  rw [SchemeValuedPoint.fromSpec_structureMap]
  exact AlgebraicGeometry.Flat.SpecMap_iff.mpr (sectionBaseMap_image_flat φ hφ fX fY g hg U.1)

end Flat

end EnvelopeProperty.SchemeImage
