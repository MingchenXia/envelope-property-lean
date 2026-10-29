/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeIdealStalk
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import EnvelopeProperty.AlgGeom.IdealSheafAffinePullback

/-!
# Actual geometric ideal pullback on affine sections and stalks

Mathlib's genuine closed-subscheme ideal pullback has its affine ideal
image formula derived from the true geometric adjunction. Actual open
restriction, global-section isomorphisms and affine refinement then prove
the whole stalk-image identity for arbitrary schemes and morphisms.
No finite generation, Noetherianity, separatedness or properness is assumed.
-/


open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

/-- Genuine open restriction transports the actual global ideal back to its original affine section ring. -/
theorem comap_open_ideal_top_map (I : X.IdealSheafData) {U : X.Opens} (hU : IsAffineOpen U) :
    (letI : IsAffine U.toScheme := hU;
      ((I.comap U.ι).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩).map U.topIso.hom.hom) =
      I.ideal ⟨U, hU⟩ := by
  let : IsAffine U.toScheme := hU
  rw [ideal_comap_of_isOpenImmersion]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  change (I.ideal ⟨U.ι ''ᵁ ⊤, (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩).map
    U.topIso.hom.hom = I.ideal ⟨U, hU⟩
  have hh : U.topIso.hom = X.presheaf.map
      (homOfLE (show U ≤ U.ι ''ᵁ ⊤ from U.ι_image_top.symm.le)).op := by
    simp only [Scheme.Opens.topIso_hom, eqToHom_op]
    congr 1
  rw [hh]
  exact I.map_ideal (U := ⟨U, hU⟩)
    (V := ⟨U.ι ''ᵁ ⊤, (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩)
    (show U ≤ U.ι ''ᵁ ⊤ from U.ι_image_top.symm.le)

/-- Actual affine chart ideals of the geometric pullback are genuine section-ring images for every scheme morphism. -/
theorem comap_ideal_of_affine_opens (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (h : U.1 ≤ f ⁻¹ᵁ V.1) :
    (I.comap f).ideal U = (I.ideal V).map (f.appLE V U h).hom := by
  have he : (I.comap f).comap U.1.ι =
      (I.comap V.1.ι).comap (f.resLE V U h) := by
    rw [← comap_comp, ← comap_comp, Scheme.Hom.resLE_comp_ι]
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine V.1.toScheme := V.2
  have hp := comap_ideal_top_of_isAffine_native (I.comap V.1.ι) (f.resLE V U h)
  rw [← he] at hp
  have hm := congrArg (Ideal.map U.1.topIso.hom.hom) hp
  rw [comap_open_ideal_top_map (I.comap f) U.2, Ideal.map_map] at hm
  have hmaps : U.1.topIso.hom.hom.comp (f.resLE V U h).appTop.hom =
      (f.appLE V U h).hom.comp V.1.topIso.hom.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appTop,
      Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hmaps, ← Ideal.map_map, comap_open_ideal_top_map I V.2] at hm
  exact hm

/-- The actual geometric pullback's intrinsic stalk ideal is the genuine stalk-map image, for arbitrary schemes. -/
theorem paperStalkIdeal_comap (I : Y.IdealSheafData) (f : X ⟶ Y) (x : X) :
    (I.comap f).stalkIdeal x = (I.stalkIdeal (f x)).map (f.stalkMap x).hom := by
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (U := ⊤) (x := f x) trivial
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := f ⁻¹ᵁ V) (x := x) hxV
  let U' : X.affineOpens := ⟨U, hU⟩
  let V' : Y.affineOpens := ⟨V, hV⟩
  rw [stalkIdeal_eq_affine _ x U' hxU, comap_ideal_of_affine_opens I f U' V' hUV,
    Ideal.map_map, stalkIdeal_eq_affine I (f x) V' hxV, Ideal.map_map,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  have hg : f.appLE V U hUV ≫ X.presheaf.germ U x hxU =
      Y.presheaf.germ V (f x) hxV ≫ f.stalkMap x := by
    rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res (homOfLE hUV) x hxU]
    exact (Scheme.Hom.germ_stalkMap f V x hxV).symm
  rw [hg]
end AlgebraicGeometry.Scheme.IdealSheafData
