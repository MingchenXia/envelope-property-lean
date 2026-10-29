/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ProperMapLocality
import EnvelopeProperty.Berkovich.SchemeClosedImmersion
import EnvelopeProperty.Berkovich.SpectrumIntegralProper
import Mathlib.AlgebraicGeometry.Morphisms.Integral


/-!
# Proper native point maps of actual integral scheme morphisms

Genuine integral affine section maps, entire native affine chart squares and
true proper-map locality prove global properness of actual integral native
maps. Closedness and compact preimages and fibres follow. Restricting the
whole basepoint preimage yields the same conclusions for every prescribed
base seminorm. No coefficient bound, proper structure morphism, separated
total scheme, finite-type or Noetherian assumption is required.
The conclusion is topological properness, not algebraic properness of an
integral morphism without finite type.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite
universe u
noncomputable section
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

/-- On every actual affine support open, an integral morphism induces a proper native point map. -/
theorem isProperMap_map_restrict_affine_of_isIntegralHom (U : Y.Opens) (hU : IsAffineOpen U) :
    IsProperMap ((supportOpens U : Set (SchemeValuedPoint Y)).restrictPreimage (map f)) := by
  have hc := (affineOpenSpectrumHomeomorph hU).symm.isClosedEmbedding.isProperMap.comp
    ((Spectrum.isProperMap_comap_of_isIntegral (f.app U).hom (f.isIntegral_app U hU)).comp
      (affineOpenSpectrumHomeomorph (hU.preimage f)).isClosedEmbedding.isProperMap)
  have he : (affineOpenSpectrumHomeomorph hU).symm ∘ Spectrum.comap (f.app U).hom ∘
      affineOpenSpectrumHomeomorph (hU.preimage f) =
        (supportOpens U : Set (SchemeValuedPoint Y)).restrictPreimage (map f) := by
    funext x
    apply (affineOpenSpectrumHomeomorph hU).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact (affineOpenSpectrumHomeomorph_map f U hU x).symm
  exact he ▸ hc

/-- Integral scheme morphisms genuinely induce proper native maps, without bounded-base or separation assumptions. -/
theorem isProperMap_map_of_isIntegralHom : IsProperMap (map f) := by
  let U : AffineAtlasIndex Y → TopologicalSpace.Opens (SchemeValuedPoint Y) :=
    fun i => supportOpens (canonicalAffineOpens Y i)
  have hU : TopologicalSpace.IsOpenCover U := TopologicalSpace.IsOpenCover.mk (by
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    change (⋃ i, (supportOpens (canonicalAffineOpens Y i) : Set (SchemeValuedPoint Y))) = Set.univ
    exact iUnion_supportOpens (canonicalAffineOpens Y) (iUnion_canonicalAffineOpens Y))
  exact (EnvelopeProperty.isProperMap_iff_restrictPreimage_of_openCover hU (continuous_map f)).mpr
    (fun i => isProperMap_map_restrict_affine_of_isIntegralHom f _ (isAffineOpen_canonicalAffineOpens Y i))

/-- These actual integral native maps are closed. -/
theorem isClosedMap_map_of_isIntegralHom : IsClosedMap (map f) :=
  (isProperMap_map_of_isIntegralHom f).isClosedMap

/-- Compact native target subsets have compact inverse images under integral morphisms. -/
theorem isCompact_preimage_map_of_isIntegralHom {K : Set (SchemeValuedPoint Y)} (hK : IsCompact K) :
    IsCompact (map f ⁻¹' K) := (isProperMap_map_of_isIntegralHom f).isCompact_preimage hK

/-- Every native fibre of an actual integral morphism is compact. -/
theorem isCompact_fibre_map_of_isIntegralHom (y : SchemeValuedPoint Y) :
    IsCompact (map f ⁻¹' {y}) := isCompact_preimage_map_of_isIntegralHom f isCompact_singleton

end EnvelopeProperty.Berkovich.SchemeValuedPoint
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}
variable (g : X ⟶ Y) (hg : g ≫ fY = fX) [IsIntegralHom g]

/-- The true fixed-base map of any integral scheme morphism is proper for every prescribed seminorm. -/
theorem isProperMap_map_of_isIntegralHom : IsProperMap (map (v := v) g hg) := by
  let e := Homeomorph.setCongr (relativeLocus_preimage_eq (v := v) g hg)
  have hc := ((SchemeValuedPoint.isProperMap_map_of_isIntegralHom g).restrictPreimage
    (SchemeValuedPoint.relativeLocus v fY)).comp e.isClosedEmbedding.isProperMap
  have he : (SchemeValuedPoint.relativeLocus v fY).restrictPreimage (SchemeValuedPoint.map g) ∘ e =
      map g hg := by
    funext x
    apply Subtype.ext
    rfl
  exact he ▸ hc

/-- Integral prescribed-base native maps are closed without coefficient bounds. -/
theorem isClosedMap_map_of_isIntegralHom : IsClosedMap (map (v := v) g hg) :=
  (isProperMap_map_of_isIntegralHom g hg).isClosedMap

/-- Actual relative integral native maps preserve compact inverse images. -/
theorem isCompact_preimage_map_of_isIntegralHom {K : Set (RelativeSchemeValuedPoint v fY)}
    (hK : IsCompact K) : IsCompact (map g hg ⁻¹' K) :=
  (isProperMap_map_of_isIntegralHom g hg).isCompact_preimage hK

/-- Their genuine fixed-base point fibres are compact for every prescribed base seminorm. -/
theorem isCompact_fibre_map_of_isIntegralHom (y : RelativeSchemeValuedPoint v fY) :
    IsCompact (map g hg ⁻¹' {y}) := isCompact_preimage_map_of_isIntegralHom g hg isCompact_singleton

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
