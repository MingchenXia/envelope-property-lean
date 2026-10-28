import EnvelopeProperty.Berkovich.SchemeNetPSH
import EnvelopeProperty.Berkovich.SchemeOpenLocalPSH

/-! # Actual open descent and whole native cover locality for directed PL nets -/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Classical
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}

private def extendOpenNetFunction (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (u : RelativeSchemeValuedPoint v fX → EReal) (x : RelativeSchemeValuedPoint v fY) : EReal :=
  if hx : x ∈ Set.range (map g hg) then u (Classical.choose hx) else 0

private theorem extendOpenNetFunction_map (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = fX)
    (u : RelativeSchemeValuedPoint v fX → EReal) (x : RelativeSchemeValuedPoint v fX) :
    extendOpenNetFunction g hg u (map g hg x) = u x := by
  unfold extendOpenNetFunction
  rw [dif_pos (show map g hg x ∈ Set.range (map g hg) from ⟨x, rfl⟩)]
  apply congrArg u
  exact (isOpenEmbedding_map_of_isOpenImmersion (v := v) g hg).injective
    (Classical.choose_spec (show map g hg x ∈ Set.range (map g hg) from ⟨x, rfl⟩))

/-- True whole native inverse values extend the genuine source directed net, preserving all inequalities and infima. -/
theorem IsDecrConvexPLNetLimitOn.of_comp_openImmersion (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = fX)
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hU : U ⊆ Set.range (map g hg))
    (hu : IsDecrConvexPLNetLimitOn (map g hg ⁻¹' U) (fun y => u (map g hg y))) :
    IsDecrConvexPLNetLimitOn U u := by
  obtain ⟨J, _, _, _, a, ha, hanti, hlim⟩ := hu
  refine ⟨J, inferInstance, inferInstance, inferInstance, fun j => extendOpenNetFunction g hg (a j), ?_, ?_, ?_⟩
  · intro j
    apply IsConvexPLOn.of_comp_openImmersion g hg hU
    simpa only [extendOpenNetFunction_map] using ha j
  · intro y hy
    obtain ⟨z, rfl⟩ := hU hy
    simpa only [extendOpenNetFunction_map] using hanti z hy
  · intro y hy
    obtain ⟨z, rfl⟩ := hU hy
    simpa only [extendOpenNetFunction_map] using hlim z hy

/-- Real open-immersion native images and inverse section maps descend the intrinsic local presentation class. -/
theorem IsLocallyNetPSHOn.of_comp_openImmersion (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = fX)
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hU : U ⊆ Set.range (map g hg))
    (hu : IsLocallyNetPSHOn (map g hg ⁻¹' U) (fun y => u (map g hg y))) : IsLocallyNetPSHOn U u := by
  intro x hx
  obtain ⟨y, rfl⟩ := hU hx
  obtain ⟨W, hW, hyW, hWU, hloc⟩ := hu y hx
  have hmap := isOpenEmbedding_map_of_isOpenImmersion (v := v) g hg
  refine ⟨map g hg '' W, hmap.isOpenMap W hW, ⟨y, hyW, rfl⟩,
    (by rintro z ⟨z', hz', rfl⟩; exact hWU hz'), ?_⟩
  apply IsDecrConvexPLNetLimitOn.of_comp_openImmersion g hg (Set.image_subset_range _ _)
  simpa only [Set.preimage_image_eq _ hmap.injective] using hloc

/-- A genuine original scheme open cover glues the intrinsic local presentation class on WHOLE prescribed native points. -/
theorem IsLocallyNetPSHOn.of_openCover (𝒰 : Y.OpenCover)
    (f : ∀ i, 𝒰.X i ⟶ Spec (CommRingCat.of R)) (hf : ∀ i, 𝒰.f i ≫ fY = f i)
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hu : ∀ i, IsLocallyNetPSHOn
      (map (v := v) (𝒰.f i) (hf i) ⁻¹' U)
      (fun y => u (map (𝒰.f i) (hf i) y))) : IsLocallyNetPSHOn U u := by
  intro x hx
  let i := 𝒰.idx x.1.point
  let M := map (v := v) (𝒰.f i) (hf i)
  have hxrange : x ∈ Set.range M := by
    rw [show Set.range M = {y : RelativeSchemeValuedPoint v fY |
      y.1.point ∈ (𝒰.f i).opensRange} from range_map_of_isOpenImmersion (𝒰.f i) (hf i)]
    exact 𝒰.covers x.1.point
  obtain ⟨y, hy⟩ := hxrange
  have hyU : M y ∈ U := hy.symm ▸ hx
  obtain ⟨W, hW, hyW, hWU, hloc⟩ := hu i y hyU
  have hmap := isOpenEmbedding_map_of_isOpenImmersion (v := v) (𝒰.f i) (hf i)
  refine ⟨M '' W, hmap.isOpenMap W hW, ⟨y, hyW, hy⟩,
    (by rintro z ⟨z', hz', rfl⟩; exact hWU hz'), ?_⟩
  apply IsDecrConvexPLNetLimitOn.of_comp_openImmersion (𝒰.f i) (hf i) (Set.image_subset_range _ _)
  simpa only [Set.preimage_image_eq _ hmap.injective] using hloc

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
