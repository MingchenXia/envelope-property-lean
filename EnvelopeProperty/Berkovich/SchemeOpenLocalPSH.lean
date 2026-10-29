/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLocalPSH
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas

/-!
# Actual open-immersion descent and genuine scheme-cover locality

Real inverse section isomorphisms push genuine regular units. Actual whole
native open embeddings push neighborhoods, and their genuine inverse values
extend the actual sequence without any continuity claim outside that image.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Classical
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}

/-- The inverse ORIGINAL section isomorphism of a genuine open immersion preserves every unit logarithm. -/
theorem unitTropAffine_map_appIso_inv (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = fX)
    {V : X.Opens} {n : ℕ} (a : Fin n → Γ(X, V)ˣ) (p : (Fin n → ℚ) × ℚ)
    (y : RelativeSchemeValuedPoint v fX) (hy : y.1.point ∈ V) :
    unitTropAffine (fun i => Units.map (g.appIso V).inv.hom.toMonoidHom (a i)) p
      (map g hg y) (Set.mem_image_of_mem g hy) = unitTropAffine a p y hy := by
  unfold unitTropAffine
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  exact congrArg (fun z : ℝ≥0 => (z : ℝ))
    (SchemeValuedPoint.eval_map_appIso_inv g y.1 V hy (a i : Γ(X, V)))

/-- Actual open native images and genuine inverse section maps descend the intrinsic whole-unit class. -/
theorem IsConvexPLOn.of_comp_openImmersion (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = fX)
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hU : U ⊆ Set.range (map g hg))
    (hu : IsConvexPLOn (map g hg ⁻¹' U) (fun y => u (map g hg y))) : IsConvexPLOn U u := by
  intro x hx
  obtain ⟨y, rfl⟩ := hU hx
  obtain ⟨W, hW, hyW, hWU, V, hWV, n, a, s, hs, hform⟩ := hu y hx
  have hmap := isOpenEmbedding_map_of_isOpenImmersion (v := v) g hg
  have hWV' : ∀ z ∈ map g hg '' W, z.1.point ∈ g ''ᵁ V := by
    rintro z ⟨z', hz', rfl⟩
    exact Set.mem_image_of_mem g (hWV z' hz')
  refine ⟨map g hg '' W, hmap.isOpenMap W hW, ⟨y, hyW, rfl⟩,
    (by rintro z ⟨z', hz', rfl⟩; exact hWU hz'), g ''ᵁ V, hWV', n,
    (fun i => Units.map (g.appIso V).inv.hom.toMonoidHom (a i)), s, hs, ?_⟩
  rintro z ⟨z', hz', rfl⟩
  calc
    _ = ((s.sup' hs fun p => unitTropAffine a p z' (hWV z' hz') : ℝ) : EReal) := hform z' hz'
    _ = _ := by
      congr 1
      apply Finset.sup'_congr hs rfl
      intro p hp
      exact (unitTropAffine_map_appIso_inv g hg a p z' (hWV z' hz')).symm

private def extendOpenFunction (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (u : RelativeSchemeValuedPoint v fX → EReal) (x : RelativeSchemeValuedPoint v fY) : EReal :=
  if hx : x ∈ Set.range (map g hg) then u (Classical.choose hx) else 0

private theorem extendOpenFunction_map (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = fX)
    (u : RelativeSchemeValuedPoint v fX → EReal) (x : RelativeSchemeValuedPoint v fX) :
    extendOpenFunction g hg u (map g hg x) = u x := by
  unfold extendOpenFunction
  rw [dif_pos (show map g hg x ∈ Set.range (map g hg) from ⟨x, rfl⟩)]
  apply congrArg u
  exact (isOpenEmbedding_map_of_isOpenImmersion (v := v) g hg).injective
    (Classical.choose_spec (show map g hg x ∈ Set.range (map g hg) from ⟨x, rfl⟩))

/-- True whole native inverse values extend the genuine source sequence, preserving all inequalities and infima. -/
theorem IsDecrConvexPLLimitOn.of_comp_openImmersion (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = fX)
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hU : U ⊆ Set.range (map g hg))
    (hu : IsDecrConvexPLLimitOn (map g hg ⁻¹' U) (fun y => u (map g hg y))) :
    IsDecrConvexPLLimitOn U u := by
  obtain ⟨a, ha, hanti, hlim⟩ := hu
  refine ⟨fun j => extendOpenFunction g hg (a j), ?_, ?_, ?_⟩
  · intro j
    apply IsConvexPLOn.of_comp_openImmersion g hg hU
    simpa only [extendOpenFunction_map] using ha j
  · intro y hy
    obtain ⟨z, rfl⟩ := hU hy
    simpa only [extendOpenFunction_map] using hanti z hy
  · intro y hy
    obtain ⟨z, rfl⟩ := hU hy
    simpa only [extendOpenFunction_map] using hlim z hy

/-- Real open-immersion native images and inverse section maps descend the intrinsic local presentation class. -/
theorem IsLocallyPSHOn.of_comp_openImmersion (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = fX)
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hU : U ⊆ Set.range (map g hg))
    (hu : IsLocallyPSHOn (map g hg ⁻¹' U) (fun y => u (map g hg y))) : IsLocallyPSHOn U u := by
  intro x hx
  obtain ⟨y, rfl⟩ := hU hx
  obtain ⟨W, hW, hyW, hWU, hloc⟩ := hu y hx
  have hmap := isOpenEmbedding_map_of_isOpenImmersion (v := v) g hg
  refine ⟨map g hg '' W, hmap.isOpenMap W hW, ⟨y, hyW, rfl⟩,
    (by rintro z ⟨z', hz', rfl⟩; exact hWU hz'), ?_⟩
  apply IsDecrConvexPLLimitOn.of_comp_openImmersion g hg (Set.image_subset_range _ _)
  simpa only [Set.preimage_image_eq _ hmap.injective] using hloc

/-- A genuine original scheme open cover glues the intrinsic local presentation class on WHOLE prescribed native points. -/
theorem IsLocallyPSHOn.of_openCover (𝒰 : Y.OpenCover)
    (f : ∀ i, 𝒰.X i ⟶ Spec (CommRingCat.of R)) (hf : ∀ i, 𝒰.f i ≫ fY = f i)
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hu : ∀ i, IsLocallyPSHOn
      (map (v := v) (𝒰.f i) (hf i) ⁻¹' U)
      (fun y => u (map (𝒰.f i) (hf i) y))) : IsLocallyPSHOn U u := by
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
  apply IsDecrConvexPLLimitOn.of_comp_openImmersion (𝒰.f i) (hf i) (Set.image_subset_range _ _)
  simpa only [Set.preimage_image_eq _ hmap.injective] using hloc

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
